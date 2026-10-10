// This file is part of Crag.
//
// Copyright (C) 2026 Ralf Claussnitzer
//
// Crag is free software: you can redistribute it and/or modify it under the
// terms of the GNU General Public License as published by the Free Software
// Foundation, either version 3 of the License, or (at your option) any later
// version.
//
// Crag is distributed in the hope that it will be useful, but WITHOUT ANY
// WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
// A PARTICULAR PURPOSE. See the GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License along with
// Crag. If not, see <https://www.gnu.org/licenses/>.

//! Compile-time evaluation (Implementation Plan §11.6.7, Specification
//! §18.4): pure code run in the compiler.
//!
//! A module-level value whose body has no effects is a constant. The
//! compiler compiles what it reaches in the metered tier, loads it into
//! its own process and runs it on a fiber under a meter, which is safe
//! because pure code does no I/O and the meter bounds its steps and its
//! memory. The result is encoded as canonical bytes and hashed, and the
//! query keeps it.
//!
//! An evaluation that traps, or runs out of steps or memory, is a compile
//! error at the value. One that reaches what the compiler cannot compile
//! yet, or code with errors, or gives what has no encoding, such as a
//! function value, is no error: the value is not a constant and is computed
//! when the program runs, as before.
//!
//! At each refill of the fuel the evaluation asks whether an edit cancelled
//! the query, and stops if so. The query then unwinds as cancelled queries
//! do, from Rust, after the fiber has stopped.
//!
//! Not built yet: conditions with known inputs and type functions, which
//! wait for conditions and `Type` values in the checker, and `embed`
//! (§11.6.10).

extern crate crag_db as salsa;

use std::collections::HashMap;
use std::sync::{Arc, OnceLock};

use crag_abi::{CELL_FULL, CELL_VALUE_OFFSET, FuncId, RuntimeFn, SlotKey, TrapKind};
use crag_backend::{code, func_id, shapes};
use crag_codegen::{CodegenSettings, OptLevel, Target, compile_entry_stub, target_for};
use crag_db::{Db, catch_cancelled, check_cancelled};
use crag_hir::{ItemId, ItemKind, ModuleId, Owner, Program};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_mir::{Entry, InstanceKey, Tier, collect_instances, mir};
use crag_runtime::{
    CodeMap, Fiber, FiberConfig, FiberState, Meter, Types, Worker, encode_value, release_value,
};
use crag_types::Ty;

/// The steps an evaluation may take: function entries and loop turns.
pub const STEP_LIMIT: u64 = 100_000_000;

/// The bytes of heap and stack an evaluation may take.
pub const MEMORY_LIMIT: usize = 256 << 20;

/// The meter of an evaluation.
pub const LIMITS: Meter = Meter {
    steps: STEP_LIMIT,
    memory: MEMORY_LIMIT,
};

/// Where evaluation was asked for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum EvalSite<'db> {
    /// A module-level value.
    Value(ItemId<'db>),
}

/// A value computed at compile time, in the Solid codec's bytes, with
/// their hash.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct ConstValue {
    pub bytes: Vec<u8>,
    pub hash: [u8; 32],
}

/// Why a site has no compile-time value.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum EvalError {
    /// The evaluation trapped, or ran out of steps or memory: a compile
    /// error.
    Trap {
        kind: TrapKind,
        /// The module and the byte offset of the expression that trapped,
        /// if known.
        position: Option<(ModuleId, u32)>,
        /// The functions of the frames, the trapping one first.
        stack: Vec<String>,
    },
    /// The site is not a constant, for this reason; it is computed when
    /// the program runs.
    NotConstant(String),
}

/// The value of a site, computed at compile time.
#[crag_db::tracked(returns(ref))]
pub fn const_eval<'db>(
    db: &'db dyn Db,
    program: Program,
    site: EvalSite<'db>,
) -> Result<ConstValue, EvalError> {
    evaluate(db, program, site, LIMITS).0
}

/// Every module-level value of a module that is a constant but whose
/// evaluation failed: the compile errors of compile-time evaluation.
pub fn eval_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(ItemId<'db>, EvalError)> {
    let mut out = Vec::new();
    for item in &crag_hir::item_tree(db, module).items {
        if *item.id.kind(db) != ItemKind::Value {
            continue;
        }
        if let Err(e @ EvalError::Trap { .. }) = const_eval(db, program, EvalSite::Value(item.id)) {
            out.push((item.id, e.clone()));
        }
    }
    out
}

/// The evaluation behind `const_eval`, under the meter, and the boxes left
/// on the heap after it, which is none unless something leaks. For tests.
#[doc(hidden)]
pub fn evaluate<'db>(
    db: &'db dyn Db,
    program: Program,
    site: EvalSite<'db>,
    meter: Meter,
) -> (Result<ConstValue, EvalError>, usize) {
    let not = |why: &str| (Err(EvalError::NotConstant(why.into())), 0);
    let EvalSite::Value(item) = site;
    let owner = Owner::Item(item);
    let types = crag_types::body_types(db, program, owner);
    if !types.errors.is_empty() {
        return not("it has errors");
    }
    if types.effects.has_effects() {
        return not("it has effects");
    }
    let root = InstanceKey::body(db, owner);
    let Some(ty) = mir(db, program, root, Tier::Baseline)
        .as_ref()
        .map(|b| b.result)
    else {
        return not("it has no body");
    };
    match Evaluation::build(db, program, root) {
        Ok(mut evaluation) => {
            let result = evaluation.run(db, program, ty, meter);
            let left = evaluation.finish(db, program);
            (result, left)
        }
        Err(why) => not(&why),
    }
}

/// The host's target.
fn host() -> &'static Target {
    static HOST: OnceLock<Target> = OnceLock::new();
    HOST.get_or_init(|| target_for("x86_64-unknown-linux-gnu").expect("the host is supported"))
}

/// The metered code of what a value reaches, loaded, with a worker to run
/// it.
struct Evaluation<'db> {
    arena: CodeArena,
    symbols: SymbolTable,
    worker: Worker,
    root: InstanceKey<'db>,
    /// Each function's entry, name and module.
    functions: HashMap<FuncId, (usize, String, ModuleId)>,
    /// The values among the instances: their cells' keys and types.
    cells: Vec<(SlotKey, Ty<'db>)>,
}

impl<'db> Evaluation<'db> {
    fn build(
        db: &'db dyn Db,
        program: Program,
        root: InstanceKey<'db>,
    ) -> Result<Evaluation<'db>, String> {
        let mut objects = Vec::new();
        let mut types = Vec::new();
        let mut names = Vec::new();
        let mut cells = Vec::new();
        for instance in collect_instances(db, program, &[root], Tier::Metered) {
            let compiled = match code(db, program, instance, Tier::Metered) {
                Some(Ok(compiled)) => compiled,
                Some(Err(e)) => return Err(format!("its code does not compile: {e}")),
                None => return Err("it reaches what has no body".into()),
            };
            let owner = *instance.owner(db);
            let name = match owner {
                Owner::Item(item) => item.name(db).text(db).clone(),
                Owner::Test(test) => format!("test {}", test.label(db)),
            };
            let name = match instance.entry(db) {
                Entry::Body => name,
                Entry::Closure(_) => format!("a closure in {name}"),
                Entry::Function(_) => format!("a function value in {name}"),
            };
            let value = matches!(owner, Owner::Item(i) if *i.kind(db) == ItemKind::Value);
            if value && *instance.entry(db) == Entry::Body {
                let body = mir(db, program, instance, Tier::Baseline);
                cells.extend(body.as_ref().map(|b| (compiled.slot, b.result)));
            }
            names.push((compiled.func, name, owner.module(db)));
            types.extend(compiled.types.iter().cloned());
            objects.push((compiled.slot, &compiled.object));
        }
        let io = |e: std::io::Error| format!("no memory for its code: {e}");
        let mut arena = CodeArena::new(16 << 20).map_err(io)?;
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            symbols.define_runtime(func, crag_runtime::runtime_fn_addr(func));
        }
        let entries = load_group(&mut arena, &mut symbols, &objects)
            .map_err(|e| format!("its code does not load: {e:?}"))?;
        let mut map = CodeMap::new();
        let mut functions = HashMap::new();
        for ((&(slot, object), entry), (func, name, module)) in
            objects.iter().zip(&entries).zip(names)
        {
            map.add(slot.func, entry.addr(), object);
            functions.insert(func, (entry.addr(), name, module));
        }
        let mut worker = Worker::new();
        worker.set_types(Arc::new(Types::new(types)));
        worker.set_code_map(Arc::new(map));
        Ok(Evaluation {
            arena,
            symbols,
            worker,
            root,
            functions,
            cells,
        })
    }

    /// Runs the root under the meter and encodes its result, of type `ty`.
    fn run(
        &mut self,
        db: &'db dyn Db,
        program: Program,
        ty: Ty<'db>,
        meter: Meter,
    ) -> Result<ConstValue, EvalError> {
        let (shapes, shape) = shapes(db, program, ty);
        let returns = shapes.shapes[shape as usize].words();
        let settings = CodegenSettings {
            target: host().clone(),
            opt: OptLevel::None,
            metered: false,
        };
        let stub = compile_entry_stub(0, returns, &settings).expect("the stub compiles");
        let stub = load(&mut self.arena, &self.symbols, &stub).expect("the stub loads");
        let entry = self.functions[&func_id(self.root)].0;
        // SAFETY: the stub was compiled for the root's words, and both stay
        // loaded while the evaluation exists, which outlives the fiber.
        let mut fiber = unsafe { Fiber::new(stub.addr(), entry, &[], FiberConfig::default()) }
            .map_err(|e| EvalError::NotConstant(format!("no memory for a stack: {e}")))?;
        fiber.set_meter(meter);
        let poll = move || catch_cancelled(|| check_cancelled(db)).is_err();
        // SAFETY: the database outlives the fiber, which ends in this
        // function, and catching the cancellation keeps the poll from
        // unwinding.
        unsafe { fiber.set_poll(Box::new(poll)) };
        match self.worker.resume(&mut fiber) {
            FiberState::Finished => {}
            FiberState::Trapped => {
                let trap = fiber.trap().expect("trapped");
                return Err(match trap.kind {
                    // Unwinds, as a cancelled query does.
                    TrapKind::Cancelled => {
                        check_cancelled(db);
                        EvalError::NotConstant("it was cancelled".into())
                    }
                    TrapKind::Error => EvalError::NotConstant("it reaches code with errors".into()),
                    TrapKind::Unsupported => EvalError::NotConstant(
                        "it reaches code the compiler does not support yet".into(),
                    ),
                    kind => {
                        let func = |f: &FuncId| self.functions.get(f);
                        EvalError::Trap {
                            kind,
                            position: trap
                                .position
                                .zip(trap.stack.first().and_then(func))
                                .map(|(at, f)| (f.2, at)),
                            stack: trap
                                .stack
                                .iter()
                                .filter_map(func)
                                .map(|f| f.1.clone())
                                .collect(),
                        }
                    }
                });
            }
            state => unreachable!("a fiber nothing stops ended {state:?}"),
        }
        let words = fiber.results().expect("finished")[..returns as usize].to_vec();
        let types = self.worker.types();
        // SAFETY: the words are the root's result, of type `ty`, which the
        // fiber left to us; it is released once encoded.
        unsafe {
            let bytes = encode_value(&words, &shapes, shape, &types);
            release_value(self.worker.heap(), &types, &words, &shapes, shape);
            let bytes = bytes.map_err(|e| EvalError::NotConstant(format!("it holds {}", e.0)))?;
            let hash = *blake3::hash(&bytes).as_bytes();
            Ok(ConstValue { bytes, hash })
        }
    }

    /// Releases what the cells of the values hold and returns the boxes
    /// left on the heap.
    fn finish(mut self, db: &'db dyn Db, program: Program) -> usize {
        let types = self.worker.types();
        for &(key, ty) in &self.cells {
            let cells = self.symbols.cells();
            if cells.state(key) != Some(CELL_FULL) {
                continue;
            }
            let (shapes, shape) = shapes(db, program, ty);
            let n = shapes.shapes[shape as usize].words() as usize;
            let at = cells.address(key).expect("a full cell") + CELL_VALUE_OFFSET as usize;
            // SAFETY: a full cell holds a value of its type, with a
            // reference of its own, which nothing uses any more.
            unsafe {
                let words = std::slice::from_raw_parts(at as *const u64, n);
                release_value(self.worker.heap(), &types, words, &shapes, shape);
            }
        }
        self.worker.heap().live_blocks()
    }
}
