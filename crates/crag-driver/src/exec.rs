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

//! Compiling what a program reaches, loading it, and running it on fibers.

use std::collections::HashMap;
use std::sync::Arc;

use crag_abi::{FuncId, RuntimeFn, SlotKey, TrapKind, TypeDescriptor};
use crag_backend::{code, func_id};
use crag_codegen::{CodeObject, CodegenSettings, OptLevel, compile_entry_stub, target_for};
use crag_hir::{ItemKind, ModuleId, Owner};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_mir::{Entry, InstanceKey, Tier, collect_instances};
use crag_runtime::{CodeMap, Fiber, FiberConfig, FiberState, Trap, Types, Worker};

use crate::diagnostics::render_at;
use crate::project::Project;

/// Loaded code with a worker to run it.
pub struct Image {
    arena: CodeArena,
    symbols: SymbolTable,
    settings: CodegenSettings,
    functions: HashMap<FuncId, Function>,
    /// Each function's entry.
    entries: HashMap<FuncId, usize>,
    worker: Worker,
}

/// A compiled function as runs and reports need it.
#[derive(Clone, Debug)]
pub struct Function {
    /// Words of parameters and results.
    pub params: u32,
    pub returns: u32,
    /// The name reports give it, and where its code is written.
    pub name: String,
    pub module: ModuleId,
    /// The functions it calls.
    pub calls: Vec<FuncId>,
    /// The cell it keeps its value in, for the code of a module-level
    /// value.
    pub cell: Option<SlotKey>,
}

/// The code of what some roots reach.
pub struct Compiled<'a> {
    /// Each function's code and the slot it fills.
    pub objects: Vec<(SlotKey, &'a CodeObject)>,
    /// The descriptors of the types the code uses, by index.
    pub types: Vec<(u32, TypeDescriptor)>,
    pub functions: HashMap<FuncId, Function>,
}

/// Compiles the instances and everything they call.
pub fn compile<'a>(
    project: &'a Project,
    roots: &[InstanceKey<'a>],
) -> Result<Compiled<'a>, String> {
    let (db, program) = (&project.db, project.program);
    let mut compiled = Compiled {
        objects: Vec::new(),
        types: Vec::new(),
        functions: HashMap::new(),
    };
    for instance in collect_instances(db, program, roots, Tier::Baseline) {
        let owner = *instance.owner(db);
        let name = match instance.entry(db) {
            Entry::Body => owner_name(project, owner),
            Entry::Closure(_) => format!("a closure in {}", owner_name(project, owner)),
            Entry::Function(_) => {
                format!("a function value in {}", owner_name(project, owner))
            }
        };
        let value = matches!(owner, Owner::Item(item) if *item.kind(db) == ItemKind::Value);
        let code = match code(db, program, instance, Tier::Baseline) {
            Some(Ok(code)) => code,
            Some(Err(e)) => return Err(format!("cannot compile {name}: {e}")),
            None => return Err(format!("{name} has no body to compile")),
        };
        compiled.objects.push((code.slot, &code.object));
        for t in &code.types {
            if !compiled.types.contains(t) {
                compiled.types.push(t.clone());
            }
        }
        compiled.functions.insert(
            code.func,
            Function {
                params: code.params,
                returns: code.returns,
                name,
                module: owner.module(db),
                calls: code.calls.iter().map(|&c| func_id(c)).collect(),
                cell: (value && *instance.entry(db) == Entry::Body).then_some(code.slot),
            },
        );
    }
    Ok(compiled)
}

/// The settings entry stubs are compiled with: the host's target.
pub fn stub_settings() -> Result<CodegenSettings, String> {
    Ok(CodegenSettings {
        target: target_for("x86_64-unknown-linux-gnu").map_err(|e| e.to_string())?,
        opt: OptLevel::None,
    })
}

/// Where reports show a module's source.
pub trait Sources {
    /// The label of the text a position of the module is in, the text, and
    /// the position in it.
    fn locate(&self, module: ModuleId, position: u32) -> (String, &str, u32);
}

impl Sources for Project {
    fn locate(&self, module: ModuleId, position: u32) -> (String, &str, u32) {
        (
            self.file(module).shown.clone(),
            self.source(module),
            position,
        )
    }
}

/// A trap as the user sees it: what went wrong, where, and the functions
/// it happened in.
pub fn report(sources: &dyn Sources, functions: &HashMap<FuncId, Function>, trap: &Trap) -> String {
    let what = match trap.kind {
        TrapKind::Overflow => "arithmetic overflow",
        TrapKind::DivideByZero => "division by zero",
        TrapKind::Index => "index out of range",
        TrapKind::Hole => "reached `???`",
        TrapKind::NoMatch => "no arm of `case` matched",
        TrapKind::Error => "reached code with errors",
        TrapKind::Unsupported => "reached code the compiler does not support yet",
    };
    let first = trap.stack.first().map(|f| &functions[f]);
    let mut out = match (first, trap.position) {
        (Some(f), Some(position)) => {
            let (file, source, position) = sources.locate(f.module, position);
            render_at("trap", what, &file, source, position..position)
        }
        _ => format!("trap: {what}\n"),
    };
    // Runs of one function, as recursion makes them, are told once.
    let mut k = 0;
    while k < trap.stack.len() {
        let func = trap.stack[k];
        let run = trap.stack[k..].iter().take_while(|&&f| f == func).count();
        let name = &functions[&func].name;
        out += &match run {
            1 => format!("  in {name}\n"),
            n => format!("  in {name}, {n} frames\n"),
        };
        k += run;
    }
    out
}

/// The name of a body for reports: a function's, or a test's label.
pub fn owner_name(project: &Project, owner: Owner) -> String {
    let db = &project.db;
    match owner {
        Owner::Item(item) if item.name(db).text(db) == crate::repl::INPUT => "the input".into(),
        Owner::Item(item) => item.name(db).text(db).clone(),
        Owner::Test(test) => format!("test {}", test.label(db)),
    }
}

impl Image {
    /// Compiles the instances and everything they call, and loads them
    /// with the runtime's functions.
    pub fn build(project: &Project, roots: &[InstanceKey]) -> Result<Image, String> {
        let Compiled {
            objects,
            types,
            functions,
        } = compile(project, roots)?;
        let io = |e: std::io::Error| format!("cannot map memory for code: {e}");
        let mut arena = CodeArena::new(64 << 20).map_err(io)?;
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            symbols.define_runtime(func, crag_runtime::runtime_fn_addr(func));
        }
        let entries = load_group(&mut arena, &mut symbols, &objects)
            .map_err(|e| format!("cannot load the code: {e:?}"))?;
        let mut map = CodeMap::new();
        let mut addrs = HashMap::new();
        for (&(slot, object), entry) in objects.iter().zip(&entries) {
            map.add(slot.func, entry.addr(), object);
            addrs.insert(slot.func, entry.addr());
        }
        let mut worker = Worker::new();
        worker.set_types(Arc::new(Types::new(types)));
        worker.set_code_map(Arc::new(map));
        Ok(Image {
            arena,
            symbols,
            settings: stub_settings()?,
            functions,
            entries: addrs,
            worker,
        })
    }

    /// Runs a function without parameters on a fiber of its own: its result
    /// words, or the trap that ended it.
    pub fn run(&mut self, func: FuncId) -> Result<Vec<u64>, Trap> {
        let f = &self.functions[&func];
        assert_eq!(f.params, 0, "an entry point takes no parameters");
        let returns = f.returns;
        let stub = compile_entry_stub(0, returns, &self.settings).expect("the stub compiles");
        let stub = load(&mut self.arena, &self.symbols, &stub).expect("the stub loads");
        // SAFETY: the stub was compiled for the function's words, and both
        // stay loaded while the image exists, which outlives the fiber.
        let entry = self.entries[&func];
        let mut fiber = unsafe { Fiber::new(stub.addr(), entry, &[], FiberConfig::default()) }
            .expect("a fiber's stack can be mapped");
        match self.worker.resume(&mut fiber) {
            FiberState::Finished => {
                Ok(fiber.results().expect("finished")[..returns as usize].to_vec())
            }
            FiberState::Trapped => Err(fiber.trap().expect("trapped").clone()),
            state => unreachable!("a fiber nothing stops ended {state:?}"),
        }
    }

    /// A trap as the user sees it.
    pub fn report(&self, project: &Project, trap: &Trap) -> String {
        report(project, &self.functions, trap)
    }

    /// The heap the image's fibers allocate from.
    pub fn live_blocks(&mut self) -> usize {
        self.worker.heap().live_blocks()
    }
}
