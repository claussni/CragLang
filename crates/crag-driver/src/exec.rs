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

use crag_abi::{CELL_FULL, FuncId, RuntimeFn, Shapes, SlotKey, TrapKind, TypeDescriptor};
use crag_backend::{code, func_id, shapes};
use crag_codegen::{CodeObject, CodegenSettings, OptLevel, compile_entry_stub, target_for};
use crag_eval::{EvalSite, const_eval};
use crag_hir::{ItemId, ModuleId, Owner};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_mir::{Entry, InstanceKey, Tier, collect_instances, mir};
use crag_runtime::{
    CodeMap, Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Trap, Types, Worker,
    decode_value,
};
use crag_session::Fill;

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
    /// The worker whose heap holds the values the compiler computed, kept
    /// as long as they are.
    _worker: Worker,
    /// Runs the fibers of the image's programs and their tasks.
    scheduler: Scheduler,
    /// The values the compiler computed, whose cells were filled.
    constants: usize,
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
    /// Its steps, by index, for the debugger.
    pub steps: Vec<StepView>,
}

/// A statement's step: where it starts in the module, and the locals whose
/// words a stopped task has there, in order.
#[derive(Clone, Debug)]
pub struct StepView {
    pub position: Option<u32>,
    pub locals: Vec<LocalView>,
}

/// A local at a step: its name and the shapes its value is printed by.
#[derive(Clone, Debug)]
pub struct LocalView {
    pub name: String,
    pub shapes: std::sync::Arc<Shapes>,
    pub root: u32,
}

/// The code of what some roots reach.
pub struct Compiled<'a> {
    /// Each function's code and the slot it fills.
    pub objects: Vec<(SlotKey, &'a CodeObject)>,
    /// The descriptors of the types the code uses, by index.
    pub types: Vec<(u32, TypeDescriptor)>,
    pub functions: HashMap<FuncId, Function>,
    /// The module-level values reached, by the keys of their cells.
    pub values: Vec<(SlotKey, ItemId<'a>)>,
}

/// The values among those compiled that the compiler computed, ready for
/// their cells (§11.6.8). A value that is no constant is computed when it
/// is first read, as before.
pub fn constants<'a>(project: &'a Project, values: &[(SlotKey, ItemId<'a>)]) -> Vec<Fill> {
    let (db, program) = (&project.db, project.program);
    let mut fills = Vec::new();
    for &(cell, item) in values {
        let Ok(value) = const_eval(db, program, EvalSite::Value(item)) else {
            continue;
        };
        let instance = InstanceKey::body(db, Owner::Item(item));
        let Some(body) = mir(db, program, instance, Tier::Baseline) else {
            continue;
        };
        let (shapes, root) = shapes(db, program, body.result);
        fills.push(Fill {
            cell,
            shapes,
            root,
            bytes: value.bytes.clone(),
        });
    }
    fills
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
        values: Vec::new(),
    };
    // Steps name the same types again and again.
    let mut shaped: HashMap<crag_types::Ty, (std::sync::Arc<Shapes>, u32)> = HashMap::new();
    for instance in collect_instances(db, program, roots, Tier::Baseline) {
        let owner = *instance.owner(db);
        let name = match instance.entry(db) {
            Entry::Body => owner_name(project, owner),
            Entry::Closure(_) => format!("a closure in {}", owner_name(project, owner)),
            Entry::Function(_) => {
                format!("a function value in {}", owner_name(project, owner))
            }
            Entry::Default(_) => format!("a default in {}", owner_name(project, owner)),
            Entry::Dispose => format!("the dispose code of {}", owner_name(project, owner)),
        };
        // `CRAG_MIR=1` shows the MIR of what is compiled and what code
        // generation does not support, for debugging the compiler.
        if std::env::var_os("CRAG_MIR").is_some()
            && let Some(body) = mir(db, program, instance, Tier::Baseline)
        {
            eprintln!("{name}\n{}", body.pretty(db));
        }
        let value = matches!(owner, Owner::Item(item) if item.kind(db).is_value());
        let code = match code(db, program, instance, Tier::Baseline) {
            Some(Ok(code)) => code,
            Some(Err(e)) => return Err(format!("cannot compile {name}: {e}")),
            None => return Err(format!("{name} has no body to compile")),
        };
        if std::env::var_os("CRAG_MIR").is_some() && !code.unsupported.is_empty() {
            eprintln!(
                "{name}: code generation does not support {:?}",
                code.unsupported
            );
        }
        compiled.objects.push((code.slot, &code.object));
        if let Owner::Item(item) = owner
            && value
            && *instance.entry(db) == Entry::Body
        {
            compiled.values.push((code.slot, item));
        }
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
                steps: code
                    .steps
                    .iter()
                    .map(|step| StepView {
                        position: step.position,
                        locals: step
                            .locals
                            .iter()
                            .map(|&(name, ty)| {
                                let (shapes, root) = shaped
                                    .entry(ty)
                                    .or_insert_with(|| {
                                        let (shapes, root) = crag_backend::shapes(db, program, ty);
                                        (std::sync::Arc::new(shapes), root)
                                    })
                                    .clone();
                                LocalView {
                                    name: name.text(db).clone(),
                                    shapes,
                                    root,
                                }
                            })
                            .collect(),
                    })
                    .collect(),
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
        metered: false,
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

/// What a trap of the kind tells the user.
pub fn trap_message(kind: TrapKind) -> &'static str {
    match kind {
        TrapKind::Overflow => "arithmetic overflow",
        TrapKind::DivideByZero => "division by zero",
        TrapKind::Index => "index out of range",
        TrapKind::Hole => "reached `???`",
        TrapKind::NoMatch => "no arm of `case` matched",
        TrapKind::Error => "reached code with errors",
        TrapKind::Unsupported => "reached code the compiler does not support yet",
        TrapKind::OutOfSteps => "ran out of steps",
        TrapKind::OutOfMemory => "ran out of memory",
        TrapKind::Cancelled => "was cancelled",
        TrapKind::Cycle => "a lazy value needed itself",
        TrapKind::Fault => "the environment failed, as writing to a closed output does",
    }
}

/// A trap as the user sees it: what went wrong, where, and the functions
/// it happened in.
pub fn report(sources: &dyn Sources, functions: &HashMap<FuncId, Function>, trap: &Trap) -> String {
    let what = trap_message(trap.kind);
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
            values,
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
        let settings = stub_settings()?;
        // Tasks start in the stubs for one argument, the task's closure.
        let task_entries = [0, 1, 2].map(|results| {
            let stub = compile_entry_stub(1, results, &settings).expect("the stub compiles");
            load(&mut arena, &symbols, &stub)
                .expect("the stub loads")
                .addr()
        });
        // SAFETY: the stubs stay loaded while the image exists, which
        // outlives its scheduler's fibers.
        unsafe { map.set_task_entries(task_entries) };
        let mut worker = Worker::new();
        let types = Arc::new(Types::new(types));
        let code = Arc::new(map);
        worker.set_types(types.clone());
        worker.set_code_map(code.clone());
        let scheduler = Scheduler::new(SchedulerConfig::default(), types.clone(), code);
        // The constants are in their cells before any code runs.
        for fill in constants(project, &values) {
            // SAFETY: the shapes describe the layouts the code was compiled
            // with, whose descriptors the worker has.
            let words = unsafe {
                decode_value(&fill.bytes, &fill.shapes, fill.root, worker.heap(), &types)
            }
            .map_err(|e| format!("cannot decode a constant: {}", e.0))?;
            symbols.cells().fill(fill.cell, &words);
        }
        let cells = symbols.cells();
        let constants = values
            .iter()
            .filter(|(key, _)| cells.state(*key) == Some(CELL_FULL))
            .count();
        Ok(Image {
            arena,
            symbols,
            settings,
            functions,
            entries: addrs,
            _worker: worker,
            scheduler,
            constants,
        })
    }

    /// Runs a function without parameters as the root task of the
    /// scheduler: its result words, or the trap that ended it.
    pub fn run(&mut self, func: FuncId) -> Result<Vec<u64>, Trap> {
        let f = &self.functions[&func];
        assert_eq!(f.params, 0, "an entry point takes no parameters");
        let returns = f.returns;
        let stub = compile_entry_stub(0, returns, &self.settings).expect("the stub compiles");
        let stub = load(&mut self.arena, &self.symbols, &stub).expect("the stub loads");
        // SAFETY: the stub was compiled for the function's words, and both
        // stay loaded while the image exists, which outlives the fiber.
        let entry = self.entries[&func];
        let fiber = unsafe { Fiber::new(stub.addr(), entry, &[], FiberConfig::default()) }
            .expect("a fiber's stack can be mapped");
        self.scheduler.spawn(fiber);
        let mut stopped = self.scheduler.wait();
        assert_eq!(stopped.len(), 1, "only the root task stops on its own");
        let fiber = stopped.pop().expect("one");
        match fiber.state() {
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

    /// How many values were in their cells when the image was built: the
    /// values the compiler computed.
    pub fn constants(&self) -> usize {
        self.constants
    }
}
