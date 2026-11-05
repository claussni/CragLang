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

//! Compiling what a program reaches, and running it in an image in this
//! process.

use std::collections::HashMap;

use crag_abi::{Frame, FuncId, Shapes, SlotKey, TrapKind, TypeDescriptor};
use crag_backend::{code, func_id, shapes};
use crag_codegen::{CodeObject, CodegenSettings, OptLevel, compile_entry_stub, target_for};
use crag_eval::{EvalSite, const_eval};
use crag_hir::{ItemId, ModuleId, Owner};
use crag_mir::{Entry, InstanceKey, Tier, collect_instances, mir};
use crag_runtime::Trap;
use crag_session::{Fill, Message, RunResult, Stub, TierUp, run_result};

use crate::diagnostics::render_at;
use crate::project::Project;
use crate::scratch::{Shipped, shipped_functions};
use crate::tier::{Hot, tiers_up};

/// Compiled code in an image in this process, as `crag run` and `crag
/// test` run it: the image a session would start as a process of its own,
/// with the host's side of shipping and tier-up (Implementation Plan
/// §11.10.2) done here.
pub struct Image<'a> {
    project: &'a Project,
    image: crag_session::Image,
    /// The instances compiled, by their functions, for tier-up.
    instances: HashMap<FuncId, InstanceKey<'a>>,
    /// What the host knows of the code shipped: the functions, for
    /// reports, and the tier-up so far.
    shipped: Shipped,
    /// The values the compiler computed, whose cells were filled.
    constants: usize,
}

/// How many calls and back-edges make a function hot.
const HOT: u64 = 10_000;

/// How many calls and back-edges make a function hot: `HOT`, or the
/// count `CRAG_HOT` gives, so that tests can have most code optimized
/// while it runs; zero never optimizes. Read once.
pub(crate) fn hot() -> u64 {
    static HOT_COUNT: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *HOT_COUNT.get_or_init(|| {
        std::env::var("CRAG_HOT")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(HOT)
    })
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

/// A statement's step: where it starts in its module, and the locals whose
/// words a stopped task has there, in order.
#[derive(Clone, Debug)]
pub struct StepView {
    pub position: Option<u32>,
    /// The module the statement is in: the function's, or that of the
    /// innermost function inlined where it is.
    pub module: ModuleId,
    /// The functions whose code was inlined where it is, innermost first
    /// (Implementation Plan §11.10.1).
    pub inlined: Vec<FuncId>,
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
    /// The instances compiled, by their functions.
    pub instances: HashMap<FuncId, InstanceKey<'a>>,
}

/// Whether the code compiled can receive code: it reaches
/// `std.transport.run` (Implementation Plan §11.10.9).
pub fn receives<'a>(project: &'a Project, instances: &HashMap<FuncId, InstanceKey<'a>>) -> bool {
    let db = &project.db;
    instances.values().any(|i| match *i.owner(db) {
        Owner::Item(item) => {
            item.module(db).path(db) == "std.transport" && item.name(db).text(db) == "run"
        }
        Owner::Test(_) => false,
    })
}

/// What a receiver rebuilds the program from: its sources, the type
/// indices of the code compiled, and the cells of its values by the keys
/// the program gave them.
pub fn bundle<'a>(
    project: &'a Project,
    instances: &HashMap<FuncId, InstanceKey<'a>>,
    values: &[(SlotKey, ItemId<'a>)],
) -> crag_receive::Bundle {
    let (db, program) = (&project.db, project.program);
    let instances: Vec<InstanceKey<'a>> = instances.values().copied().collect();
    let indices = crag_backend::program_indices(db, program, &instances, Tier::compiled());
    let cells = values
        .iter()
        .map(|&(key, item)| (value_name(project, item), key))
        .collect();
    crag_receive::Bundle::of(db, program, indices, cells)
}

/// A module-level value as a receiver names it: `module.name`.
pub fn value_name(project: &Project, item: ItemId<'_>) -> String {
    let db = &project.db;
    format!("{}.{}", item.module(db).path(db), item.name(db).text(db))
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
        instances: HashMap::new(),
    };
    // Steps name the same types again and again.
    let mut shaped: HashMap<(crag_types::Ty, bool), (std::sync::Arc<Shapes>, u32)> = HashMap::new();
    let tier = Tier::compiled();
    for instance in collect_instances(db, program, roots, tier) {
        let owner = *instance.owner(db);
        let name = match instance.entry(db) {
            Entry::Body | Entry::Part => owner_name(project, owner),
            Entry::Closure(_) => format!("a closure in {}", owner_name(project, owner)),
            Entry::Function(_) | Entry::Adapter => {
                format!("a function value in {}", owner_name(project, owner))
            }
            Entry::Default(_) => format!("a default in {}", owner_name(project, owner)),
            Entry::Dispose => format!("the dispose code of {}", owner_name(project, owner)),
            Entry::Check => format!("the conditions of {}", owner_name(project, owner)),
        };
        // `CRAG_MIR=1` shows the MIR of what is compiled and what code
        // generation does not support, for debugging the compiler.
        if std::env::var_os("CRAG_MIR").is_some()
            && let Some(body) = mir(db, program, instance, tier)
        {
            eprintln!("{name}\n{}", body.pretty(db));
        }
        let value = matches!(owner, Owner::Item(item) if item.kind(db).is_value());
        let code = match code(db, program, instance, tier) {
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
        compiled.instances.insert(code.func, instance);
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
                        module: step
                            .inlined
                            .first()
                            .map_or(owner, |i| *i.owner(db))
                            .module(db),
                        inlined: step.inlined.iter().map(|&i| func_id(i)).collect(),
                        locals: step
                            .locals
                            .iter()
                            .map(|&(name, ty, split)| {
                                let (shapes, root) = shaped
                                    .entry((ty, split))
                                    .or_insert_with(|| {
                                        let (shapes, root) = match split {
                                            true => crag_backend::split_shapes(db, program, ty),
                                            false => crag_backend::shapes(db, program, ty),
                                        };
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
        profile: None,
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
    kind.message()
}

/// A trap as the user sees it: what went wrong, where, and the functions
/// it happened in.
pub fn report(sources: &dyn Sources, functions: &HashMap<FuncId, Function>, trap: &Trap) -> String {
    let what = match &trap.detail {
        Some(detail) => format!("{}: {detail}", trap_message(trap.kind)),
        None => trap_message(trap.kind).to_string(),
    };
    let what = what.as_str();
    let first = trap.stack.first().map(|f| &functions[&f.func]);
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
        let frame = trap.stack[k];
        let run = trap.stack[k..].iter().take_while(|&&f| f == frame).count();
        let name = frame_name(functions, frame);
        out += &match run {
            1 => format!("  in {name}\n"),
            n => format!("  in {name}, {n} frames\n"),
        };
        k += run;
    }
    out
}

/// The name of a frame for reports: its function's, marked when its code
/// was inlined into the frame after it.
pub fn frame_name(functions: &HashMap<FuncId, Function>, frame: Frame) -> String {
    let name = functions
        .get(&frame.func)
        .map_or_else(|| format!("function {}", frame.func.0), |f| f.name.clone());
    match frame.inlined {
        true => format!("{name} (inlined)"),
        false => name,
    }
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

/// The entry stubs an image needs for compiled code with these roots: the
/// stubs tasks start in, for one argument, the task's closure, and one for
/// the words of each root without parameters.
pub(crate) fn entry_stubs(
    settings: &CodegenSettings,
    compiled: &Compiled,
    roots: &[InstanceKey],
) -> Result<Vec<Stub>, String> {
    let mut shapes: Vec<(u32, u32)> = (0..3).map(|returns| (1, returns)).collect();
    for &root in roots {
        let f = &compiled.functions[&func_id(root)];
        if f.params == 0 && !shapes.contains(&(0, f.returns)) {
            shapes.push((0, f.returns));
        }
    }
    shapes
        .into_iter()
        .map(|(params, returns)| {
            let object = compile_entry_stub(params, returns, settings)
                .map_err(|e| format!("cannot compile an entry stub: {e}"))?;
            Ok(Stub {
                params,
                returns,
                object,
            })
        })
        .collect()
}

/// Why an image did not do as asked, from its answer.
fn refused(answer: Option<Message>) -> String {
    match answer {
        Some(Message::Failed(why)) => why,
        other => format!("the image answered {other:?}"),
    }
}

impl<'a> Image<'a> {
    /// Compiles the instances and everything they call, and loads them into
    /// an image, with the values the compiler computed in their cells.
    pub fn build(project: &'a Project, roots: &[InstanceKey<'a>]) -> Result<Image<'a>, String> {
        let compiled = compile(project, roots)?;
        let stubs = entry_stubs(&stub_settings()?, &compiled, roots)?;
        let fills = constants(project, &compiled.values);
        let constants = fills.len();
        let mut image =
            crag_session::Image::new().map_err(|e| format!("cannot map memory for code: {e}"))?;
        let load = Message::Load {
            types: compiled.types.clone(),
            stubs,
            functions: shipped_functions(&compiled),
            reset: Vec::new(),
            fills,
        };
        match image.answer(load) {
            Some(Message::Loaded) => {}
            other => return Err(refused(other)),
        }
        // A program that runs received code checks and compiles it itself,
        // sharing the cells of its values (§11.10.9).
        if receives(project, &compiled.instances) {
            let bytes = bundle(project, &compiled.instances, &compiled.values).encode();
            match image.answer(Message::Receive(bytes)) {
                Some(Message::Done) => {}
                other => return Err(refused(other)),
            }
        }
        Ok(Image {
            project,
            image,
            instances: compiled.instances,
            shipped: Shipped {
                functions: compiled.functions,
                ..Shipped::default()
            },
            constants,
        })
    }

    /// Runs a function without parameters as the root task of the image:
    /// its result words, or the trap that ended it. Functions that become
    /// hot meanwhile are swapped for optimized code.
    pub fn run(&mut self, func: FuncId) -> Result<Vec<u64>, Trap> {
        let mut hot = Hot {
            project: self.project,
            instances: &self.instances,
            shipped: &mut self.shipped,
        };
        let tier = tiers_up().then_some(&mut hot as &mut dyn TierUp);
        match run_result(self.image.run_with(func, tier)) {
            Ok(RunResult::Finished(words)) => Ok(words),
            Ok(RunResult::Trapped(trap)) => Err(trap),
            Ok(other) => unreachable!("a run in this process ended {other:?}"),
            Err(e) => panic!("the image refused the run: {e}"),
        }
    }

    /// A trap as the user sees it.
    pub fn report(&self, project: &Project, trap: &Trap) -> String {
        report(project, &self.shipped.functions, trap)
    }

    /// How many values were in their cells when the image was built: the
    /// values the compiler computed.
    pub fn constants(&self) -> usize {
        self.constants
    }

    /// How many functions runs swapped for optimized code so far.
    pub fn optimized(&self) -> usize {
        self.shipped.optimized
    }
}
