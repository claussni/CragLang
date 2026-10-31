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

//! Running code in the scratch image (Implementation Plan §11.6.3): the
//! host compiles what the roots reach, ships what the image lacks, and asks
//! the image to run a root. A crash in the code ends only the image.

use std::collections::{BTreeSet, HashMap, HashSet};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io;

use crag_abi::{FuncId, SlotKey};
use crag_backend::{func_id, shapes};
use crag_codegen::{CodeObject, CodegenSettings, compile_entry_stub};
use crag_mir::InstanceKey;
use crag_runtime::Trap;
use crag_session::{ImageCommand, ImageKind, RunResult, Session, ShippedFunction, Stub, TierUp};
use crag_types::Ty;

use crate::exec::{Compiled, Function, Sources, compile, constants, report, stub_settings};
use crate::project::Project;
use crate::tier::{Hot, tiers_up};

/// What the host knows of the code it shipped to an image.
#[derive(Default)]
pub(crate) struct Shipped {
    pub functions: HashMap<FuncId, Function>,
    /// For each module-level value, a hash of the code its value was
    /// computed with: its own and what that calls.
    pub values: HashMap<SlotKey, u64>,
    /// The hot functions compiled in the optimizing tier since their code
    /// was last shipped, swapped in or not (Implementation Plan §11.10.2).
    pub tried: HashSet<FuncId>,
    /// How many functions were swapped for optimized code.
    pub optimized: usize,
    /// Whether the code differs from what the image runs, which keeps the
    /// image from tiering up until code is shipped again.
    pub stale: bool,
}

/// What a shipment did.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Shipment {
    /// Functions sent, new or with new code.
    pub functions: usize,
    /// Module-level values to be computed again.
    pub values: usize,
}

/// A session with its scratch image and, while the app runs, its app
/// image, and what the host knows of the code it shipped to each.
pub struct Scratch {
    pub(crate) session: Session,
    settings: CodegenSettings,
    pub(crate) scratch: Shipped,
    pub(crate) app: Shipped,
    /// How many values the compiler computed were sent to their cells.
    constants: usize,
    /// The app's breakpoints, by file and line, which reloads keep.
    pub(crate) breakpoints: Vec<(String, u32)>,
    /// How the app image ended when a request no one waited for found out,
    /// such as one for tier-up, to be told by the next status.
    pub(crate) app_ended: Option<String>,
}

impl Scratch {
    pub fn start(command: ImageCommand) -> io::Result<Scratch> {
        Ok(Scratch {
            session: Session::start(command)?,
            settings: stub_settings().map_err(io::Error::other)?,
            scratch: Shipped::default(),
            app: Shipped::default(),
            constants: 0,
            breakpoints: Vec::new(),
            app_ended: None,
        })
    }

    /// How many values the compiler computed were sent to their cells,
    /// each time their code changed.
    pub fn constants(&self) -> usize {
        self.constants
    }

    /// Whether the app runs.
    pub fn app_runs(&self) -> bool {
        self.session.app().is_some()
    }

    pub fn session(&mut self) -> &mut Session {
        &mut self.session
    }

    /// Compiles what the roots reach and ships what the image lacks, with
    /// an entry stub for each root: how many functions were sent.
    pub fn ship(&mut self, project: &Project, roots: &[InstanceKey]) -> Result<usize, String> {
        let compiled = compile(project, roots)?;
        Ok(self
            .ship_to(ImageKind::Scratch, project, &compiled, roots, true)?
            .functions)
    }

    /// Ships compiled code to an image. Values whose code changed are
    /// computed again; with `fill`, those the compiler computed are filled
    /// in, which only an image that runs nothing yet may take.
    pub(crate) fn ship_to(
        &mut self,
        kind: ImageKind,
        project: &Project,
        compiled: &Compiled,
        roots: &[InstanceKey],
        fill: bool,
    ) -> Result<Shipment, String> {
        let functions = shipped_functions(compiled);
        // Tasks start in the stubs for one argument, the task's closure;
        // the host ships each stub once.
        let mut stubs = Vec::new();
        for returns in 0..3 {
            let object = compile_entry_stub(1, returns, &self.settings)
                .map_err(|e| format!("cannot compile an entry stub: {e}"))?;
            stubs.push(Stub {
                params: 1,
                returns,
                object,
            });
        }
        for &root in roots {
            let f = &compiled.functions[&func_id(root)];
            if f.params == 0
                && !stubs
                    .iter()
                    .any(|s: &Stub| s.params == 0 && s.returns == f.returns)
            {
                let object = compile_entry_stub(0, f.returns, &self.settings)
                    .map_err(|e| format!("cannot compile an entry stub: {e}"))?;
                stubs.push(Stub {
                    params: 0,
                    returns: f.returns,
                    object,
                });
            }
        }
        // A value is computed again once the code it is computed with
        // changed. Every run ships its root first, which reaches every value
        // the run may read, so the image never reads a value computed with
        // other code.
        let codes: HashMap<FuncId, &CodeObject> = compiled
            .objects
            .iter()
            .map(|&(slot, o)| (slot.func, o))
            .collect();
        let shipped = match kind {
            ImageKind::Scratch => &mut self.scratch,
            ImageKind::App => &mut self.app,
        };
        let mut values = Vec::new();
        for (&id, f) in &compiled.functions {
            if let Some(cell) = f.cell {
                let hash = code_hash(id, &compiled.functions, &codes);
                if shipped.values.get(&cell) != Some(&hash) {
                    values.push((cell, hash));
                }
            }
        }
        let reset: Vec<SlotKey> = values.iter().map(|&(cell, _)| cell).collect();
        // A value computed again with new code is filled with what the
        // compiler computed, if it is a constant.
        let changed: Vec<_> = compiled
            .values
            .iter()
            .filter(|(cell, _)| reset.contains(cell))
            .copied()
            .collect();
        let fills = if fill {
            constants(project, &changed)
        } else {
            Vec::new()
        };
        let changed = self.session.changed(kind, &functions);
        let sent = self
            .session
            .ship_to(kind, &compiled.types, &stubs, &functions, &reset, &fills)
            .map_err(|e| e.to_string())?;
        let shipped = match kind {
            ImageKind::Scratch => &mut self.scratch,
            ImageKind::App => &mut self.app,
        };
        // New code is baseline code, which may become hot in turn.
        shipped.tried.retain(|f| !changed.contains(f));
        shipped.stale = false;
        shipped.functions.extend(compiled.functions.clone());
        shipped.values.extend(values);
        self.constants += fills.len();
        Ok(Shipment {
            functions: sent,
            values: reset.len(),
        })
    }

    /// Ships a root without parameters and runs it in the image: how the
    /// run ended. Functions that become hot meanwhile are swapped for
    /// optimized code.
    pub fn execute(&mut self, project: &Project, root: InstanceKey) -> Result<RunResult, String> {
        let compiled = compile(project, &[root])?;
        self.ship_to(ImageKind::Scratch, project, &compiled, &[root], true)?;
        let mut hot = Hot {
            project,
            instances: &compiled.instances,
            shipped: &mut self.scratch,
        };
        let tier = tiers_up().then_some(&mut hot as &mut dyn TierUp);
        self.session
            .run_with(func_id(root), tier)
            .map_err(|e| e.to_string())
    }

    /// Ships a root without parameters and runs it in the image, which
    /// shows its result, of type `ty`, and releases it; with `text`, a
    /// `Str` as it is.
    pub fn show(
        &mut self,
        project: &Project,
        root: InstanceKey,
        ty: Ty,
        text: bool,
    ) -> Result<RunResult, String> {
        let compiled = compile(project, &[root])?;
        self.ship_to(ImageKind::Scratch, project, &compiled, &[root], true)?;
        let (shapes, shape) = shapes(&project.db, project.program, ty);
        let mut hot = Hot {
            project,
            instances: &compiled.instances,
            shipped: &mut self.scratch,
        };
        let tier = tiers_up().then_some(&mut hot as &mut dyn TierUp);
        self.session
            .show_with(func_id(root), &shapes, shape, text, tier)
            .map_err(|e| e.to_string())
    }

    /// Ships a root without parameters and runs it in the image: its result
    /// words, or the report of the trap or interrupt that ended it.
    pub fn run(
        &mut self,
        project: &Project,
        root: InstanceKey,
    ) -> Result<Result<Vec<u64>, String>, String> {
        Ok(match self.execute(project, root)? {
            RunResult::Finished(words) => Ok(words),
            RunResult::Trapped(trap) => Err(self.report(project, &trap)),
            RunResult::Interrupted => Err("interrupted\n".into()),
            RunResult::Shown(_) => unreachable!("a run shows nothing"),
        })
    }

    /// A trap in shipped code as the user sees it.
    pub fn report(&self, sources: &dyn Sources, trap: &Trap) -> String {
        report(sources, &self.scratch.functions, trap)
    }
}

/// The functions of compiled code as an image takes them.
pub(crate) fn shipped_functions(compiled: &Compiled) -> Vec<ShippedFunction> {
    compiled
        .objects
        .iter()
        .map(|&(slot, object)| {
            let f = &compiled.functions[&slot.func];
            ShippedFunction {
                id: slot.func,
                signature: slot.signature,
                params: f.params,
                returns: f.returns,
                object: object.clone(),
            }
        })
        .collect()
}

/// A hash of the code a function runs: its own and that of every function
/// it reaches.
fn code_hash(
    root: FuncId,
    functions: &HashMap<FuncId, Function>,
    codes: &HashMap<FuncId, &CodeObject>,
) -> u64 {
    let mut reached = BTreeSet::from([root.0]);
    let mut work = vec![root];
    while let Some(f) = work.pop() {
        for &callee in functions.get(&f).map_or(&[][..], |f| &f.calls) {
            if reached.insert(callee.0) {
                work.push(callee);
            }
        }
    }
    let mut hasher = DefaultHasher::new();
    for f in reached {
        f.hash(&mut hasher);
        codes.get(&FuncId(f)).hash(&mut hasher);
    }
    hasher.finish()
}
