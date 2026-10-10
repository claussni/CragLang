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

use std::collections::{BTreeSet, HashMap};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io;

use crag_abi::{FuncId, SlotKey};
use crag_backend::{func_id, shapes};
use crag_codegen::{CodeObject, CodegenSettings, compile_entry_stub};
use crag_mir::InstanceKey;
use crag_runtime::Trap;
use crag_session::{ImageCommand, RunResult, Session, ShippedFunction, Stub};
use crag_types::Ty;

use crate::exec::{Function, Sources, compile, report, stub_settings};
use crate::project::Project;

/// A session with its scratch image, and what the host knows of the code
/// it shipped there.
pub struct Scratch {
    session: Session,
    settings: CodegenSettings,
    functions: HashMap<FuncId, Function>,
    /// For each module-level value, a hash of the code its value was
    /// computed with: its own and what that calls.
    values: HashMap<SlotKey, u64>,
}

impl Scratch {
    pub fn start(command: ImageCommand) -> io::Result<Scratch> {
        Ok(Scratch {
            session: Session::start(command)?,
            settings: stub_settings().map_err(io::Error::other)?,
            functions: HashMap::new(),
            values: HashMap::new(),
        })
    }

    pub fn session(&mut self) -> &mut Session {
        &mut self.session
    }

    /// Compiles what the roots reach and ships what the image lacks, with
    /// an entry stub for each root: how many functions were sent.
    pub fn ship(&mut self, project: &Project, roots: &[InstanceKey]) -> Result<usize, String> {
        let compiled = compile(project, roots)?;
        let functions: Vec<ShippedFunction> = compiled
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
            .collect();
        let mut stubs = Vec::new();
        for &root in roots {
            let f = &compiled.functions[&func_id(root)];
            if f.params == 0 && !stubs.iter().any(|s: &Stub| s.returns == f.returns) {
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
        let mut values = Vec::new();
        for (&id, f) in &compiled.functions {
            if let Some(cell) = f.cell {
                let hash = code_hash(id, &compiled.functions, &codes);
                if self.values.get(&cell) != Some(&hash) {
                    values.push((cell, hash));
                }
            }
        }
        let reset: Vec<SlotKey> = values.iter().map(|&(cell, _)| cell).collect();
        let sent = self
            .session
            .ship(&compiled.types, &stubs, &functions, &reset)
            .map_err(|e| e.to_string())?;
        self.functions.extend(compiled.functions);
        self.values.extend(values);
        Ok(sent)
    }

    /// Ships a root without parameters and runs it in the image: how the
    /// run ended.
    pub fn execute(&mut self, project: &Project, root: InstanceKey) -> Result<RunResult, String> {
        self.ship(project, &[root])?;
        self.session.run(func_id(root)).map_err(|e| e.to_string())
    }

    /// Ships a root without parameters and runs it in the image, which
    /// shows its result, of type `ty`, and releases it.
    pub fn show(
        &mut self,
        project: &Project,
        root: InstanceKey,
        ty: Ty,
    ) -> Result<RunResult, String> {
        self.ship(project, &[root])?;
        let (shapes, shape) = shapes(&project.db, project.program, ty);
        self.session
            .show(func_id(root), &shapes, shape)
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
        report(sources, &self.functions, trap)
    }
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
