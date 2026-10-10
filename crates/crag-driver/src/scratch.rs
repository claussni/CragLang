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

use std::collections::HashMap;
use std::io;

use crag_abi::FuncId;
use crag_backend::func_id;
use crag_codegen::{CodegenSettings, compile_entry_stub};
use crag_mir::InstanceKey;
use crag_session::{ImageCommand, RunResult, Session, ShippedFunction, Stub};

use crate::exec::{Function, compile, report, stub_settings};
use crate::project::Project;

/// A session with its scratch image, and what the host knows of the code
/// it shipped there.
pub struct Scratch {
    session: Session,
    settings: CodegenSettings,
    functions: HashMap<FuncId, Function>,
}

impl Scratch {
    pub fn start(command: ImageCommand) -> io::Result<Scratch> {
        Ok(Scratch {
            session: Session::start(command)?,
            settings: stub_settings().map_err(io::Error::other)?,
            functions: HashMap::new(),
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
        let sent = self
            .session
            .ship(&compiled.types, &stubs, &functions)
            .map_err(|e| e.to_string())?;
        self.functions.extend(compiled.functions);
        Ok(sent)
    }

    /// Ships a root without parameters and runs it in the image: its result
    /// words, or the report of the trap that ended it.
    pub fn run(
        &mut self,
        project: &Project,
        root: InstanceKey,
    ) -> Result<Result<Vec<u64>, String>, String> {
        self.ship(project, &[root])?;
        match self.session.run(func_id(root)).map_err(|e| e.to_string())? {
            RunResult::Finished(words) => Ok(Ok(words)),
            RunResult::Trapped(trap) => Ok(Err(report(project, &self.functions, &trap))),
        }
    }
}
