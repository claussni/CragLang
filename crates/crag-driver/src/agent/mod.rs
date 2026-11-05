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

//! The agent server (Implementation Plan §11.12, Specification §20.10):
//! `crag mcp` serves the compiler's answers to coding agents over the
//! Model Context Protocol, through the facade of `crag-mcp`.
//!
//! The server works in one context at a time: the project a call names,
//! else the one in the directory the server started in, else `std` alone.
//! A context is a REPL session with its scratch image, so a snippet is
//! checked and run as REPL input is, and the session keeps what `eval`
//! defined until the context changes. Before each call the context reads
//! the project's files again, so the answers follow the agent's edits.

mod tools;

use std::path::{Path, PathBuf};

use crag_mcp::{CallError, Handler, Info, Outcome};
use crag_session::ImageCommand;
use serde_json::{Map, Value};

use crate::project::Project;
use crate::repl::Repl;
use crate::scratch::Scratch;

/// What the user allowed the agent's code, for the session.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Grants {
    /// Whether `eval` runs code with the `io` effect (§20.10).
    pub io_eval: bool,
}

/// A project's REPL session, with what its files were when it was loaded.
struct Context {
    /// The project's root; none for `std` alone.
    root: Option<PathBuf>,
    repl: Repl,
    shape: Shape,
}

/// What makes a project another one when it changes: its module files and
/// its manifest and SBOM. Other edits only change a module's text.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct Shape {
    files: Vec<PathBuf>,
    manifest: String,
    sbom: String,
}

impl Shape {
    fn of(root: Option<&Path>) -> Shape {
        let Some(root) = root else {
            return Shape::default();
        };
        Shape {
            files: crag_package::content::module_files(root).unwrap_or_default(),
            manifest: std::fs::read_to_string(root.join("package.crag")).unwrap_or_default(),
            sbom: std::fs::read_to_string(root.join("sbom.crag")).unwrap_or_default(),
        }
    }
}

/// The agent server's state, on the facade's handler thread.
pub struct AgentServer {
    command: ImageCommand,
    /// Where the server started, against which a call's project resolves.
    here: PathBuf,
    grants: Grants,
    context: Option<Context>,
}

impl AgentServer {
    pub fn new(command: ImageCommand, here: PathBuf, grants: Grants) -> AgentServer {
        AgentServer {
            command,
            here,
            grants,
            context: None,
        }
    }

    /// The project's root a call names, or the starting directory's if it
    /// is a project: none for `std` alone.
    fn root(&self, project: Option<&str>) -> Result<Option<PathBuf>, String> {
        let Some(project) = project else {
            return Ok(self
                .here
                .join("package.crag")
                .is_file()
                .then(|| self.here.clone()));
        };
        let dir = self
            .here
            .join(project)
            .canonicalize()
            .map_err(|e| format!("cannot find the project {project}: {e}"))?;
        if !dir.join("package.crag").is_file() {
            return Err(format!(
                "{} is no project: it has no package.crag",
                dir.display()
            ));
        }
        Ok(Some(dir))
    }

    /// The context of the project a call names, loaded again when its
    /// files or manifest changed, with its modules read from disk.
    fn context(&mut self, project: Option<&str>) -> Result<&mut Context, String> {
        let root = self.root(project)?;
        let shape = Shape::of(root.as_deref());
        let keep = self
            .context
            .as_ref()
            .is_some_and(|c| c.root == root && c.shape == shape);
        if !keep {
            // The old session and its image go first.
            self.context = None;
            let project = match &root {
                Some(root) => Project::load(root)?,
                None => Project::bare(),
            };
            let scratch = Scratch::start(self.command.clone())
                .map_err(|e| format!("cannot start the scratch image: {e}"))?;
            self.context = Some(Context {
                root,
                repl: Repl::new(project, scratch),
                shape,
            });
        }
        let context = self.context.as_mut().expect("a context");
        context.repl.project_mut().refresh();
        Ok(context)
    }
}

impl Handler for AgentServer {
    fn call(&mut self, tool: &str, args: &Map<String, Value>) -> Result<Outcome, CallError> {
        tools::call(self, tool, args)
    }
}

/// What the server tells a client about itself.
fn info() -> Info {
    Info {
        name: "crag".into(),
        version: env!("CARGO_PKG_VERSION").into(),
        instructions: "Crag's compiler, test runner and scratch image. Use `check` and \
                       `typeOf` before guessing how Crag works, `members` and `searchStd` to \
                       find functions, `eval` to try code, and `test` to run a project's tests. \
                       Every tool takes an optional `project`: a directory with a package.crag, \
                       relative to where the server started; without it the tools work in that \
                       directory's project, or with std alone."
            .into(),
    }
}

/// `crag mcp`: serves the agent server on standard input and `output`
/// until the input ends: the exit status.
pub fn serve(output: std::fs::File, command: ImageCommand, grants: Grants) -> u8 {
    let here = match std::env::current_dir() {
        Ok(here) => here,
        Err(e) => {
            eprintln!("crag mcp: {e}");
            return 1;
        }
    };
    let make = move || AgentServer::new(command, here, grants);
    match crag_mcp::serve(info(), &tools::specs(), make, output) {
        Ok(()) => 0,
        Err(e) => {
            eprintln!("crag mcp: {e}");
            1
        }
    }
}
