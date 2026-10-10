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

//! The driver (Implementation Plan §11.4.15): the `crag` command's `run`
//! and `test`. It loads a project into the database, prints the
//! diagnostics of every module, compiles what the entry points reach, and
//! runs them on fibers.

pub mod diagnostics;
pub mod exec;
pub mod project;

use std::io::Write;
use std::path::Path;

use crag_backend::{func_id, record_layout};
use crag_hir::{ItemKind, Owner, item_tree, owners};
use crag_mir::{InstanceKey, Tier, mir};
use crag_types::{Ty, TyKind, prelude_item, signature};

pub use diagnostics::{Diagnostic, check, render_diagnostic};
pub use exec::Image;
pub use project::Project;

/// The exit status of a run that trapped (Specification §19.7.1).
pub const EXIT_TRAP: u8 = 70;

/// Loads the project and prints its diagnostics; the project if it has
/// none.
fn checked(root: &Path, out: &mut dyn Write) -> Option<Project> {
    let project = match Project::load(root) {
        Ok(project) => project,
        Err(e) => {
            let _ = writeln!(out, "error: {e}");
            return None;
        }
    };
    let diagnostics = check(&project);
    for d in &diagnostics {
        let file = &project.file(d.module).shown;
        let _ = write!(
            out,
            "{}",
            render_diagnostic(d, file, project.source(d.module))
        );
    }
    match diagnostics.len() {
        0 => Some(project),
        n => {
            let _ = writeln!(out, "{n} error{}", if n == 1 { "" } else { "s" });
            None
        }
    }
}

/// `crag run`: compiles what `main` of the project at `root` reaches, runs
/// it on a fiber and returns the exit status: 0 for `()`, the code of an
/// `ExitCode`, 1 for errors, or 70 for a trap, which it reports.
pub fn crag_run(root: &Path, out: &mut dyn Write) -> u8 {
    match run(root, out) {
        Ok(status) => status,
        Err(message) => {
            let _ = writeln!(out, "error: {message}");
            1
        }
    }
}

fn run(root: &Path, out: &mut dyn Write) -> Result<u8, String> {
    let Some(project) = checked(root, out) else {
        return Ok(1);
    };
    let (db, program) = (&project.db, project.program);
    let path = project
        .main
        .as_deref()
        .ok_or("package.crag names no `main` module")?;
    let module = project
        .module(path)
        .ok_or_else(|| format!("the `main` module `{path}` does not exist"))?;
    let item = item_tree(db, module)
        .items
        .iter()
        .map(|i| i.id)
        .find(|id| *id.kind(db) == ItemKind::Function && id.name(db).text(db) == "main")
        .ok_or_else(|| format!("module `{path}` declares no `fn main()`"))?;
    if !signature(db, program, item).params.is_empty() {
        return Err("`main` takes no parameters; arguments come from `args()`".into());
    }
    let key = InstanceKey::body(db, Owner::Item(item));
    let result = mir(db, program, key, Tier::Baseline)
        .as_ref()
        .ok_or("`main` has no body")?
        .result;
    let exit_code =
        prelude_item(db, program, "ExitCode").map(|i| Ty::new(db, TyKind::Named(i, Vec::new())));
    // Where the code lies in an `ExitCode`'s box.
    let code_offset = if result == Ty::unit(db) {
        None
    } else if Some(result) == exit_code {
        let (slots, _) = record_layout(db, program, result).ok_or("`ExitCode` has no layout")?;
        let slot = slots
            .iter()
            .find(|s| s.name.text(db) == "code")
            .ok_or("`ExitCode` has no `code`")?;
        Some(slot.offset as usize)
    } else {
        return Err("`main` must return `()` or `ExitCode`".into());
    };
    let mut image = Image::build(&project, &[key])?;
    match image.run(func_id(key)) {
        Ok(words) => Ok(match code_offset {
            None => 0,
            Some(offset) => {
                // SAFETY: the result is a live `ExitCode`, whose reference
                // the finished fiber left to its caller.
                let code = unsafe { ((words[0] as usize + offset) as *const i64).read() };
                u8::try_from(code).map_err(|_| format!("the exit code {code} is out of range"))?
            }
        }),
        Err(trap) => {
            let _ = write!(out, "{}", image.report(&project, &trap));
            Ok(EXIT_TRAP)
        }
    }
}

/// What `crag test` found.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct TestReport {
    /// The tests that passed, by module and label.
    pub passed: Vec<String>,
    /// The tests that failed, each with its trap report.
    pub failed: Vec<(String, String)>,
    /// Whether the project had errors, so no test ran.
    pub errors: bool,
}

impl TestReport {
    pub fn success(&self) -> bool {
        !self.errors && self.failed.is_empty()
    }
}

/// `crag test [filter]`: runs every test of the project at `root` whose
/// label contains `filter`, each in a fiber of its own, and prints how each
/// went. A test passes when its block completes and fails when it traps
/// (Specification §5.7).
pub fn crag_test(root: &Path, filter: Option<&str>, out: &mut dyn Write) -> TestReport {
    let mut report = TestReport::default();
    let Some(project) = checked(root, out) else {
        report.errors = true;
        return report;
    };
    let db = &project.db;
    let mut tests = Vec::new();
    for file in project.own() {
        for owner in owners(db, file.module) {
            let Owner::Test(test) = owner else { continue };
            let label = test.label(db);
            if filter.is_none_or(|f| label.contains(f)) {
                let key = InstanceKey::body(db, owner);
                tests.push((format!("{} {label}", file.shown), key));
            }
        }
    }
    let keys: Vec<InstanceKey> = tests.iter().map(|(_, key)| *key).collect();
    let mut image = match Image::build(&project, &keys) {
        Ok(image) => image,
        Err(e) => {
            let _ = writeln!(out, "error: {e}");
            report.errors = true;
            return report;
        }
    };
    for (name, key) in tests {
        match image.run(func_id(key)) {
            Ok(_) => {
                let _ = writeln!(out, "test {name} ... ok");
                report.passed.push(name);
            }
            Err(trap) => {
                let _ = writeln!(out, "test {name} ... FAILED");
                report.failed.push((name, image.report(&project, &trap)));
            }
        }
    }
    for (name, trap) in &report.failed {
        let _ = write!(out, "\n{name}:\n{trap}");
    }
    let _ = writeln!(
        out,
        "\n{} passed, {} failed",
        report.passed.len(),
        report.failed.len()
    );
    report
}
