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

//! The diagnostic registry's examples (Implementation Plan §11.12.2): every
//! entry's failing program reports its code, and its fixed program checks
//! clean. `CRAG_DIAG=E0301,E0302` checks only those entries.

mod common;

use crag_diag::{DiagEntry, ENTRIES};
use crag_driver::{Project, check};

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\n";

/// The codes and messages of a program's diagnostics, or why it would not
/// load.
fn diagnose(name: &str, example: &str) -> Result<Vec<(String, String)>, String> {
    let mut files = DiagEntry::files(example);
    if !files.iter().any(|(path, _)| path == "package.crag") {
        files.push(("package.crag".into(), MANIFEST.into()));
    }
    let dir = common::project(name, &[]);
    for (path, bytes) in &files {
        let path = dir.join(path);
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(path, bytes).unwrap();
    }
    let project = Project::load(&dir)?;
    let found = check(&project)
        .iter()
        .map(|d| (d.code.to_string(), d.message.clone()))
        .collect();
    let _ = std::fs::remove_dir_all(&dir);
    Ok(found)
}

#[test]
fn every_entry_has_examples_that_hold() {
    common::watchdog(600, "the diagnostic examples hung");
    let only: Option<Vec<String>> = std::env::var("CRAG_DIAG")
        .ok()
        .map(|v| v.split(',').map(|c| c.trim().to_uppercase()).collect());
    let mut problems = Vec::new();
    for entry in ENTRIES {
        let code = entry.code.as_str();
        if only.as_ref().is_some_and(|o| !o.iter().any(|c| c == code)) {
            continue;
        }
        let text = [
            entry.title,
            entry.spec,
            entry.rule,
            entry.rationale,
            entry.failing,
            entry.fixed,
        ];
        if text.iter().any(|t| t.contains("TODO")) {
            problems.push(format!("{code}: not written yet"));
            continue;
        }
        if entry.retired.is_some() {
            continue;
        }
        match diagnose(&format!("diag-{code}-failing"), entry.failing) {
            Err(why) => problems.push(format!("{code}: the failing example does not load: {why}")),
            Ok(found) if !found.iter().any(|(c, _)| c == code) => problems.push(format!(
                "{code}: the failing example does not report it, but {found:?}"
            )),
            Ok(_) => {}
        }
        match diagnose(&format!("diag-{code}-fixed"), entry.fixed) {
            Err(why) => problems.push(format!("{code}: the fixed example does not load: {why}")),
            Ok(found) if !found.is_empty() => {
                problems.push(format!("{code}: the fixed example reports {found:?}"))
            }
            Ok(_) => {}
        }
    }
    assert!(
        problems.is_empty(),
        "{} entries fail:\n{}",
        problems.len(),
        problems.join("\n")
    );
}
