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

//! `crag build` (Specification §20.6, §20.7): the project's release
//! executable, `dist/<package>`.
//!
//! The build checks the project and runs its tests first, as `crag test`
//! does; a failing test builds nothing, unless `--skip-tests` (`:build
//! skip-tests` in the REPL) leaves the tests out. It then compiles what
//! `main` reaches in the release tier into an object (Implementation Plan
//! §11.10.3) and links it with the runtime archive (§11.10.4, §11.10.5).
//! The object is written to a directory of its own, which goes again.

use std::io::Write;
use std::path::{Path, PathBuf};

use crag_aot::{MAIN, Target, emit_object, link, runtime_archive};

use crate::commands::{Args, Spec};
use crate::{checked, main_instance, main_result, run_tests};

/// What `build` accepts.
pub const BUILD: Spec = Spec {
    switches: &["skip-tests"],
    values: &[],
};

/// The directory the executable is written to, in the project's root.
pub const DIST: &str = "dist";

/// `crag build` in the project at `root`: the exit status, 0 once the
/// executable is written.
pub fn crag_build(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    match build(root, args, out) {
        Ok(status) => status,
        Err(message) => {
            let _ = writeln!(out, "error: {message}");
            1
        }
    }
}

fn build(root: &Path, args: &Args, out: &mut dyn Write) -> Result<u8, String> {
    if let Some(word) = args.positional.first() {
        return Err(format!("`build` takes no argument `{word}`"));
    }
    let Some(project) = checked(root, out) else {
        return Ok(1);
    };
    let key = main_instance(&project)?;
    main_result(&project, key)?;
    if !args.switch("skip-tests") {
        if !run_tests(&project, None, out).success() {
            let _ = writeln!(
                out,
                "error: the tests failed, so nothing was built; `--skip-tests` builds without them"
            );
            return Ok(1);
        }
        let _ = writeln!(out);
    }
    let emitted = emit_object(&project.db, project.program, &[(key, MAIN)])?;
    let target = Target::host();
    let archive = runtime_archive(target).map_err(|e| e.to_string())?;
    let dist = root.join(DIST);
    std::fs::create_dir_all(&dist).map_err(|e| format!("cannot create {}: {e}", dist.display()))?;
    let exe = dist.join(&project.package);
    let scratch = Scratch::new(&project.package)?;
    let object = scratch.0.join(format!("{}.o", project.package));
    std::fs::write(&object, &emitted.bytes)
        .map_err(|e| format!("cannot write {}: {e}", object.display()))?;
    link(&[object], &[archive], target, &exe).map_err(|e| e.to_string())?;
    let _ = writeln!(out, "built {DIST}/{}", project.package);
    Ok(0)
}

/// A directory of the build's own for the object, removed when dropped.
struct Scratch(PathBuf);

impl Scratch {
    fn new(package: &str) -> Result<Scratch, String> {
        let dir = std::env::temp_dir().join(format!("crag-build-{package}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir)
            .map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
        Ok(Scratch(dir))
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}
