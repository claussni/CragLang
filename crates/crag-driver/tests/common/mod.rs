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

//! What the integration tests share: a watchdog, the scratch image's
//! command, a bare REPL and fresh project directories.

#![allow(dead_code)]

use std::fs;
use std::path::PathBuf;
use std::sync::Once;
use std::time::Duration;

use crag_driver::{Project, Repl, Scratch};
use crag_session::ImageCommand;

/// Ends the test process, printing `what`, if its tests take longer than
/// `secs` seconds. Only the first call of a test binary starts the timer.
pub fn watchdog(secs: u64, what: &str) {
    static START: Once = Once::new();
    START.call_once(|| {
        let what = what.to_owned();
        std::thread::spawn(move || {
            std::thread::sleep(Duration::from_secs(secs));
            eprintln!("{what}");
            std::process::abort();
        });
    });
}

/// The command that starts the scratch image: the `crag` binary under test.
pub fn image_command() -> ImageCommand {
    ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    }
}

/// A REPL on a bare project, with a scratch image of its own.
pub fn repl() -> Repl {
    let scratch = Scratch::start(image_command()).unwrap();
    Repl::new(Project::bare(), scratch)
}

/// A fresh directory `crag-{name}-{pid}` under the temporary directory,
/// holding the files; what was there before is removed.
pub fn project(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    for (path, text) in files {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    root
}
