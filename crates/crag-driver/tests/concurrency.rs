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

//! End-to-end tests of the concurrency features (Plan §11.7.14): Crag
//! projects compiled and run on the scheduler. A watchdog ends the process
//! if a test hangs.

use std::fs;
use std::path::PathBuf;
use std::sync::Once;
use std::time::{Duration, Instant};

use crag_driver::crag_run;

/// Ends the test process if the tests take longer than a minute.
fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(60));
            eprintln!("the concurrency tests hung");
            std::process::abort();
        });
    });
}

fn project(name: &str, app: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-conc-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    fs::write(root.join("app.crag"), app).unwrap();
    root
}

/// Runs the project's `main`: its exit status and what it printed.
fn run(name: &str, app: &str) -> (u8, String) {
    watchdog();
    let root = project(name, app);
    let mut out = Vec::new();
    let code = crag_run(&root, &mut out);
    let _ = fs::remove_dir_all(&root);
    (code, String::from_utf8(out).unwrap())
}

#[test]
fn sleep_suspends_the_task() {
    let start = Instant::now();
    let (code, out) = run(
        "sleep",
        "import std.time\n\nfn main() -> ExitCode {\n  sleep(millis(50))\n  sleep(nanos(-1))\n  ExitCode(code: 3)\n}\n",
    );
    assert_eq!(code, 3, "{out}");
    assert!(start.elapsed() >= Duration::from_millis(50));
}
