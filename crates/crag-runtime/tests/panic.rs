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

//! The panic hook of image processes, observed from outside: the test runs
//! itself as a child process that installs the hook and panics.

use std::os::unix::process::ExitStatusExt;
use std::process::Command;

const CHILD: &str = "CRAG_PANIC_TEST_CHILD";

/// Would announce itself if the panic unwound through its owner.
struct Guard;

impl Drop for Guard {
    fn drop(&mut self) {
        eprintln!("the guard was dropped");
    }
}

#[test]
fn a_panic_aborts_the_process_without_unwinding() {
    if let Some(mode) = std::env::var_os(CHILD) {
        if mode == "hook" {
            crag_runtime::abort_on_panic();
        }
        let _guard = Guard;
        panic!("deliberate panic in the child");
    }

    let child = |mode: &str| {
        Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "a_panic_aborts_the_process_without_unwinding",
                "--nocapture",
            ])
            .env(CHILD, mode)
            .output()
            .unwrap()
    };

    // With the hook: killed by the abort signal, the panic reported, and no
    // destructor run.
    let hooked = child("hook");
    let stderr = String::from_utf8_lossy(&hooked.stderr);
    assert_eq!(hooked.status.signal(), Some(libc::SIGABRT), "{stderr}");
    assert!(stderr.contains("deliberate panic in the child"), "{stderr}");
    assert!(!stderr.contains("the guard was dropped"), "{stderr}");

    // Without it, for contrast: the panic unwinds, the guard is dropped, and
    // the test harness exits normally with a failure.
    let plain = child("plain");
    let stderr = String::from_utf8_lossy(&plain.stderr);
    assert_eq!(plain.status.signal(), None, "{stderr}");
    assert!(!plain.status.success());
    assert!(stderr.contains("the guard was dropped"), "{stderr}");
}
