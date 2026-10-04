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
