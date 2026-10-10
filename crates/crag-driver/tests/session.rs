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

//! The session manager with the real image, `crag __image`.

use crag_session::{ImageCommand, ImageState, Message, Session, SessionError, describe};

fn command() -> ImageCommand {
    ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    }
}

/// Whether a process exists; a reaped one does not.
fn exists(pid: u32) -> bool {
    // SAFETY: signal 0 only checks that the process could be signalled.
    unsafe { libc::kill(pid as i32, 0) == 0 }
}

/// Sends a signal to a process and waits until it has died of it, so a
/// request cannot reach it before.
fn kill_with(pid: u32, signal: i32) {
    // SAFETY: the process is the test's own image.
    assert_eq!(unsafe { libc::kill(pid as i32, signal) }, 0);
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    loop {
        // The state follows the parenthesized name: `Z` for a zombie.
        let stat = std::fs::read_to_string(format!("/proc/{pid}/stat")).unwrap();
        if stat[stat.rfind(')').unwrap()..].starts_with(") Z") {
            return;
        }
        assert!(std::time::Instant::now() < deadline, "the image lives on");
        std::thread::sleep(std::time::Duration::from_millis(2));
    }
}

#[test]
fn the_scratch_image_answers_and_shuts_down() {
    let mut session = Session::start(command()).unwrap();
    let pid = session.scratch().pid();
    assert_ne!(pid, std::process::id());
    assert_eq!(session.scratch().state(), ImageState::Running);
    assert_eq!(
        session.request(&Message::Ping(7)).unwrap(),
        Message::Pong(7)
    );
    assert_eq!(
        session.request(&Message::Ping(u64::MAX)).unwrap(),
        Message::Pong(u64::MAX)
    );
    assert!(exists(pid));
    // It exits when asked to, well before it would be killed.
    let start = std::time::Instant::now();
    drop(session);
    assert!(start.elapsed() < crag_session::host::EXIT_GRACE / 2);
    assert!(!exists(pid));
}

#[test]
fn an_image_ends_when_the_host_goes_away() {
    let dir = std::env::temp_dir().join(format!("crag-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("host-gone.sock");
    let _ = std::fs::remove_file(&path);
    let listener = std::os::unix::net::UnixListener::bind(&path).unwrap();
    let mut child = std::process::Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(["__image", "scratch"])
        .arg(&path)
        .spawn()
        .unwrap();
    let (mut stream, _) = listener.accept().unwrap();
    let Message::Hello { pid, .. } = crag_session::read_message(&mut stream).unwrap() else {
        panic!("no Hello");
    };
    assert_eq!(pid, child.id());
    drop(stream);
    assert!(child.wait().unwrap().success());
    std::fs::remove_dir_all(&dir).unwrap();
}

#[test]
fn a_crashed_image_is_replaced() {
    let mut session = Session::start(command()).unwrap();
    let old = session.scratch().pid();
    // An image's panic aborts (Architecture §2.1). A SIGSEGV sent from
    // outside would not do: the standard library's handler, which tells
    // stack overflows from other faults, returns from one that is no fault.
    kill_with(old, libc::SIGABRT);
    let Err(SessionError::Exited(exit)) = session.request(&Message::Ping(1)) else {
        panic!("the request reached a dead image");
    };
    assert_eq!(exit.pid, old);
    assert_eq!(describe(exit.status), "was killed by signal 6 (SIGABRT)");
    assert_eq!(
        SessionError::Exited(exit).to_string(),
        format!(
            "the scratch image (process {old}) was killed by signal 6 (SIGABRT); \
             a fresh one has started"
        )
    );
    let new = session.scratch().pid();
    assert_ne!(new, old);
    assert!(!exists(old));
    assert_eq!(
        session.request(&Message::Ping(2)).unwrap(),
        Message::Pong(2)
    );
}

#[test]
fn a_runaway_image_is_restarted() {
    let mut session = Session::start(command()).unwrap();
    let old = session.scratch().pid();
    let exit = session.restart().unwrap();
    assert_eq!(exit.pid, old);
    assert_eq!(describe(exit.status), "was killed by signal 9 (SIGKILL)");
    assert!(!exists(old));
    assert_ne!(session.scratch().pid(), old);
    assert_eq!(
        session.request(&Message::Ping(3)).unwrap(),
        Message::Pong(3)
    );
}

#[test]
fn an_image_needs_a_socket() {
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(["__image", "scratch", "/nonexistent/image.sock"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8(out.stderr).unwrap();
    assert!(err.starts_with("crag image: "), "{err}");
    let out = std::process::Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(["__image", "app", "/nonexistent/image.sock"])
        .output()
        .unwrap();
    assert_eq!(out.status.code(), Some(2));
    assert_eq!(
        String::from_utf8(out.stderr).unwrap(),
        "crag image: no image is called `app`\n"
    );
}
