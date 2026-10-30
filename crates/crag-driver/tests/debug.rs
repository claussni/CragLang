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

//! The debugger on the app image (Implementation Plan §11.8.6): a server
//! stops at a breakpoint, shows where and its locals, steps and goes on.
//! Every wait has a bound, and a watchdog ends the process if a test hangs.

use std::fs;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::Once;
use std::time::{Duration, Instant};

use crag_driver::debug::{Pause, Resume};
use crag_driver::{Project, Scratch};
use crag_session::ImageCommand;

fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(90));
            eprintln!("the debugger tests hung");
            std::process::abort();
        });
    });
}

const SERVER: &str = r#"import std.io

fn answer(n: Int) -> Bytes { if n > 2 { b"many" } else { b"one" } }

type Twice(n: Int, doubled: Int)

fn reply(c: Connection, n: Int) -> () {
  case c.read() {
    bytes: Bytes -> {
      let twice = Twice(n: n, doubled: n * 2)
      let doubled = twice.doubled
      let written = c.write(answer(doubled))
    }
    _ -> ()
  }
}

fn serve(l: Listener, n: Int) -> () {
  case l.accept() {
    c: Connection -> {
      reply(c, n)
      serve(l, n + 1)
    }
    _ -> ()
  }
}

fn main() -> () {
  case listen(PORT) {
    l: Listener -> serve(l, 1)
    _ -> ()
  }
}
"#;

/// The line of the first line of `SERVER` that holds `text`, from one.
fn line_of(text: &str) -> u32 {
    SERVER.lines().position(|l| l.contains(text)).unwrap() as u32 + 1
}

fn ask(port: u16) -> String {
    let deadline = Instant::now() + Duration::from_secs(20);
    let mut stream = loop {
        match TcpStream::connect(("127.0.0.1", port)) {
            Ok(stream) => break stream,
            Err(e) => {
                assert!(Instant::now() < deadline, "the server never listened: {e}");
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    };
    stream
        .set_read_timeout(Some(Duration::from_secs(30)))
        .unwrap();
    stream.write_all(b"hello").unwrap();
    let mut answer = String::new();
    stream.read_to_string(&mut answer).unwrap();
    answer
}

struct Setup {
    root: PathBuf,
    project: Project,
    scratch: Scratch,
    port: u16,
}

impl Drop for Setup {
    fn drop(&mut self) {
        let _ = self.scratch.stop_app();
        let _ = fs::remove_dir_all(&self.root);
    }
}

fn setup(name: &str) -> Setup {
    watchdog();
    let root = std::env::temp_dir().join(format!("crag-debug-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    let port = TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    fs::write(
        root.join("app.crag"),
        SERVER.replace("PORT", &port.to_string()),
    )
    .unwrap();
    let project = Project::load(&root).unwrap();
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    Setup {
        root,
        project,
        scratch,
        port,
    }
}

/// The next stopped task, waiting for one.
fn stopped(s: &mut Setup) -> Pause {
    let deadline = Instant::now() + Duration::from_secs(20);
    loop {
        if let Some(pause) = s.scratch.pauses(&s.project).unwrap().pop() {
            return pause;
        }
        assert!(Instant::now() < deadline, "no task stopped");
        std::thread::sleep(Duration::from_millis(5));
    }
}

#[test]
fn a_breakpoint_stops_the_task_that_reaches_it() {
    let mut s = setup("break");
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "one");
    let line = line_of("let doubled");
    let placed = s
        .scratch
        .set_breakpoints(&s.project, &[("app.crag".into(), line)])
        .unwrap();
    assert_eq!(placed, [1]);
    let port = s.port;
    let client = std::thread::spawn(move || ask(port));
    let pause = stopped(&mut s);
    assert_eq!(pause.function, "reply");
    assert_eq!((pause.file.as_str(), pause.line), ("app.crag", line));
    assert_eq!(pause.callers.first().map(String::as_str), Some("serve"));
    // The locals that hold values there, `n` of the second connection
    // among them, and `twice`, a flat record kept in registers; `bytes`,
    // which nothing uses any more, is gone.
    let locals = s.scratch.locals(pause.task).unwrap();
    assert!(locals.contains(&("n".into(), "2".into())), "{locals:?}");
    assert!(
        locals.contains(&("twice".into(), "Twice(n: 2, doubled: 4)".into())),
        "{locals:?}"
    );
    assert!(
        locals
            .iter()
            .any(|(name, value)| name == "c" && value.starts_with("Connection(")),
        "{locals:?}"
    );
    assert!(
        !locals.iter().any(|(name, _)| name == "bytes"),
        "{locals:?}"
    );

    // Over the statement: the next one in the same function.
    s.scratch.resume(pause.task, Resume::Over).unwrap();
    let next = stopped(&mut s);
    assert_eq!((next.function.as_str(), next.line), ("reply", line + 1));
    let locals = s.scratch.locals(next.task).unwrap();
    assert!(
        locals.contains(&("doubled".into(), "4".into())),
        "{locals:?}"
    );

    // Into the call of `answer`.
    s.scratch.resume(next.task, Resume::Into).unwrap();
    let inner = stopped(&mut s);
    assert_eq!(inner.function, "answer");
    assert_eq!(inner.callers.first().map(String::as_str), Some("reply"));

    // Out: steps are at the starts of statements, and `reply` has none
    // after the call, so the next is in `serve`, which called it.
    s.scratch.resume(inner.task, Resume::Out).unwrap();
    let out = stopped(&mut s);
    assert_eq!(
        (out.function.as_str(), out.line),
        ("serve", line_of("serve(l, n + 1)"))
    );
    s.scratch.resume(out.task, Resume::Continue).unwrap();
    assert_eq!(client.join().unwrap(), "many");

    // Without breakpoints nothing stops.
    s.scratch.set_breakpoints(&s.project, &[]).unwrap();
    assert_eq!(ask(s.port), "many");
    assert!(s.scratch.pauses(&s.project).unwrap().is_empty());
}

#[test]
fn breakpoints_survive_a_reload_and_a_stop_releases_stopped_tasks() {
    let mut s = setup("reload");
    s.scratch.start_app(&s.project).unwrap();
    let line = line_of("let doubled");
    s.scratch
        .set_breakpoints(&s.project, &[("app.crag".into(), line)])
        .unwrap();
    // A line moves down: the breakpoint follows its statement's line,
    // which it keeps by number.
    let module = s.project.module("demo.app").unwrap();
    let text = s
        .project
        .source(module)
        .replace(r#"b"one""#, r#"b"just one""#);
    s.project.set_source(module, text);
    s.scratch.reload(&s.project).unwrap();
    let port = s.port;
    let client = std::thread::spawn(move || ask(port));
    let pause = stopped(&mut s);
    assert_eq!((pause.function.as_str(), pause.line), ("reply", line));
    // Stopping the app lets the stopped task go, so it can be cancelled.
    s.scratch.stop_app().unwrap();
    let answer = client.join().unwrap();
    assert!(answer.is_empty() || answer == "just one", "{answer:?}");
}

#[test]
fn the_repl_debugs_the_app() {
    use crag_driver::Repl;

    let s = setup("repl");
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    let mut repl = Repl::new(Project::load(&s.root).unwrap(), scratch);
    let mut eval = |text: &str| match repl.eval_input(text) {
        Ok(output) => output.render(),
        Err(errors) => errors,
    };
    let line = line_of("let doubled");
    assert_eq!(
        eval(&format!(":break app.crag:{line}")),
        format!("breakpoint at app.crag:{line}\n")
    );
    assert!(eval(":start").starts_with("the app runs"));
    assert_eq!(eval(":break"), format!("app.crag:{line}\n"));
    let port = s.port;
    let client = std::thread::spawn(move || ask(port));
    let deadline = Instant::now() + Duration::from_secs(20);
    let paused = loop {
        let paused = eval(":paused");
        if paused != "no task is stopped\n" {
            break paused;
        }
        assert!(Instant::now() < deadline, "no task stopped");
        std::thread::sleep(Duration::from_millis(5));
    };
    assert_eq!(
        paused,
        format!("1: reply at app.crag:{line}, called from serve\n")
    );
    let locals = eval(":locals");
    assert!(locals.contains("n = 1\n"), "{locals}");
    assert_eq!(eval(":next"), format!("reply at app.crag:{}\n", line + 1));
    assert!(eval(":locals 1").contains("doubled = 2\n"));
    assert_eq!(eval(":locals 2"), "error: only 1 task is stopped\n");
    assert_eq!(eval(":clear"), "no breakpoints\n");
    assert_eq!(eval(":continue"), "");
    assert_eq!(client.join().unwrap(), "one");
    assert_eq!(eval(":paused"), "no task is stopped\n");
}
