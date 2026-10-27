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

//! The app image and hot reload (Implementation Plan §11.8.4, §11.8.5): a
//! running server is edited, and new connections see the new code while
//! the server keeps running. A watchdog ends the process if a test hangs.

use std::fs;
use std::io::{Read, Write};
use std::net::{TcpListener, TcpStream};
use std::path::PathBuf;
use std::sync::Once;
use std::time::{Duration, Instant};

use crag_driver::{Project, Scratch};
use crag_session::ImageCommand;

fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(90));
            eprintln!("the reload tests hung");
            std::process::abort();
        });
    });
}

/// A server that answers each connection with `answer()` and then waits
/// for the next one, in a loop written as a tail call.
const SERVER: &str = r#"import std.io

fn answer() -> Bytes { b"v1" }

fn reply(c: Connection) -> () {
  case c.read() {
    bytes: Bytes -> {
      let written = c.write(answer())
    }
    _ -> ()
  }
}

fn serve(l: Listener) -> () {
  case l.accept() {
    c: Connection -> {
      reply(c)
      serve(l)
    }
    _ -> ()
  }
}

fn main() -> () {
  case listen(PORT) {
    l: Listener -> serve(l)
    _ -> ()
  }
}
"#;

/// The server with a task per connection, so that many workers run its
/// code while a reload comes.
const TASK_SERVER: &str = r#"import std.io
import std.task

fn answer() -> Bytes { b"v1" }

fn reply(c: Connection) -> () {
  case c.read() {
    bytes: Bytes -> {
      let written = c.write(answer())
    }
    _ -> ()
  }
}

fn main() -> () {
  case listen(PORT) {
    l: Listener -> {
      all(limit: 64) { g ->
        for i in 1..1000000 {
          case l.accept() {
            c: Connection -> g.start { -> reply(c) }
            _ -> ()
          }
        }
      }
    }
    _ -> ()
  }
}
"#;

fn free_port() -> u16 {
    TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port()
}

/// What the server answers a new connection.
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
        .set_read_timeout(Some(Duration::from_secs(20)))
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

fn setup(name: &str) -> Setup {
    watchdog();
    let root = std::env::temp_dir().join(format!("crag-reload-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    let port = free_port();
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

impl Setup {
    /// Changes the app's module as an edit of its file would.
    fn edit(&mut self, from: &str, to: &str) {
        let module = self.project.module("demo.app").unwrap();
        let text = self.project.source(module).replace(from, to);
        assert_ne!(
            text,
            self.project.source(module),
            "`{from}` is not in the code"
        );
        self.project.set_source(module, text);
    }
}

impl Drop for Setup {
    fn drop(&mut self) {
        let _ = self.scratch.stop_app();
        let _ = fs::remove_dir_all(&self.root);
    }
}

#[test]
fn a_running_server_takes_new_code_on_reload() {
    let mut s = setup("server");
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "v1");
    assert_eq!(ask(s.port), "v1");

    // A new body: the next connection gets it, from the same server.
    s.edit(r#"b"v1""#, r#"b"v2""#);
    let shipment = s.scratch.reload(&s.project).unwrap();
    assert!(shipment.functions >= 1, "{shipment:?}");
    assert_eq!(ask(s.port), "v2");

    // A new signature: a new slot, which the new `reply` calls.
    s.edit(
        r#"fn answer() -> Bytes { b"v2" }"#,
        r#"fn answer(n: Int) -> Bytes { b"v3" }"#,
    );
    s.edit("c.write(answer())", "c.write(answer(3))");
    s.scratch.reload(&s.project).unwrap();
    assert_eq!(ask(s.port), "v3");

    // Nothing changed: nothing is sent.
    assert_eq!(s.scratch.reload(&s.project).unwrap().functions, 0);
    assert_eq!(s.scratch.app_status(&s.project).unwrap(), None);
}

#[test]
fn a_reload_with_errors_changes_nothing() {
    let mut s = setup("errors");
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "v1");
    s.edit(r#"b"v1""#, "missing");
    let error = s.scratch.reload(&s.project).unwrap_err();
    assert!(
        error.contains("rejected") && error.contains("missing"),
        "{error}"
    );
    assert_eq!(ask(s.port), "v1");
    // Fixed, it reloads.
    s.edit("missing", r#"b"fixed""#);
    s.scratch.reload(&s.project).unwrap();
    assert_eq!(ask(s.port), "fixed");
}

#[test]
fn a_changed_type_gets_new_slots() {
    let mut s = setup("types");
    let with_type = SERVER
        .replace("PORT", &s.port.to_string())
        .replace(
            r#"fn answer() -> Bytes { b"v1" }"#,
            "type Reply(text: Bytes)\n\nfn make() -> Reply { Reply(text: b\"one\") }\n\nfn answer() -> Bytes { make().text }",
        );
    let module = s.project.module("demo.app").unwrap();
    s.project.set_source(module, with_type);
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "one");
    // `Reply` gains a field after `text`, which stays where it was: `make`
    // returns another layout, so it is another function to the slots, and
    // `answer`, which reads the field, is new code calling it.
    s.edit(
        "type Reply(text: Bytes)",
        "type Reply(text: Bytes, zone: Int)",
    );
    s.edit(r#"Reply(text: b"one")"#, r#"Reply(text: b"two", zone: 7)"#);
    s.scratch.reload(&s.project).unwrap();
    assert_eq!(ask(s.port), "two");
    // A field before `text` moves it: boxes of the old layout may be
    // alive, and the image frees boxes by their type, so this needs a
    // restart.
    s.edit(
        "type Reply(text: Bytes, zone: Int)",
        "type Reply(code: Int, text: Bytes, zone: Int)",
    );
    s.edit(
        r#"Reply(text: b"two", zone: 7)"#,
        r#"Reply(code: 1, text: b"three", zone: 7)"#,
    );
    let error = s.scratch.reload(&s.project).unwrap_err();
    assert!(error.contains("restart the app"), "{error}");
    assert_eq!(ask(s.port), "two");
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "three");
}

#[test]
fn a_stopped_app_is_gone() {
    let mut s = setup("stop");
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "v1");
    s.scratch.stop_app().unwrap();
    assert_eq!(
        s.scratch.app_status(&s.project).unwrap().as_deref(),
        Some("no app runs")
    );
    assert!(s.scratch.reload(&s.project).is_err());
    assert!(TcpStream::connect(("127.0.0.1", s.port)).is_err());
}

#[test]
fn reloads_under_load_lose_no_request() {
    let mut s = setup("load");
    s.scratch.start_app(&s.project).unwrap();
    under_load(&mut s);
}

#[test]
fn reloads_under_load_of_many_tasks_lose_no_request() {
    let mut s = setup("tasks");
    let module = s.project.module("demo.app").unwrap();
    s.project
        .set_source(module, TASK_SERVER.replace("PORT", &s.port.to_string()));
    s.scratch.start_app(&s.project).unwrap();
    under_load(&mut s);
}

/// Reloads eleven times while eight clients ask without pause.
fn under_load(s: &mut Setup) {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    assert_eq!(ask(s.port), "v1");
    let done = Arc::new(AtomicBool::new(false));
    let port = s.port;
    let clients: Vec<_> = (0..8)
        .map(|_| {
            let done = done.clone();
            std::thread::spawn(move || {
                let mut answers = Vec::new();
                while !done.load(Ordering::Relaxed) {
                    answers.push(ask(port));
                }
                answers
            })
        })
        .collect();
    let mut version = 1;
    for next in 2..=12 {
        s.edit(&format!(r#"b"v{version}""#), &format!(r#"b"v{next}""#));
        s.scratch.reload(&s.project).unwrap();
        version = next;
        std::thread::sleep(Duration::from_millis(20));
    }
    done.store(true, Ordering::Relaxed);
    let mut total = 0;
    for client in clients {
        let answers = client.join().unwrap();
        total += answers.len();
        let numbers: Vec<u32> = answers
            .iter()
            .map(|a| {
                a.strip_prefix('v')
                    .and_then(|n| n.parse().ok())
                    .unwrap_or_else(|| panic!("{a:?}"))
            })
            .collect();
        // Each client sees the versions in order.
        assert!(numbers.windows(2).all(|w| w[0] <= w[1]), "{numbers:?}");
    }
    assert!(total > 20, "only {total} requests were served");
    assert_eq!(ask(s.port), "v12");
}

#[test]
fn a_trap_in_reloaded_code_is_reported_with_its_stack() {
    let mut s = setup("trap");
    s.scratch.start_app(&s.project).unwrap();
    assert_eq!(ask(s.port), "v1");
    s.edit(
        r#"fn answer() -> Bytes { b"v1" }"#,
        "fn zero() -> Int { 0 }\n\nfn answer() -> Bytes { if 10 / zero() > 1 { b\"big\" } else { b\"small\" } }",
    );
    s.scratch.reload(&s.project).unwrap();
    // The connection ends without an answer, and so does the app.
    assert_eq!(ask(s.port), "");
    let deadline = Instant::now() + Duration::from_secs(20);
    let status = loop {
        if let Some(status) = s.scratch.app_status(&s.project).unwrap() {
            break status;
        }
        assert!(Instant::now() < deadline, "the app never ended");
        std::thread::sleep(Duration::from_millis(10));
    };
    assert!(status.contains("division by zero"), "{status}");
    // `main` tail-called `serve`, so its frame is gone.
    for frame in ["in answer", "in reply", "in serve"] {
        assert!(status.contains(frame), "{frame} missing from {status}");
    }
}

#[test]
fn the_repl_starts_reloads_and_stops_the_app() {
    use crag_driver::Repl;

    let s = setup("repl");
    let Setup { root, port, .. } = &s;
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    let mut repl = Repl::new(Project::load(root).unwrap(), scratch);
    let mut eval = |text: &str| match repl.eval_input(text) {
        Ok(output) => output.render(),
        Err(errors) => errors,
    };
    assert!(eval(":start").starts_with("the app runs"));
    assert_eq!(ask(*port), "v1");
    assert_eq!(eval(":status"), "the app runs\n");
    let file = root.join("app.crag");
    let text = fs::read_to_string(&file)
        .unwrap()
        .replace(r#"b"v1""#, r#"b"v2""#);
    fs::write(&file, text).unwrap();
    assert_eq!(
        eval(":status"),
        "the app runs\n  app.crag changed since the app got its code\n"
    );
    let reloaded = eval(":reload");
    assert!(
        reloaded.starts_with("reloaded from app.crag: "),
        "{reloaded}"
    );
    assert_eq!(ask(*port), "v2");
    assert_eq!(eval(":status"), "the app runs\n");
    assert_eq!(eval(":stop"), "the app stopped\n");
    assert_eq!(eval(":status"), "no app runs\n");
}
