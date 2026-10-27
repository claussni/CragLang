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

//! The example programs in `examples/`: each runs with `crag run`, passes
//! its tests and is formatted, and what it prints reaches the REPL. The
//! web example's test serves its page from a local server, so no test
//! needs the network.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::Once;
use std::time::Duration;

fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(120));
            eprintln!("the example tests hung");
            std::process::abort();
        });
    });
}

fn example(name: &str) -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../examples")
        .join(name)
}

/// The settings directory of a test, so the persisted code stays apart.
fn home(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!("crag-examples-{name}-{}", std::process::id()))
}

fn crag(name: &str, args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(args)
        .current_dir(example(name))
        .env("CRAG_HOME", home(name))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn text(output: &Output) -> String {
    format!(
        "{}{}",
        stdout(output),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// `crag test` and `crag fmt --check` pass in the example.
fn tested_and_formatted(name: &str) {
    let out = crag(name, &["test"], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    assert!(text(&out).contains(" 0 failed"), "{}", text(&out));
    let out = crag(name, &["fmt", "--check"], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
}

#[test]
fn hello_prints_its_greeting() {
    watchdog();
    let out = crag("hello", &["run"], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    assert_eq!(stdout(&out), "Hello, world!\n");
    tested_and_formatted("hello");
}

#[test]
fn files_prints_the_poem() {
    watchdog();
    let out = crag("files", &["run"], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let poem = std::fs::read_to_string(example("files").join("poem.txt")).unwrap();
    assert_eq!(stdout(&out), poem);
    tested_and_formatted("files");
}

#[test]
fn web_fetches_from_a_local_server() {
    watchdog();
    tested_and_formatted("web");
}

#[test]
fn the_repl_shows_what_programs_print_in_order() {
    watchdog();
    let input =
        "import std.io\nimport hello.main\nprintLine(greeting(\"Ada\"))\n1 + 2\n:start\n:stop\n";
    let out = crag("hello", &[], input);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let shown = stdout(&out);
    let ada = shown.find("Hello, Ada!\n").expect(&shown);
    let three = shown.find("3\n").expect(&shown);
    let app = shown.find("Hello, world!\n").expect(&shown);
    assert!(ada < three && three < app, "{shown}");
}
