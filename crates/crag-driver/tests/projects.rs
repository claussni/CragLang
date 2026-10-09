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

//! `crag run` and `crag test` on small multi-module projects on disk.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use crag_driver::{EXIT_TRAP, crag_run, crag_test};

/// A fresh project directory holding the files.
fn project(name: &str, files: &[(&str, &str)]) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    for (path, text) in files {
        let path = root.join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }
    root
}

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\nmain demo.app\n";

const SHAPE: &str = r#"pub type Point(x: Int, y: Int)

pub fn area(p: Point) -> Int {
  p.x * p.y
}

pub fn sum(xs: List[Int]) -> Int {
  var total = 0
  for x in xs {
    total = total + x
  }
  total
}

test "area multiplies" {
  if area(Point(x: 3, y: 4)) != 12 { ??? }
}
"#;

const APP: &str = r#"import demo.geo.shape

fn main() -> ExitCode {
  let p = Point(x: 2, y: 3)
  ExitCode(code: area(p) + sum([1, 2, 3]))
}

test "sums" {
  if sum([1, 2]) != 3 { ??? }
}

test "reads past the end" {
  let xs = [1, 2]
  let y = xs[5]
}
"#;

fn demo(name: &str) -> PathBuf {
    project(
        name,
        &[
            ("package.crag", MANIFEST),
            ("geo/shape.crag", SHAPE),
            ("app.crag", APP),
        ],
    )
}

fn text(out: Vec<u8>) -> String {
    String::from_utf8(out).unwrap()
}

#[test]
fn run_returns_the_exit_code_of_main() {
    let root = demo("run");
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 12, "{}", text(out));
}

#[test]
fn test_runs_every_test_in_a_fiber_of_its_own() {
    let root = demo("test");
    let mut out = Vec::new();
    let report = crag_test(&root, None, &mut out);
    let out = text(out);
    assert_eq!(
        report.passed,
        ["app.crag \"sums\"", "geo/shape.crag \"area multiplies\""],
        "{out}"
    );
    assert_eq!(report.failed.len(), 1, "{out}");
    let (name, trap) = &report.failed[0];
    assert_eq!(name, "app.crag \"reads past the end\"");
    assert_eq!(
        trap,
        "trap: index out of range\n  --> app.crag:14:11\n   |\n14 |   let y = xs[5]\n   |           ^\n  in test \"reads past the end\"\n"
    );
    assert!(out.ends_with("\n2 passed, 1 failed\n"), "{out}");
    assert!(!report.success());
    // A filter picks tests by their labels.
    let report = crag_test(&root, Some("area"), &mut Vec::new());
    assert_eq!(report.passed, ["geo/shape.crag \"area multiplies\""]);
    assert!(report.success());
}

#[test]
fn errors_are_shown_against_the_source() {
    let root = project(
        "errors",
        &[
            ("package.crag", MANIFEST),
            ("app.crag", "fn main() {\n  let n = missing + 1\n}\n"),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    assert!(
        out.starts_with(
            "error: `missing` is not defined\n --> app.crag:2:11\n  |\n2 |   let n = missing + 1\n  |           ^^^^^^^\n"
        ),
        "{out}"
    );
    assert!(
        out.ends_with("error\n") || out.ends_with("errors\n"),
        "{out}"
    );
}

#[test]
fn a_trap_in_main_is_reported_with_its_stack() {
    let root = project(
        "trap",
        &[
            ("package.crag", MANIFEST),
            (
                "app.crag",
                "fn down(n: Int) -> Int {\n  if n == 0 { 1 / n } else { down(n - 1) + 1 }\n}\n\nfn main() {\n  let r = down(3)\n}\n",
            ),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), EXIT_TRAP);
    assert_eq!(
        text(out),
        "trap: division by zero\n --> app.crag:2:15\n  |\n2 |   if n == 0 { 1 / n } else { down(n - 1) + 1 }\n  |               ^\n  in down, 4 frames\n  in main\n"
    );
}

#[test]
fn the_command_runs_the_project_in_the_current_directory() {
    let root = demo("command");
    let crag = env!("CARGO_BIN_EXE_crag");
    let status = Command::new(crag)
        .arg("run")
        .current_dir(&root)
        .status()
        .unwrap();
    assert_eq!(status.code(), Some(12));
    let output = Command::new(crag)
        .args(["test", "sums"])
        .current_dir(&root)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0));
    assert!(text(output.stdout).contains("test app.crag \"sums\" ... ok"));
    let usage = Command::new(crag).arg("build").status().unwrap();
    assert_eq!(usage.code(), Some(2));
}
