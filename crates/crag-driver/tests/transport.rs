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

//! Running received code (Implementation Plan §11.10.9, Specification
//! §18.7): `std.transport.run` checks and compiles an `Expr`'s tree again
//! and runs it under the policy's limits, next to the program's data.

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crag_driver::{EXIT_TRAP, Project, Repl, Scratch};
use crag_session::ImageCommand;

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\nmain demo.app\n";

/// What `crag run` prints for the project's `app` module, and its exit
/// status. The program runs in a process of its own, killed after a
/// minute.
fn run(name: &str, app: &str) -> (i32, String) {
    run_with(name, app, &[])
}

/// What `run` gives, with these variables set for the program.
fn run_with(name: &str, app: &str, vars: &[(&str, &str)]) -> (i32, String) {
    let root = std::env::temp_dir().join(format!("crag-transport-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(root.join("package.crag"), MANIFEST).unwrap();
    fs::write(root.join("app.crag"), app).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
        .arg("run")
        .envs(vars.iter().copied())
        .current_dir(&root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    while child.try_wait().unwrap().is_none() {
        if Instant::now() > deadline {
            let _ = child.kill();
            let _ = child.wait();
            panic!("{name} did not finish within a minute");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().unwrap();
    let _ = fs::remove_dir_all(PathBuf::from(&root));
    let text = String::from_utf8_lossy(&output.stdout).into_owned()
        + &String::from_utf8_lossy(&output.stderr);
    (output.status.code().unwrap_or(-1), text)
}

/// The program's side: what each result of `run` prints as.
const REPORT: &str = r#"import std.io
import std.transport

fn report(r: Int | Unresolved | IllTyped | Impure | StepLimit | MemoryLimit) -> Str {
  case r {
    n: Int -> "ran {n}"
    e: Unresolved -> "unresolved: {e.message}"
    e: IllTyped -> "ill-typed: {e.message}"
    e: Impure -> "impure: {e.message}"
    StepLimit -> "step limit"
    MemoryLimit -> "memory limit"
  }
}

fn go(e: Expr[((Int) -> Int is Pure)], input: Int, policy: Policy) -> () {
  printLine(report(run(e, input, policy)))
}

pub fn triple(n: Int) -> Int { n * 3 }

let table = [10, 20, 30]

pub fn lookup(i: Int) -> Int { table[i] }

pub fn spin(n: Int) -> Int {
  var total = 0
  for i in 0..n {
    total = total + i % 7
  }
  total
}

pub fn grow(n: Int) -> Int {
  var xs: List[Int] = []
  for i in 0..n {
    xs = xs.append(i)
  }
  xs.count()
}

fn twice(n: Int) -> Int { n + n }

fn plus(n: Int) -> Int { n + 1 }
"#;

#[test]
fn received_code_runs_next_to_the_programs_data() {
    // The closure's captures, the program's `pub` functions, a helper it
    // bundles and a module value they read all reach the code the program
    // compiled again; the result comes back as it is. Trees that bundle
    // different helpers each run their own.
    let app = format!(
        "{REPORT}\nfn main() -> () {{\n  let k = 7\n  \
         go({{ x -> x * k }}, 6, Policy())\n  \
         go({{ x -> triple(x) + twice(x) }}, 2, Policy())\n  \
         go({{ x -> lookup(x) }}, 2, Policy(accept: Signature))\n  \
         go(triple, 5, Policy())\n  \
         go({{ x -> plus(x) }}, 2, Policy())\n}}\n"
    );
    let (status, out) = run("runs", &app);
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "ran 42\nran 10\nran 30\nran 15\nran 3\n");
}

#[test]
fn received_code_stops_at_the_policys_limits() {
    // Running out of steps or memory is a value (§18.7), whether the run
    // or the receiving took them, and the program goes on.
    let app = format!(
        "{REPORT}\nfn main() -> () {{\n  \
         go({{ n -> spin(n) }}, 1000000000, Policy(steps: 100000))\n  \
         go({{ n -> grow(n) }}, 10000000, Policy(memory: 1000000))\n  \
         go({{ n -> spin(n) }}, 10, Policy(steps: 3))\n  \
         go({{ n -> spin(n) }}, 10, Policy(memory: 10))\n  \
         go({{ n -> spin(n) }}, 10, Policy())\n}}\n"
    );
    let (status, out) = run("limits", &app);
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "step limit\nmemory limit\nstep limit\nmemory limit\nran 27\n"
    );
}

#[test]
fn values_pass_in_and_out_as_they_are() {
    // Records, lists and strings go in and come back without encoding,
    // an input need not be Solid, and the same code runs again from the
    // store.
    let app = r#"import std.io
import std.transport

pub type Pair(a: Int, b: Int)

pub type Work(pairs: List[Pair], label: Str)

fn products(w: Work) -> () {
  case run({ v -> v.pairs.map({ p -> p.a * p.b }) }, w, Policy()) {
    xs: List[Int] -> printLine("{w.label}: {xs.count()} products, the last {xs[xs.count() - 1]}")
    _ -> printLine("refused")
  }
}

fn main() -> () {
  let w = Work(pairs: [Pair(a: 1, b: 2), Pair(a: 3, b: 4)], label: "two")
  products(w)
  products(Work(..w, label: "again"))
  case run({ p -> "a={p.a}, b={p.b}" }, Pair(a: 5, b: 6), Policy()) {
    s: Str -> printLine(s)
    _ -> printLine("refused")
  }
}
"#;
    let (status, out) = run("values", app);
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "two: 2 products, the last 12\nagain: 2 products, the last 12\na=5, b=6\n"
    );
}

#[test]
fn received_code_runs_again_once_unloaded() {
    // With a bound of one byte, each tree first unloads what the store may
    // (Implementation Plan §11.10.9): later rounds compile the code
    // again. A function the result holds, and the code of a module value,
    // stay loaded and still run.
    let app = format!(
        "{REPORT}\ntype Add = ((Int) -> Int is Pure)\n\nfn adder(n: Int) -> Add | Unresolved | IllTyped | Impure | StepLimit | MemoryLimit {{\n  \
         let e: Expr[((Int) -> ((Int) -> Int is Pure) is Pure)] = {{ k -> {{ m -> m + k + triple(1) }} }}\n  run(e, n, Policy())\n}}\n\
         fn main() -> () {{\n  \
         let f = case adder(4) {{\n    g: Add -> g\n    _ -> {{ m: Int -> 0 }}\n  }}\n  \
         for round in 0..2 {{\n    \
         go({{ x -> x * 7 }}, 6, Policy())\n    \
         go({{ x -> triple(x) + twice(x) }}, 2, Policy())\n    \
         go({{ x -> lookup(x) }}, 2, Policy())\n    \
         go({{ x -> spin(x) }}, 10, Policy())\n    \
         printLine(\"f {{f(round)}}\")\n  }}\n}}\n"
    );
    let (status, out) = run_with("unload", &app, &[("CRAG_RECEIVED_CODE", "1")]);
    assert_eq!(status, 0, "{out}");
    let round = "ran 42\nran 10\nran 30\nran 27\n";
    assert_eq!(out, format!("{round}f 7\n{round}f 8\n{round}f 9\n"));
}

#[test]
fn a_trap_in_received_code_is_the_callers() {
    // A trap in the body behaves as anywhere else (§18.7).
    let app = format!("{REPORT}\nfn main() -> () {{\n  go({{ n -> 10 / n }}, 0, Policy())\n}}\n");
    let (status, out) = run("trap", &app);
    assert_eq!(status, i32::from(EXIT_TRAP), "{out}");
    assert!(out.contains("divi"), "{out}");
}

#[test]
fn the_repl_runs_received_code_in_its_image() {
    // The host sends the scratch image the program's bundle, from which
    // the image's receiver checks and compiles the code itself, again
    // whenever the session changed.
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    let mut r = Repl::new(Project::bare(), scratch);
    let mut eval = |text: &str| match r.eval_input(text) {
        Ok(output) => output.render(),
        Err(errors) => errors,
    };
    assert_eq!(eval("import std.transport"), "");
    eval("pub fn triple(n: Int) -> Int { n * 3 }");
    assert_eq!(eval("run({ x -> triple(x) + 1 }, 4, Policy())"), "13\n");
    eval("pub fn half(n: Int) -> Int { n / 2 }");
    assert_eq!(eval("run({ x -> half(x) }, 9, Policy())"), "4\n");
    assert_eq!(
        eval("run({ x -> half(x) }, 9, Policy(steps: 2))"),
        "StepLimit()\n"
    );
}
