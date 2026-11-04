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

mod common;

use std::fs;
use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use crag_driver::EXIT_TRAP;

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\nmain demo.app\n";

/// What `crag run` prints for the project's `app` module, and its exit
/// status. The program runs in a process of its own, killed after a
/// minute.
fn run(name: &str, app: &str) -> (i32, String) {
    run_with(name, app, &[])
}

/// What `run` gives, with these variables set for the program.
fn run_with(name: &str, app: &str, vars: &[(&str, &str)]) -> (i32, String) {
    run_args(name, app, &[], vars)
}

/// What `run` gives, with these arguments to `crag run` and these
/// variables set.
fn run_args(name: &str, app: &str, args: &[&str], vars: &[(&str, &str)]) -> (i32, String) {
    let root = common::project(
        &format!("transport-{name}"),
        &[("package.crag", MANIFEST), ("app.crag", app)],
    );
    let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
        .arg("run")
        .args(args)
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

fn report(r: Int | Unresolved | IllTyped | Impure | StepLimit | MemoryLimit | Unbudgeted | BudgetLimit) -> Str {
  case r {
    n: Int -> "ran {n}"
    e: Unresolved -> "unresolved: {e.message}"
    e: IllTyped -> "ill-typed: {e.message}"
    e: Impure -> "impure: {e.message}"
    StepLimit -> "step limit"
    MemoryLimit -> "memory limit"
    e: Unbudgeted -> "unbudgeted: {e.message}"
    e: BudgetLimit -> "budget limit: {e.budget.name}"
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
        "{REPORT}\ntype Add = ((Int) -> Int is Pure)\n\nfn adder(n: Int) -> Add | Unresolved | IllTyped | Impure | StepLimit | MemoryLimit | Unbudgeted | BudgetLimit {{\n  \
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
    let mut r = common::repl();
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

/// A budget document of two senders: `acme` short of steps and runs,
/// `globex` of memory.
const BUDGETS: &str = r#"{
  "name": "partners",
  "date": "2026-11-04",
  "issuer": "ops@example.org",
  "budgets": [
    { "name": "acme", "steps": 200000, "runs": 3 },
    { "name": "globex", "memory": 1000000 }
  ]
}
"#;

/// Runs `crag lmt new` on the document in a folder of its own, which then
/// holds the document, its salt and a token file for each budget.
fn budget_dir(name: &str, document: &str) -> PathBuf {
    let dir = common::project(&format!("lmt-{name}"), &[("partners.json", document)]);
    let output = Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(["lmt", "new", "partners.json"])
        .current_dir(&dir)
        .output()
        .unwrap();
    let text = String::from_utf8_lossy(&output.stderr);
    assert!(output.status.success(), "{text}");
    assert!(text.contains("partners-acme.token"), "{text}");
    dir
}

/// What `run` gives with the budget directory in `CRAG_BUDGETS`.
fn run_budgeted(name: &str, app: &str, dir: &std::path::Path) -> (i32, String) {
    let dir = dir.to_string_lossy().into_owned();
    run_with(name, app, &[("CRAG_BUDGETS", dir.as_str())])
}

/// A program that sends code to itself over a connection, and what it
/// does with what arrives. `SEND` sends, `ARRIVED` takes the `bytes` of
/// one message.
const LOOPBACK: &str = r#"import std.io
import std.stream
import std.transport

type Code = Expr[((Int) -> Int is Pure)]

pub fn spin(n: Int) -> Int {
  var total = 0
  for i in 0..n {
    total = total + i % 7
  }
  total
}

fn report(r: Int | Unresolved | IllTyped | Impure | StepLimit | MemoryLimit | Unbudgeted | BudgetLimit) -> Str {
  case r {
    n: Int -> "ran {n}"
    e: Unresolved -> "unresolved: {e.message}"
    e: IllTyped -> "ill-typed: {e.message}"
    e: Impure -> "impure: {e.message}"
    StepLimit -> "step limit"
    MemoryLimit -> "memory limit"
    e: Unbudgeted -> "unbudgeted: {e.message}"
    e: BudgetLimit -> "budget limit: {e.budget.document}/{e.budget.name}"
  }
}

fn decoded(bytes: Bytes) -> Code | Str {
  case decode[Code](bytes, Policy()) {
    e: Code -> e
    e: Unbudgeted -> "unbudgeted: {e.message}"
    e: BudgetLimit -> "budget limit: {e.budget.name}"
    e: DecodeError -> "not code: {e.message}"
    _ -> "refused"
  }
}

fn send(to: Peer) -> () {
  SEND
}

fn arrived(bytes: Bytes) -> () {
  ARRIVED
}

fn main() -> () {
  case listen(0) {
    l: Listener -> case connect(l.port()) {
      c: Connection -> {
        send(peer(c))
        case l.accept() {
          s: Connection -> {
            let from = peer(s)
            for round in 1..ROUNDS {
              case from.read() {
                bytes: Bytes -> arrived(bytes)
                _ -> printLine("read failed")
              }
            }
          }
          _ -> printLine("accept failed")
        }
      }
      _ -> printLine("connect failed")
    }
    _ -> printLine("listen failed")
  }
}
"#;

/// The loopback program with these parts.
fn loopback(send: &str, arrived: &str, rounds: usize) -> String {
    LOOPBACK
        .replace("SEND", send)
        .replace("ARRIVED", arrived)
        .replace("ROUNDS", &rounds.to_string())
}

#[test]
fn crag_lmt_new_writes_a_salt_and_a_token_file_for_each_budget() {
    let dir = budget_dir("files", BUDGETS);
    let salt = fs::read_to_string(dir.join("partners.salt")).unwrap();
    assert_eq!(salt.trim().len(), 64);
    let acme = fs::read_to_string(dir.join("partners-acme.token")).unwrap();
    let globex = fs::read_to_string(dir.join("partners-globex.token")).unwrap();
    // A token file names its budget and carries its limits.
    assert!(acme.contains("\"budget\": \"acme\""), "{acme}");
    assert!(acme.contains("\"steps\": 200000"), "{acme}");
    assert!(
        globex.contains("\"issuer\": \"ops@example.org\""),
        "{globex}"
    );
    // Only their owner reads them.
    use std::os::unix::fs::PermissionsExt;
    for file in ["partners.salt", "partners-acme.token"] {
        let mode = fs::metadata(dir.join(file)).unwrap().permissions().mode();
        assert_eq!(mode & 0o077, 0, "{file}");
    }
    // A salt is never overwritten, which would change every token.
    let again = Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(["lmt", "new", "partners.json"])
        .current_dir(&dir)
        .output()
        .unwrap();
    assert!(!again.status.success());
    assert!(String::from_utf8_lossy(&again.stderr).contains("exists"));
    assert_eq!(fs::read_to_string(dir.join("partners.salt")).unwrap(), salt);
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn a_program_lists_and_manages_its_budgets() {
    // §18.7: the runtime reads the budget directory; `list` gives the
    // budgets it enforces and those it sends under, and both fit the
    // budget forms through their final functions.
    let dir = budget_dir("manage", BUDGETS);
    let app = r#"import std.io
import std.transport

fn describe[B: Metered](b: B) -> Str {
  let o = origin(b)
  "{o.document}/{o.name} by {o.issuer} of {o.date}: {limits(b)}, {usage(b)}"
}

fn main() -> () {
  let budgets = list()
  for b in budgets.receiving { printLine("enforce {describe(b)}") }
  for s in budgets.sending { printLine("send {describe(s)}") }
  let b = budgets.receiving[0]
  case renew(b) {
    e: RenewError -> printLine("renew failed: {e.message}")
    _ -> printLine("renewed")
  }
  reset(budgets.sending[1])
  printLine("{usage(b)}")
}
"#;
    let (status, out) = run_budgeted("manage", app, &dir);
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "enforce partners/acme by ops@example.org of 2026-11-04: \
         Limits(steps: 200000, memory: Empty, runs: 3), Usage(steps: 0, memory: 0, runs: 0)\n\
         enforce partners/globex by ops@example.org of 2026-11-04: \
         Limits(steps: Empty, memory: 1000000, runs: Empty), Usage(steps: 0, memory: 0, runs: 0)\n\
         send partners/acme by ops@example.org of 2026-11-04: \
         Limits(steps: 200000, memory: Empty, runs: 3), Usage(steps: Empty, memory: Empty, runs: 0)\n\
         send partners/globex by ops@example.org of 2026-11-04: \
         Limits(steps: Empty, memory: 1000000, runs: Empty), Usage(steps: Empty, memory: Empty, runs: 0)\n\
         renewed\n\
         Usage(steps: 0, memory: 0, runs: 0)\n"
    );
    // A process without a budget directory has none.
    let (status, out) = run(
        "no-budgets",
        "import std.io\nimport std.transport\n\
         fn main() -> () {\n  let b = list()\n  \
         printLine(\"{b.receiving.count()} {b.sending.count()}\")\n}\n",
    );
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "0 0\n");
    // A directory the runtime cannot read stops the program.
    let (status, out) = run_budgeted("bad-dir", "fn main() -> () {}\n", &dir.join("missing"));
    assert_ne!(status, 0, "{out}");
    assert!(out.contains("budget directory"), "{out}");
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn the_budget_directory_may_be_given_to_crag_run() {
    // The flag wins over the variable.
    let dir = budget_dir("flag", BUDGETS);
    let app = "import std.io\nimport std.transport\n\
               fn main() -> () {\n  let b = list()\n  \
               printLine(\"{b.receiving.count()} {b.sending.count()}\")\n}\n";
    let flag = dir.to_string_lossy().into_owned();
    let missing = dir.join("missing").to_string_lossy().into_owned();
    let (status, out) = run_args(
        "flag",
        app,
        &["--budgets", &flag],
        &[("CRAG_BUDGETS", &missing)],
    );
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "2 2\n");
    let (status, out) = run_args("flag-missing", app, &["--budgets", &missing], &[]);
    assert_ne!(status, 0, "{out}");
    assert!(out.contains("budget directory"), "{out}");
    let (status, out) = run_args("flag-bare", app, &["--budgets"], &[]);
    assert_ne!(status, 0, "{out}");
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn a_reset_gives_back_steps_and_runs_but_admits_no_replay() {
    let dir = budget_dir("reset", BUDGETS);
    let send = "let a = send(to, list().sending[0], { n: Int -> spin(n) })";
    let arrived = "case decoded(bytes) {\n    \
                   e: Code -> {\n      \
                   let acme = list().receiving[0]\n      \
                   printLine(report(run(e, 1000000000, Policy())))\n      \
                   printLine(report(run(e, 6, Policy())))\n      \
                   reset(acme)\n      \
                   printLine(\"{usage(acme)}\")\n      \
                   printLine(report(run(e, 6, Policy())))\n    }\n    \
                   why: Str -> printLine(why)\n  }\n  \
                   case decoded(bytes) {\n    \
                   e: Code -> printLine(\"replayed\")\n    \
                   why: Str -> printLine(why)\n  }";
    let (status, out) = run_budgeted("reset", &loopback(send, arrived, 1), &dir);
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "budget limit: partners/acme\n\
         budget limit: partners/acme\n\
         Usage(steps: 0, memory: 0, runs: 0)\n\
         ran 21\n\
         unbudgeted: budget `acme` admitted this stamp's number already\n"
    );
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn code_travels_under_its_senders_budget() {
    // §18.7: the code arrives with its captures, runs under the policy and
    // its budget, which keeps the steps it took, and is called as it is.
    // Each tree takes one of the budget's runs.
    let dir = budget_dir("travel", BUDGETS);
    let send = "let acme = list().sending[0]\n  let k = 7\n  \
                let a = send(to, acme, { x: Int -> x * k })\n  \
                let b = send(to, acme, { n: Int -> spin(n) })\n  \
                let c = send(to, acme, { x: Int -> x + 1 })\n  \
                let d = send(to, acme, { x: Int -> x + 2 })";
    let arrived = "case decoded(bytes) {\n    \
                   e: Code -> {\n      \
                   printLine(report(run(e, 6, Policy())))\n      \
                   printLine(report(run(e, 1000000000, Policy())))\n      \
                   printLine(\"called {e(5)}\")\n    }\n    \
                   why: Str -> printLine(why)\n  }\n  \
                   let acme = list().receiving[0]\n  printLine(\"{usage(acme)}\")";
    let (status, out) = run_budgeted("travel", &loopback(send, arrived, 4), &dir);
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "ran 42\nran 7000000000\ncalled 35\n\
         Usage(steps: 0, memory: 0, runs: 1)\n\
         ran 21\nbudget limit: partners/acme\ncalled 15\n\
         Usage(steps: 200000, memory: 0, runs: 2)\n\
         budget limit: partners/acme\nbudget limit: partners/acme\ncalled 6\n\
         Usage(steps: 200000, memory: 0, runs: 3)\n\
         budget limit: acme\n\
         Usage(steps: 200000, memory: 0, runs: 3)\n"
            .replace("Usage(steps: 0, memory: 0, runs: 1)", &first_usage(&out))
    );
    // Receiving and running the first tree took steps.
    assert!(!first_usage(&out).starts_with("Usage(steps: 0,"), "{out}");
    let _ = fs::remove_dir_all(dir);
}

/// The usage line after the first tree, whose steps depend on how much
/// receiving took.
fn first_usage(out: &str) -> String {
    out.lines()
        .find(|l| l.starts_with("Usage") && l.ends_with("runs: 1)"))
        .unwrap_or("")
        .to_string()
}

#[test]
fn code_without_a_valid_stamp_is_unbudgeted() {
    let dir = budget_dir("stamps", BUDGETS);
    // Unstamped code, a replay of stamped bytes, and bytes that are not
    // code.
    let send = "let acme = list().sending[0]\n  \
                let a = send(to, { x: Int -> x * 2 })\n  \
                let b = send(to, acme, { x: Int -> x * 3 })";
    let arrived = "case decoded(bytes) {\n    \
                   e: Code -> printLine(report(run(e, 2, Policy())))\n    \
                   why: Str -> printLine(why)\n  }\n  \
                   case decoded(bytes) {\n    \
                   e: Code -> printLine(\"again {report(run(e, 2, Policy()))}\")\n    \
                   why: Str -> printLine(\"again {why}\")\n  }\n  \
                   case decoded(b\"nonsense\") {\n    \
                   e: Code -> printLine(\"decoded nonsense\")\n    \
                   why: Str -> printLine(why)\n  }";
    let (status, out) = run_budgeted("stamps", &loopback(send, arrived, 2), &dir);
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "unbudgeted: the code carries no budget's stamp\n\
         again unbudgeted: the code carries no budget's stamp\n\
         not code: the bytes lack the magic of code\n\
         ran 6\n\
         again unbudgeted: budget `acme` admitted this stamp's number already\n\
         not code: the bytes lack the magic of code\n"
    );
    // A token of another salt does not verify: the sender sends under
    // its own directory's token, the receiver enforces this one's.
    let other = budget_dir("other", BUDGETS);
    fs::copy(
        other.join("partners-acme.token"),
        dir.join("partners-acme.token"),
    )
    .unwrap();
    let send = "let a = send(to, list().sending[0], { x: Int -> x * 3 })";
    let arrived = "case decoded(bytes) {\n    \
                   e: Code -> printLine(report(run(e, 2, Policy())))\n    \
                   why: Str -> printLine(why)\n  }";
    let (status, out) = run_budgeted("forged", &loopback(send, arrived, 1), &dir);
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "unbudgeted: the stamp of budget `acme` is not valid\n");
    // A process that enforces no budget ignores stamps: here it holds
    // only the token.
    for file in ["partners.json", "partners.salt", "partners-globex.token"] {
        fs::remove_file(dir.join(file)).unwrap();
    }
    let (status, out) = run_budgeted("ignored", &loopback(send, arrived, 1), &dir);
    assert_eq!(status, 0, "{out}");
    assert_eq!(out, "ran 6\n");
    let _ = fs::remove_dir_all(dir);
    let _ = fs::remove_dir_all(other);
}

#[test]
fn a_budget_holds_the_memory_of_its_runs_until_they_end() {
    // `globex` has memory for one run at a time of the policy's default,
    // so a run capped by it stops at the budget, and its memory goes back.
    let dir = budget_dir("memory", BUDGETS);
    let send = "let globex = list().sending[1]\n  \
                let a = send(to, globex, { n: Int -> grow(n) })";
    let arrived = "case decoded(bytes) {\n    \
                   e: Code -> {\n      \
                   printLine(report(run(e, 10000000, Policy())))\n      \
                   printLine(report(run(e, 10, Policy())))\n      \
                   printLine(report(run(e, 10000000, Policy(memory: 500000))))\n    }\n    \
                   why: Str -> printLine(why)\n  }\n  \
                   printLine(\"{usage(list().receiving[1])}\")";
    let app = loopback(send, arrived, 1).replace(
        "pub fn spin",
        "pub fn grow(n: Int) -> Int {\n  var xs: List[Int] = []\n  for i in 1..n {\n    \
         xs = xs.append(i)\n  }\n  xs.count()\n}\n\npub fn spin",
    );
    let (status, out) = run_budgeted("memory", &app, &dir);
    assert_eq!(status, 0, "{out}");
    let lines: Vec<&str> = out.lines().collect();
    assert_eq!(
        lines[..3],
        ["budget limit: partners/globex", "ran 10", "memory limit"],
        "{out}"
    );
    assert!(lines[3].starts_with("Usage(steps: ") && lines[3].ends_with("memory: 0, runs: 1)"));
    let _ = fs::remove_dir_all(dir);
}

#[test]
fn code_whose_captures_cannot_travel_is_not_sent() {
    // A function value has no encoding, so code that captures one stays.
    let send = "let f: ((Int) -> Int is Pure) = { y: Int -> y + 1 }\n  \
                case send(to, { x: Int -> f(x) }) {\n    \
                e: Unsendable -> printLine(\"unsendable: {e.message}\")\n    \
                _ -> printLine(\"sent\")\n  }\n  \
                let a = send(to, { x: Int -> x })";
    let arrived = "case decoded(bytes) {\n    \
                   e: Code -> printLine(report(run(e, 4, Policy())))\n    \
                   why: Str -> printLine(why)\n  }";
    let (status, out) = run("unsendable", &loopback(send, arrived, 1));
    assert_eq!(status, 0, "{out}");
    assert_eq!(
        out,
        "unsendable: its captures hold a function value, which cannot be sent\nran 4\n"
    );
}
