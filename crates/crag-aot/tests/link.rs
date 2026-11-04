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

//! Release objects linked with the runtime archive into executables that
//! run as `crag run` runs the program, the same for the same inputs.

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use crag_aot::{MAIN, Target, emit_object, link, receiving_archive, runtime_archive};
use crag_driver::{Project, check, main_instance};

/// How long a build of the archive, or a run of an executable, may take.
const BUILD_LIMIT: Duration = Duration::from_secs(600);
const RUN_LIMIT: Duration = Duration::from_secs(30);

const APP: &str = r#"import std.io
import std.env
import std.task

type Point(x: Int, y: Int)

fn area(p: Point) -> Int {
  p.x * p.y
}

fn total(ps: List[Point]) -> Int {
  var t = 0
  for p in ps {
    t = t + area(p)
  }
  t
}

fn main() -> ExitCode {
  printLine("Hello from a release build")
  printLine("{args()}")
  printLine("{total([Point(x: 3, y: 4), Point(x: 1, y: 2)])}")
  all(body: { g ->
    start(g, { -> printLine("from a task") })
  })
  ExitCode(code: 3)
}
"#;

const TRAPS: &str = r#"import std.io

fn share(a: Int, b: Int) -> Int {
  a / b
}

fn main() {
  printLine("before")
  printLine("{share(7, 0)}")
}
"#;

/// The runtime archive, built once for all the tests of this file.
fn archive() -> PathBuf {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT
        .get_or_init(|| build_archive("crag-rt", runtime_archive))
        .clone()
}

/// The runtime archive with the receiver of code, built once.
fn receiving() -> PathBuf {
    static BUILT: OnceLock<PathBuf> = OnceLock::new();
    BUILT
        .get_or_init(|| build_archive("crag-rt-receive", receiving_archive))
        .clone()
}

/// Builds the archive of a package for the host's target, by itself, so
/// that no other package's features join its own.
fn build_archive(
    package: &str,
    find: fn(Target) -> Result<PathBuf, crag_aot::LinkError>,
) -> PathBuf {
    let target = Target::host();
    let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let mut cargo = Command::new(env!("CARGO"));
    cargo
        .args(["build", "--quiet", "-p", package, "--release", "--target"])
        .arg(target.triple())
        .current_dir(workspace);
    let out = run(cargo, BUILD_LIMIT);
    assert!(
        out.status.success(),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    find(target).unwrap()
}

/// Runs a command to its end within `limit`, killing it after.
fn run(mut command: Command, limit: Duration) -> Output {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let pipe = |mut r: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = r.read_to_end(&mut bytes);
            bytes
        })
    };
    let stdout = pipe(Box::new(child.stdout.take().unwrap()));
    let stderr = pipe(Box::new(child.stderr.take().unwrap()));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            panic!("{command:?} ran longer than {limit:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    Output {
        status,
        stdout: stdout.join().unwrap(),
        stderr: stderr.join().unwrap(),
    }
}

/// A directory of its own for a test, empty.
fn scratch(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crag-link-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// The executable of a project of one module, `demo.app`, in `dir`.
fn build(dir: &Path, source: &str, out: &str) -> PathBuf {
    let root = dir.join("project");
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    fs::write(root.join("app.crag"), source).unwrap();
    let project = Project::load(&root).unwrap();
    let errors: Vec<String> = check(&project).into_iter().map(|d| d.message).collect();
    assert!(errors.is_empty(), "{errors:?}");
    let main = main_instance(&project).unwrap();
    let emitted = emit_object(&project.db, project.program, &[(main, MAIN)]).unwrap();
    let object = dir.join(format!("{out}.o"));
    fs::write(&object, &emitted.bytes).unwrap();
    let exe = dir.join(out);
    let archive = match emitted.receives {
        true => receiving(),
        false => archive(),
    };
    link(&[object], &[archive], Target::host(), &exe).unwrap();
    exe
}

#[test]
fn a_release_executable_runs_the_program() {
    let dir = scratch("runs");
    let exe = build(&dir, APP, "app");
    let mut command = Command::new(&exe);
    command.args(["a", "b c"]);
    let out = run(command, RUN_LIMIT);
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "Hello from a release build\n[\"a\", \"b c\"]\n14\nfrom a task\n"
    );
    assert_eq!(String::from_utf8_lossy(&out.stderr), "");
    // The `ExitCode` main returns.
    assert_eq!(out.status.code(), Some(3));
}

#[test]
fn a_trap_ends_the_executable_with_its_report() {
    let dir = scratch("traps");
    let exe = build(&dir, TRAPS, "traps");
    let out = run(Command::new(&exe), RUN_LIMIT);
    let _ = fs::remove_dir_all(&dir);
    let report = String::from_utf8_lossy(&out.stderr);
    assert_eq!(String::from_utf8_lossy(&out.stdout), "before\n", "{report}");
    assert!(report.starts_with("trap: division by zero\n"), "{report}");
    assert!(report.contains(" --> demo.app:4:"), "{report}");
    assert!(report.contains("  in share"), "{report}");
    assert_eq!(out.status.code(), Some(70));
}

#[test]
fn the_same_inputs_link_to_the_same_executable() {
    let (one, two) = (scratch("same-1"), scratch("same-2"));
    let a = fs::read(build(&one, APP, "app")).unwrap();
    let b = fs::read(build(&two, APP, "app")).unwrap();
    let _ = fs::remove_dir_all(&one);
    let _ = fs::remove_dir_all(&two);
    assert!(a == b, "two links of the same inputs differ");
}

const RECEIVES: &str = r#"import std.io
import std.transport

let table = [10, 20, 30]

pub fn lookup(i: Int) -> Int { table[i] }

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
    e: BudgetLimit -> "budget limit: {e.budget.name}"
  }
}

fn main() {
  let k = 7
  printLine(report(run({ x -> x * k + lookup(1) }, 6, Policy())))
  printLine(report(run({ n -> spin(n) }, 1000000000, Policy(steps: 100000))))
  printLine(report(run({ n -> spin(n) }, 10, Policy(steps: 3))))
}
"#;

#[test]
fn a_release_executable_runs_received_code_under_limits() {
    // Implementation Plan §11.10.9: the executable carries the receiver,
    // which checks and compiles the code again inside it, against the
    // program's types and cells, and runs it under the policy's limits.
    let dir = scratch("receives");
    let exe = build(&dir, RECEIVES, "receives");
    let out = run(Command::new(&exe), RUN_LIMIT);
    let _ = fs::remove_dir_all(&dir);
    assert_eq!(
        String::from_utf8_lossy(&out.stdout),
        "ran 62\nstep limit\nstep limit\n",
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert_eq!(out.status.code(), Some(0));
}
