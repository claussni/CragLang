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

//! `crag run`, `crag test` and `crag fmt` on small multi-module projects on
//! disk.

use std::fs;
use std::path::PathBuf;
use std::process::Command;

use crag_driver::{EXIT_TRAP, crag_fmt, crag_run, crag_test};

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

pub fn addUp(xs: List[Int]) -> Int {
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

let offset = addUp([1, 2, 3])

fn main() -> ExitCode {
  let p = Point(x: 2, y: 3)
  ExitCode(code: area(p) + offset)
}

test "sums" {
  if addUp([1, 2]) != 3 { ??? }
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
        "trap: index out of range\n  --> app.crag:16:11\n   |\n16 |   let y = xs[5]\n   |           ^\n  in test \"reads past the end\"\n"
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
fn a_more_specific_overload_wins_unless_the_function_is_final() {
    // §5.6.1: the app's `label(Int)` outranks the library's generic one,
    // but no overload may outrank the final `verify`, unless renamed.
    let lib = "pub fn label[T](x: T) -> Int { 1 }\npub final fn verify[T](x: T) -> Int { 2 }\n";
    let app = |import: &str| {
        format!(
            "{import}\nfn label(x: Int) -> Int {{ 10 }}\nfn verify(x: Int) -> Int {{ 20 }}\n\
             fn main() -> ExitCode {{\n  ExitCode(code: label(0) + verify(0))\n}}\n"
        )
    };
    let root = project(
        "final",
        &[
            ("package.crag", MANIFEST),
            ("lib.crag", lib),
            ("app.crag", &app("import demo.lib")),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    assert!(
        out.contains(
            "error: `verify(Int)` of `demo.app` is more specific than the final `verify(T)` of \
             `demo.lib`, which no overload may outrank; import one of them selectively or rename \
             one with `as`\n --> app.crag:3:1"
        ),
        "{out}"
    );
    let root = project(
        "final-renamed",
        &[
            ("package.crag", MANIFEST),
            ("lib.crag", lib),
            ("app.crag", &app("import demo.lib.{label, verify as vet}")),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 30, "{}", text(out));
}

#[test]
fn printing_and_transforms_that_print_are_not_pure() {
    // §3.14: the runtime functions of `std.io` do `io`, and a transform
    // runs where the record is built (§6.7).
    let app = "import std.io\n\
               type Shape(size: Int)\n\
               fn shout(n: Int) -> Int is Pure {\n  printLine(\"x\")\n  n\n}\n\
               fn grow(s: Shape) -> Shape is Pure {\n  Shape(..s, size: { n ->\n    printLine(\"y\")\n    n\n  })\n}\n\
               fn main() {}\n";
    let root = project("pure", &[("package.crag", MANIFEST), ("app.crag", app)]);
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    let wrong = "error: this has the effect `io`, which an `is Pure` function does not allow";
    assert_eq!(out.matches(wrong).count(), 2, "{out}");
    assert!(out.contains(" --> app.crag:4:3"), "{out}");
    assert!(out.contains(" --> app.crag:8:3"), "{out}");
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
fn a_constant_that_fails_at_compile_time_is_an_error() {
    let root = project(
        "constant",
        &[
            ("package.crag", MANIFEST),
            (
                "app.crag",
                "fn down(n: Int) -> Int {\n  if n == 0 { 1 / n } else { down(n - 1) }\n}\n\nlet ratio = down(3)\n\nfn main() {\n  let r = ratio\n}\n",
            ),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    assert!(
        out.starts_with(
            "error: `ratio` cannot be computed at compile time: it traps with division by zero in down\n --> app.crag:5:1\n  |\n5 | let ratio = down(3)\n  | ^^^^^^^^^^^^^^^^^^^\n"
        ),
        "{out}"
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

#[test]
fn closures_run_and_trap_where_they_are_written() {
    let app = r#"fn apply(f: (Int) -> Int, x: Int) -> Int {
  f(x)
}

fn again[T](f: (T) -> T, x: T) -> T {
  f(f(x))
}

fn main() -> ExitCode {
  let k = 4
  ExitCode(code: apply({ n -> n * k }, 3) + again({ n -> n + 1 }, 0))
}

test "overflows in a closure" {
  let big = 4611686018427387904
  let y = apply({ n -> n * big }, 2)
}
"#;
    let root = project("closures", &[("package.crag", MANIFEST), ("app.crag", app)]);
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 14, "{}", text(out));
    let mut out = Vec::new();
    let report = crag_test(&root, None, &mut out);
    let out = text(out);
    assert_eq!(report.failed.len(), 1, "{out}");
    // `apply` calls the closure in tail position, so its frame is gone.
    assert_eq!(
        report.failed[0].1,
        "trap: arithmetic overflow\n  --> app.crag:16:24\n   |\n16 |   let y = apply({ n -> n * big }, 2)\n   |                        ^\n  in a closure in test \"overflows in a closure\"\n  in test \"overflows in a closure\"\n"
    );
}

#[test]
fn embeds_give_the_files_they_name() {
    let shape = r#"embed greeting: Str from "../res/greeting.txt"
embed raw: Bytes from "../res/raw.bin"
embed short: Str from "./../res/short.txt"
// The module's own `data.txt`, not the one beside `app.crag`.
embed data: Str from "data.txt"

pub fn score() -> Int {
  var n = 0
  if greeting == "Hello from a file of the package\n" { n = n + 1 }
  if raw == b"\x00\xff\x01" { n = n + 2 }
  if short == "hi" and data == "geo" { n = n + 4 }
  n
}
"#;
    let app = r#"import demo.geo.shape

embed motto: Str from "res/greeting.txt"
embed data: Str from "data.txt"

let twice = "{motto}{motto}"

fn main() -> ExitCode {
  var n = score()
  if twice == "Hello from a file of the package\nHello from a file of the package\n" and data == "app" {
    n = n + 8
  }
  ExitCode(code: n)
}
"#;
    let root = project(
        "embed",
        &[
            ("package.crag", MANIFEST),
            ("geo/shape.crag", shape),
            ("app.crag", app),
            ("res/greeting.txt", "Hello from a file of the package\n"),
            ("res/short.txt", "hi"),
            ("geo/data.txt", "geo"),
            ("data.txt", "app"),
        ],
    );
    fs::write(root.join("res/raw.bin"), [0u8, 0xff, 1]).unwrap();
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 15, "{}", text(out));
}

#[test]
fn an_embed_that_cannot_be_read_is_an_error_at_its_source() {
    let app = r#"embed a from "missing.txt"
embed b from "../outside.txt"
embed c from "/etc/hostname"
embed d: Str from "bad.bin"
embed e: Int from "bad.bin"
embed f from "{1}.txt"
embed g from "link.txt"

fn main() {}
"#;
    let root = project(
        "embed-errors",
        &[("package.crag", MANIFEST), ("app.crag", app)],
    );
    fs::write(root.join("bad.bin"), [b'o', b'k', 0xc3]).unwrap();
    let outside = root.with_extension("outside");
    fs::write(&outside, "secret").unwrap();
    #[cfg(unix)]
    std::os::unix::fs::symlink(&outside, root.join("link.txt")).unwrap();
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    let messages: Vec<&str> = out
        .lines()
        .filter_map(|l| l.strip_prefix("error: "))
        .collect();
    assert_eq!(
        messages,
        [
            "cannot read `missing.txt`: No such file or directory (os error 2)",
            "`../outside.txt` is outside the package",
            "`/etc/hostname` is absolute; an `embed` names a file relative to its module",
            "an `embed` of `Str` needs UTF-8, which the resource is not at byte 2",
            "an `embed` of `Int` needs an `on Embed` handler, which `Int` does not declare; an `embed` of `Bytes` or `Str` needs none",
            "the source of an `embed` is a string literal, never computed",
            "`link.txt` is outside the package",
        ][..messages.len().min(7)],
        "{out}"
    );
    assert_eq!(messages.len(), 7, "{out}");
    assert!(
        out.contains(" --> app.crag:4:19\n  |\n4 | embed d: Str from \"bad.bin\"\n  |                   ^^^^^^^^^\n"),
        "{out}"
    );
}

#[test]
fn embed_handlers_make_values_of_their_types() {
    let app = r#"pub distinct type Level(n: Int)
  on Embed parseLevel

opaque type Size(n: Int)
  on Embed measure

fn parseLevel(text: Str) -> Level | EmbedError {
  case text {
    "low\n" -> Level(n: 1)
    "high\n" -> Level(n: 3)
    _ -> EmbedError(message: "expected low or high", line: 1, column: 1)
  }
}

fn measure(data: Bytes) -> Size {
  if data == b"\x00\x01" { Size(n: 20) } else { Size(n: 0) }
}

embed level: Level from "level.txt"
embed size: Size from "size.bin"

fn main() -> ExitCode {
  ExitCode(code: level.n + size.n)
}
"#;
    let root = project(
        "embed-handlers",
        &[
            ("package.crag", MANIFEST),
            ("app.crag", app),
            ("level.txt", "high\n"),
        ],
    );
    fs::write(root.join("size.bin"), [0u8, 1]).unwrap();
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 23, "{}", text(out));
    // An `EmbedError` is a compile error at the `embed`.
    fs::write(root.join("level.txt"), "medium\n").unwrap();
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    assert!(
        out.starts_with(
            "error: `level` cannot be embedded: expected low or high, at level.txt:1:1\n  --> app.crag:19:1\n"
        ),
        "{out}"
    );
    // A `Str` handler takes only UTF-8.
    fs::write(root.join("level.txt"), [0xffu8]).unwrap();
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    assert!(
        out.starts_with(
            "error: an `embed` of `Level` needs UTF-8, which the resource is not at byte 0\n"
        ),
        "{out}"
    );
}

#[test]
fn on_clauses_are_checked_against_their_kinds() {
    let app = r#"import cLib("m").{ now() -> Int }

type Plain(n: Int)
  on Embed parsePlain

distinct type NoKind(n: Int)
  on Int parseNoKind

// A form, but no lifecycle kind.
distinct type Fake[T]
  where HandlerForm[(Str) -> T]

distinct type Faked(n: Int)
  on Fake parseFaked

distinct type Misfit(n: Int)
  on Embed parseMisfit

distinct type Twice(n: Int)
  on Embed parseTwice
  on Embed parseTwice

distinct type Clock(n: Int)
  on Embed parseClock

distinct type Unknown(n: Int)

// A handler of a generic type fits each of its instances.
distinct type Narrow[T](n: Int)
  on Embed parseNarrow
distinct type Wide[T](n: Int)
  on Embed parseWide

fn parsePlain(text: Str) -> Plain { Plain(n: 1) }
fn parseNoKind(text: Str) -> NoKind { NoKind(n: 1) }
fn parseFaked(text: Str) -> Faked { Faked(n: 1) }
fn parseMisfit(n: Int) -> Misfit { Misfit(n: n) }
fn parseTwice(text: Str) -> Twice { Twice(n: 1) }
fn parseClock(text: Str) -> Clock { Clock(n: now()) }
fn parseNarrow(text: Str) -> Narrow[Int] { Narrow(n: 1) }

// Closures fit one member: the one their written types pick.
distinct type Unsure(n: Int)
  on Embed { text -> Unsure(n: 1) }
distinct type Wrong(n: Int)
  on Embed { n: Int -> Wrong(n: n) }
distinct type Loud(n: Int)
  on Embed { text: Str -> Loud(n: now()) }

// Only boxes have lives that end.
distinct type Token
  on Dispose closeToken
fn closeToken(t: Token) -> () {}

// A kind whose form a closure fits twice.
distinct type Both[T](..LifecycleHandler)
  where HandlerForm[((Int) -> T | Bool) | ((Int) -> T | EmbedError)]
distinct type Twofold(n: Int)
  on Both { n: Int -> Twofold(n: n) }
fn parseWide[T](text: Str) -> Wide[T] { Wide(n: 1) }

embed unknown: Unknown from "x.txt"

fn main() {}
"#;
    let root = project(
        "on-clauses",
        &[
            ("package.crag", MANIFEST),
            ("app.crag", app),
            ("x.txt", "x"),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_run(&root, &mut out), 1);
    let out = text(out);
    let messages: Vec<&str> = out
        .lines()
        .filter_map(|l| l.strip_prefix("error: "))
        .collect();
    assert_eq!(
        messages,
        [
            "a lifecycle handler needs a nominal type: declare it `distinct` or `opaque`",
            "this is no lifecycle kind: a type spreading `LifecycleHandler` with a handler form",
            "this is no lifecycle kind: a type spreading `LifecycleHandler` with a handler form",
            "no function `parseMisfit` fits the form of `Embed`: ((Bytes) -> EmbedError | Misfit) | ((Str) -> EmbedError | Misfit)",
            "the type already declares a handler of `Embed`",
            "a handler of `Embed` is Pure, and `parseClock` has effects",
            "no function `parseNarrow` fits the form of `Embed`: ((Bytes) -> EmbedError | Narrow[T]) | ((Str) -> EmbedError | Narrow[T])",
            "the type cannot be inferred here; write it",
            "this closure must fit exactly one member of the form of `Embed`: ((Bytes) -> EmbedError | Wrong) | ((Str) -> EmbedError | Wrong)",
            "expected (Str) -> EmbedError | Loud is Pure, found (Str) -> EmbedError | Loud",
            "only a record type has values whose lives end, so only it takes an `on Dispose` handler",
            "this closure must fit exactly one member of the form of `Both`: ((Int) -> EmbedError | Twofold) | ((Int) -> False | True | Twofold)",
            "an `embed` of `Unknown` needs an `on Embed` handler, which `Unknown` does not declare; an `embed` of `Bytes` or `Str` needs none",
        ],
        "{out}"
    );
}

#[test]
fn fmt_formats_every_module_in_place_and_check_lists_the_rest() {
    let root = project(
        "fmt",
        &[
            ("package.crag", MANIFEST),
            (
                "app.crag",
                "import demo.geo.shape\nimport std.time\nfn main( ) -> Int {\n  area(Point(x:1,y:2))\n}\n",
            ),
            ("geo/shape.crag", SHAPE),
        ],
    );
    let mut out = Vec::new();
    assert_eq!(crag_fmt(&root, &["--check"], &mut out), 1);
    assert_eq!(
        String::from_utf8(out).unwrap(),
        "app.crag: not formatted\ngeo/shape.crag: not formatted\n"
    );
    let mut out = Vec::new();
    assert_eq!(
        crag_fmt(&root, &[], &mut out),
        0,
        "{}",
        String::from_utf8_lossy(&out)
    );
    assert_eq!(
        fs::read_to_string(root.join("app.crag")).unwrap(),
        "import std.time\n\nimport demo.geo.shape\n\nfn main() -> Int { area(Point(x: 1, y: 2)) }\n"
    );
    let mut out = Vec::new();
    assert_eq!(crag_fmt(&root, &["--check", "all"], &mut out), 0);
    // A file that does not parse is reported and left alone.
    fs::write(root.join("broken.crag"), "fn f( {\n").unwrap();
    let mut out = Vec::new();
    let broken = root.join("broken.crag");
    assert_eq!(crag_fmt(&root, &[broken.to_str().unwrap()], &mut out), 1);
    assert!(
        String::from_utf8(out)
            .unwrap()
            .contains("broken.crag: not formatted, since it does not parse")
    );
    assert_eq!(
        fs::read_to_string(root.join("broken.crag")).unwrap(),
        "fn f( {\n"
    );
    let _ = fs::remove_dir_all(&root);
}

const ASSERTIONS: &str = r#"import std.test

test "passes" {
  assertEqual(1 + 1, 2)
  assert("abc".startsWith("a"))
}

test "fails twice and goes on" {
  assertEqual(1 + 1, 3)
  let reached = True
  assert(False, "this is false")
  assertEqual([1, 2], [1, 2])
}

test "fails at its end" {
  assertClose(1.0, 1.5, within: 0.1)
}

test "fails in a case" {
  case Int.parse("x") {
    n: Int -> assertEqual(n, 1)
    e: ParseError -> fail("not a number: {e.text}")
  }
}
"#;

#[test]
fn assertions_are_recorded_and_the_test_goes_on() {
    let root = project(
        "assertions",
        &[
            (
                "package.crag",
                "package demo 0.1\nruntime 0.0\nmain demo.app\n",
            ),
            ("app.crag", "fn main() {\n}\n"),
            ("test/app_test.crag", ASSERTIONS),
        ],
    );
    let mut out = Vec::new();
    let report = crag_test(&root, None, &mut out);
    let out = text(out);
    assert_eq!(report.passed, ["test/app_test.crag \"passes\""], "{out}");
    let failed: Vec<(&str, &str)> = report
        .failed
        .iter()
        .map(|(n, r)| (n.as_str(), r.as_str()))
        .collect();
    assert_eq!(
        failed,
        [
            (
                "test/app_test.crag \"fails twice and goes on\"",
                "assertion failed: expected 3, got 2\n --> test/app_test.crag:9:3\n  |\n9 |   assertEqual(1 + 1, 3)\n  |   ^\n\
                 assertion failed: this is false\n  --> test/app_test.crag:11:3\n   |\n11 |   assert(False, \"this is false\")\n   |   ^\n"
            ),
            (
                "test/app_test.crag \"fails at its end\"",
                "assertion failed: expected 1.5 within 0.1, got 1.0\n  --> test/app_test.crag:16:3\n   |\n16 |   assertClose(1.0, 1.5, within: 0.1)\n   |   ^\n"
            ),
            (
                "test/app_test.crag \"fails in a case\"",
                "assertion failed: not a number: x\n  --> test/app_test.crag:22:22\n   |\n22 |     e: ParseError -> fail(\"not a number: {e.text}\")\n   |                      ^\n"
            ),
        ],
        "{out}"
    );
}

#[test]
fn a_program_reads_its_arguments_and_environment() {
    let root = project(
        "env",
        &[
            (
                "package.crag",
                "package demo 0.1\nruntime 0.0\nmain demo.app\n",
            ),
            (
                "app.crag",
                r#"import std.io
import std.env

fn main() {
  printLine("{args()}")
  printLine("{env("CRAG_TEST_VAR")}")
  printLine("{env("CRAG_NO_SUCH_VAR")}")
  printLine("{vars()["CRAG_TEST_VAR"]}")
  printLine("{os() == Linux or os() == MacOs}")
}
"#,
            ),
        ],
    );
    let output = Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(["run", "a", "b c"])
        .current_dir(&root)
        .env("CRAG_TEST_VAR", "hello")
        .env_remove("CRAG_NO_SUCH_VAR")
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(0), "{}", text(output.stderr));
    assert_eq!(
        text(output.stdout),
        "[\"a\", \"b c\"]\n\"hello\"\nEmpty\n\"hello\"\nTrue\n"
    );
}
