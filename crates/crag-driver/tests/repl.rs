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

//! The REPL's inputs: definitions, expressions run in the scratch image,
//! `:rebind` and the other commands.

use crag_driver::repl::{is_complete, is_definition};
use crag_driver::{EvalOutput, Project, Repl, Scratch};
use crag_session::ImageCommand;

fn repl() -> Repl {
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    Repl::new(Project::bare(), scratch)
}

/// What the REPL prints for an input, errors included.
fn eval(r: &mut Repl, text: &str) -> String {
    match r.eval_input(text) {
        Ok(output) => output.render(),
        Err(errors) => errors,
    }
}

#[test]
fn expressions_run_and_show_their_values() {
    let mut r = repl();
    assert_eq!(eval(&mut r, "40 + 2"), "42\n");
    assert_eq!(eval(&mut r, "1 < 2"), "True\n");
    assert_eq!(eval(&mut r, "1.5 * 2.0"), "3.0\n");
    assert_eq!(eval(&mut r, "'x'"), "'x'\n");
    // A block of statements, whose last gives the value.
    assert_eq!(
        eval(&mut r, "var t = 0\nfor i in 1..4 {\n  t = t + i\n}\nt"),
        "10\n"
    );
    // `()` shows nothing.
    assert_eq!(eval(&mut r, "if 1 < 2 { }"), "");
    // A union shows its member.
    assert_eq!(eval(&mut r, "type Odd"), "");
    assert_eq!(
        eval(
            &mut r,
            "fn half(n: Int) -> Int | Odd { if n % 2 == 0 { n / 2 } else { Odd } }"
        ),
        ""
    );
    assert_eq!(eval(&mut r, "half(8)"), "4\n");
    assert_eq!(eval(&mut r, "half(7)"), "Odd\n");
    // Any value prints, from the shape of its type, in the image.
    assert_eq!(eval(&mut r, "[1, 2]"), "[1, 2]\n");
    assert_eq!(eval(&mut r, "type Point(x: Int, y: Int)"), "");
    assert_eq!(
        eval(&mut r, "[1: Point(x: 1, y: 2), 0: Point(x: 0, y: 0)]"),
        "[0: Point(x: 0, y: 0), 1: Point(x: 1, y: 2)]\n"
    );
    assert_eq!(eval(&mut r, "{ n: Int -> n + 1 }"), "<function>\n");
    // A long one is cut short.
    let numbers: Vec<String> = (0..1000).map(|i| i.to_string()).collect();
    let long = eval(&mut r, &format!("[{}]", numbers.join(", ")));
    assert!(long.ends_with(", 99, … 900 more]\n"), "{long}");
}

#[test]
fn strings_run_and_show_as_literals() {
    let mut r = repl();
    // A constant, computed by the host and decoded in the image.
    let name = "Ada Lovelace, Countess of Lovelace";
    assert_eq!(eval(&mut r, &format!("let name = \"{name}\"")), "");
    assert_eq!(eval(&mut r, "name"), format!("\"{name}\"\n"));
    assert_eq!(
        eval(&mut r, "\"Hello, {name}!\""),
        format!("\"Hello, {name}!\"\n")
    );
    assert_eq!(
        eval(&mut r, "\"{1 + 1} items at {2.5}\""),
        "\"2 items at 2.5\"\n"
    );
    assert_eq!(eval(&mut r, &format!("name == \"{name}\"")), "True\n");
    assert_eq!(eval(&mut r, "name == \"Ada\""), "False\n");
    assert_eq!(
        eval(
            &mut r,
            "[\"b\": 2, \"a long key, in a buffer\": 1][\"a long key, in a buffer\"]"
        ),
        "1\n"
    );
    assert_eq!(
        eval(&mut r, "\"tab\\tand {{braces}}\""),
        "\"tab\\tand {{braces}}\"\n"
    );
    assert_eq!(eval(&mut r, "b\"\\x01 bytes\""), "b\"\\x01 bytes\"\n");
}

#[test]
fn definitions_stay_and_names_are_defined_once() {
    let mut r = repl();
    assert_eq!(eval(&mut r, "type Point(x: Int, y: Int)"), "");
    assert_eq!(eval(&mut r, "let origin = Point(x: 3, y: 4)"), "");
    assert_eq!(eval(&mut r, "fn area(p: Point) -> Int { p.x * p.y }"), "");
    assert_eq!(eval(&mut r, "area(origin)"), "12\n");
    assert_eq!(eval(&mut r, "origin.x + area(Point(x: 1, y: 2))"), "5\n");
    assert_eq!(
        eval(&mut r, "fn area(p: Point) -> Int { 0 }"),
        "error: area is already defined in this session; use :rebind\n"
    );
    assert_eq!(
        eval(&mut r, "fn __input() -> Int { 0 }"),
        "error: __input is the REPL's own name\n"
    );
    // Several declarations in one input.
    assert_eq!(
        eval(
            &mut r,
            "fn one() -> Int { 1 }\nfn two() -> Int { one() + 1 }"
        ),
        ""
    );
    assert_eq!(eval(&mut r, "two()"), "2\n");
}

#[test]
fn errors_are_shown_against_the_input_and_change_nothing() {
    let mut r = repl();
    assert_eq!(eval(&mut r, "fn double(n: Int) -> Int { n * 2 }"), "");
    assert_eq!(
        eval(&mut r, "double(missing)"),
        "error: `missing` is not defined\n --> input:1:8\n  |\n1 | double(missing)\n  |        ^^^^^^^\n"
    );
    assert_eq!(
        eval(&mut r, "fn broken() -> Int {\n  nothing\n}"),
        "error: `nothing` is not defined\n --> input:2:3\n  |\n2 |   nothing\n  |   ^^^^^^^\n"
    );
    // The broken definition was not added.
    assert_eq!(
        eval(&mut r, "broken()"),
        "error: `broken` is not defined\n --> input:1:1\n  |\n1 | broken()\n  | ^^^^^^\n"
    );
    assert!(eval(&mut r, "fn ) {").starts_with("error: "));
    // A constant is computed when it is defined, and one that fails is an
    // error.
    assert_eq!(
        eval(&mut r, "let half: Int = double(1) / 0"),
        "error: `half` cannot be computed at compile time: it traps with division by zero\n --> input:1:1\n  |\n1 | let half: Int = double(1) / 0\n  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n"
    );
    assert_eq!(eval(&mut r, "double(21)"), "42\n");
}

#[test]
fn a_trap_is_reported_against_the_input() {
    let mut r = repl();
    assert_eq!(
        eval(&mut r, "fn ratio(a: Int, b: Int) -> Int { a / b }"),
        ""
    );
    assert_eq!(
        eval(&mut r, "ratio(1, 0)"),
        "trap: division by zero\n --> ratio:1:35\n  |\n1 | fn ratio(a: Int, b: Int) -> Int { a / b }\n  |                                   ^\n  in ratio\n"
    );
    assert_eq!(
        eval(&mut r, "1 + 9223372036854775807"),
        "trap: arithmetic overflow\n --> input:1:1\n  |\n1 | 1 + 9223372036854775807\n  | ^\n  in the input\n"
    );
    assert_eq!(eval(&mut r, "ratio(6, 3)"), "2\n");
}

#[test]
fn rebind_replaces_a_definition_and_names_its_dependents() {
    let mut r = repl();
    assert_eq!(eval(&mut r, "fn tax(x: Int) -> Int { x / 5 }"), "");
    assert_eq!(eval(&mut r, "fn gross(x: Int) -> Int { x + tax(x) }"), "");
    assert_eq!(
        eval(&mut r, "fn twice(x: Int) -> Int { gross(gross(x)) }"),
        ""
    );
    assert_eq!(eval(&mut r, "fn other(x: Int) -> Int { x }"), "");
    assert_eq!(eval(&mut r, "let base = gross(100)"), "");
    assert_eq!(eval(&mut r, "base"), "120\n");
    assert_eq!(eval(&mut r, "twice(100)"), "144\n");
    assert_eq!(
        eval(&mut r, ":rebind fn tax(x: Int) -> Int { x / 10 }"),
        "rebound tax (3 dependents: gross, twice, base)\n"
    );
    // The dependents run the new code, and the value is computed again.
    assert_eq!(eval(&mut r, "gross(100)"), "110\n");
    assert_eq!(eval(&mut r, "base"), "110\n");
    assert_eq!(eval(&mut r, "twice(100)"), "121\n");
    assert_eq!(
        eval(&mut r, ":rebind fn other(x: Int) -> Int { x + 1 }"),
        "rebound other\n"
    );
    assert_eq!(
        eval(&mut r, ":rebind fn missing() -> Int { 1 }"),
        "error: missing is not defined in this session; define it without :rebind\n"
    );
    // A rebind that breaks a dependent is refused, and the error is shown
    // in the dependent.
    assert_eq!(
        eval(&mut r, ":rebind fn tax(x: Int, y: Int) -> Int { x }"),
        "error: the argument `y` is missing\n --> gross:1:31\n  |\n1 | fn gross(x: Int) -> Int { x + tax(x) }\n  |                               ^^^^^^\n"
    );
    assert_eq!(eval(&mut r, "gross(100)"), "110\n");

    // A field of the name is no use of it.
    assert_eq!(eval(&mut r, "type Pair(a: Int, b: Int)"), "");
    assert_eq!(eval(&mut r, "fn first(p: Pair) -> Int { p.a }"), "");
    assert_eq!(eval(&mut r, "fn a() -> Int { 1 }"), "");
    assert_eq!(eval(&mut r, ":rebind fn a() -> Int { 2 }"), "rebound a\n");
}

#[test]
fn commands_and_completion() {
    let mut r = repl();
    assert!(eval(&mut r, ":help").contains(":rebind <definition>"));
    assert_eq!(r.eval_input(":quit"), Ok(EvalOutput::Quit));
    assert_eq!(
        eval(&mut r, ":frobnicate"),
        "error: there is no command :frobnicate; :help lists them\n"
    );
    assert_eq!(
        eval(&mut r, ":rebind"),
        "error: :rebind takes a definition\n"
    );
    assert_eq!(eval(&mut r, "fn total(n: Int) -> Int { n }"), "");
    assert_eq!(eval(&mut r, "let tally = 3"), "");
    assert_eq!(r.completions("ta"), ["tally"]);
    assert_eq!(r.completions("to"), ["total"]);
    // Keywords, and the prelude's names.
    assert_eq!(r.completions("retu"), ["return"]);
    assert!(r.completions("Int").contains(&"Int".to_string()));
}

#[test]
fn inputs_are_complete_when_the_parser_wants_nothing_more() {
    assert!(is_complete("1 + 2"));
    assert!(!is_complete("1 +"));
    assert!(!is_complete("fn f() -> Int {"));
    assert!(is_complete("fn f() -> Int {\n  1\n}"));
    assert!(!is_complete("if x {\n  1\n} else {"));
    assert!(!is_complete("[1,\n 2,"));
    assert!(is_complete("(1 + )"));
    // An error inside the input ends it, whatever the parser finds after.
    assert!(is_complete("twice321)"));
    assert!(is_complete(":rebind fn f() -> Int {"));
    assert!(is_complete(""));
    assert!(is_definition("fn f() -> Int { 1 }"));
    assert!(is_definition("pub type T(x: Int)"));
    assert!(is_definition("let x = 1"));
    assert!(!is_definition("f(1)"));
    assert!(!is_definition("var x = 1"));
}

#[test]
fn crag_without_arguments_reads_inputs_from_its_input() {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let dir = std::env::temp_dir().join(format!("crag-repl-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
        .current_dir(&dir)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    // An input spans lines until it is complete; an empty line ends one
    // that is not.
    let input = "fn double(n: Int) -> Int {\n  n * 2\n}\ndouble(21)\n\n\
                 :rebind fn double(n: Int) -> Int { n * 3 }\ndouble(\n  2\n)\n\
                 1 +\n\n:quit\n40 + 2\n";
    child
        .stdin
        .take()
        .unwrap()
        .write_all(input.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let _ = std::fs::remove_dir_all(&dir);
    assert!(out.status.success());
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(
        stdout.starts_with("42\nrebound double\n6\nerror: "),
        "{stdout}"
    );
    // Nothing runs after `:quit`.
    assert!(!stdout.contains("\n42\n"), "{stdout}");
}
