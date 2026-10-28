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

//! Control flow run in the scratch image (Specification Ch. 7 and 8).

use crag_driver::{Project, Repl, Scratch};
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
fn for_walks_maps_sets_and_ranges_of_any_discrete_type() {
    let mut r = repl();
    // §7.3.1: a map's entries are destructured.
    eval(
        &mut r,
        "fn ages() -> Int {\n  let ages = [\"ada\": 36, \"bob\": 2]\n  var t = 0\n  for (key, value) in ages { t = t + value }\n  for (key, _) in ages { t = t + 100 }\n  t\n}",
    );
    assert_eq!(eval(&mut r, "ages()"), "238\n");
    eval(
        &mut r,
        "fn members() -> Int {\n  let s: Set[Int] = [1, 2, 3]\n  var t = 0\n  for x in s { t = t + x }\n  t\n}",
    );
    assert_eq!(eval(&mut r, "members()"), "6\n");
    // §7.4: a type with `compare` and `next` forms ranges, open ones too.
    eval(&mut r, "type Day(n: Int)");
    eval(
        &mut r,
        "fn compare(a: Day, b: Day) -> Ordering { compare(a.n, b.n) }",
    );
    eval(&mut r, "fn next(d: Day) -> Day { Day(n: d.n + 1) }");
    eval(
        &mut r,
        "fn days() -> Int {\n  var n = 0\n  for d in Day(n: 1)..Day(n: 4) { n = n + d.n }\n  for d in Day(n: 5).. {\n    if d.n > 7 { return n }\n    n = n + d.n\n  }\n  n\n}",
    );
    assert_eq!(eval(&mut r, "days()"), "28\n");
}

#[test]
fn pass_hands_the_rest_to_the_caller() {
    // §8.2, entered line by line as the REPL reads it.
    let mut r = repl();
    eval(&mut r, "type NotFound");
    eval(
        &mut r,
        "fn next(x: Int | NotFound) -> Int | NotFound {\n  case x {\n    n: Int -> n + 1\n    pass\n  }\n}",
    );
    assert_eq!(eval(&mut r, "next(4)"), "5\n");
    assert_eq!(eval(&mut r, "next(NotFound)"), "NotFound\n");
    assert!(crag_driver::repl::is_complete("case x {\n  pass\n}"));
}

#[test]
fn type_mapping_functions_keep_successes_or_errors() {
    // §8.4: `~` keeps the errors, `?` turns them into `Empty`, `!!` into
    // a trap.
    let mut r = repl();
    eval(&mut r, "type E(..Error)");
    eval(&mut r, "fn kept(x: Int | E) -> () | E { ~x }");
    eval(&mut r, "fn checked(x: Int | E) -> Option[Int] { ?x }");
    eval(&mut r, "fn expected(x: Int | E) -> Int { !!x }");
    assert_eq!(eval(&mut r, "kept(E)"), "E()\n");
    assert_eq!(eval(&mut r, "checked(3)"), "3\n");
    assert_eq!(eval(&mut r, "checked(E)"), "Empty\n");
    assert_eq!(eval(&mut r, "expected(4)"), "4\n");
    assert!(eval(&mut r, "expected(E)").starts_with("trap: `!!` met an error"));
}

#[test]
fn trap_handlers_give_their_block_its_value() {
    // §8.3.1: a handler takes a trap in its block or in what it calls;
    // the most specific of a block's handlers wins, and one that takes
    // none passes it on.
    let mut r = repl();
    eval(
        &mut r,
        "fn deep(n: Int) -> Int { if n == 0 { 1 / n } else { deep(n - 1) } }",
    );
    eval(
        &mut r,
        "fn safe(xs: List[Int], i: Int) -> Int {\n  on OutOfBounds { t -> -1 }\n  xs[i]\n}",
    );
    assert_eq!(eval(&mut r, "safe([1, 2], 1)"), "2\n");
    assert_eq!(eval(&mut r, "safe([1, 2], 5)"), "-1\n");
    eval(
        &mut r,
        "fn told(n: Int) -> Str {\n  on Trap { t -> \"{t.message} at {t.origin.line}:{t.origin.column}\" }\n  \"fine {deep(n)}\"\n}",
    );
    assert_eq!(eval(&mut r, "told(3)"), "\"division by zero at 1:38\"\n");
    eval(
        &mut r,
        "fn specific() -> Str {\n  on Trap { t -> \"any\" }\n  on DivisionByZero { t -> \"zero\" }\n  \"{deep(0)}\"\n}",
    );
    assert_eq!(eval(&mut r, "specific()"), "\"zero\"\n");
    // Passed on, the trap reports where it began.
    eval(
        &mut r,
        "fn other() -> Int {\n  on Overflow { t -> 0 }\n  deep(2)\n}",
    );
    let out = eval(&mut r, "other()");
    assert!(
        out.starts_with("trap: division by zero\n --> deep:1:38"),
        "{out}"
    );
    assert!(
        out.contains("  in deep\n") && out.contains("  in other"),
        "{out}"
    );
    eval(
        &mut r,
        "fn passing() -> Int {\n  on Trap { t -> emit t }\n  deep(1)\n}",
    );
    assert!(eval(&mut r, "passing()").starts_with("trap: division by zero"));
    // `!!` names the error it met.
    eval(&mut r, "type E(..Error)");
    eval(
        &mut r,
        "fn x(v: Int | E) -> Str {\n  on Expectation { t -> \"met {t.errorType}\" }\n  \"{!!v}\"\n}",
    );
    assert_eq!(eval(&mut r, "x(E)"), "\"met E\"\n");
    // An `atomic` block a trap leaves rolls back; refs keep the rest.
    eval(
        &mut r,
        "fn tx(n: Int) -> Int {\n  ref r: Int = 10\n  r.swap(20)\n  on Trap { t -> r.use() }\n  atomic {\n    r.swap(30)\n    let x = 1 / n\n  }\n  r.use()\n}",
    );
    assert_eq!(eval(&mut r, "tx(0)"), "20\n");
    assert_eq!(eval(&mut r, "tx(1)"), "30\n");
}

#[test]
fn constructions_check_the_conditions_of_their_types() {
    // §3.10.1: a value that fails a condition of its type, or of a
    // parent's, traps with `ConditionFailed`, which names it.
    let mut r = repl();
    eval(
        &mut r,
        "type Percent(value: Int) where { nonNegative: value >= 0, atMost100: value <= 100 }",
    );
    eval(
        &mut r,
        "fn percent(k: Int) -> Str {\n  on ConditionFailed { t -> \"rejected: {t.condition}\" }\n  \"ok {Percent(value: k).value}\"\n}",
    );
    assert_eq!(eval(&mut r, "percent(50)"), "\"ok 50\"\n");
    assert_eq!(eval(&mut r, "percent(150)"), "\"rejected: atMost100\"\n");
    assert_eq!(eval(&mut r, "percent(-1)"), "\"rejected: nonNegative\"\n");
    eval(&mut r, "type Base(x: Int) where x != 0");
    eval(&mut r, "type Sub(..Base, y: Int) where y > this.x");
    eval(&mut r, "fn sub(a: Int, b: Int) -> Sub { Sub(x: a, y: b) }");
    assert_eq!(eval(&mut r, "sub(1, 2)"), "Sub(x: 1, y: 2)\n");
    let out = eval(&mut r, "sub(0, 5)");
    assert!(
        out.starts_with("trap: a value failed a condition of its type: x != 0"),
        "{out}"
    );
    assert!(eval(&mut r, "sub(3, 1)").contains("y > this.x"));
}
