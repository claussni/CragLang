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
