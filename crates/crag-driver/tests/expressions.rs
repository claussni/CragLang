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

//! Expressions run in the scratch image (Specification Ch. 6).

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
fn optional_access_goes_on_only_with_a_value() {
    // §6.8: `?.` gives `Empty` for an `Empty` receiver, and the access
    // on anything else; an `Option` the access gives is not nested.
    let mut r = repl();
    eval(&mut r, "type Address(city: Str)");
    eval(&mut r, "type User(name: Str, address: Option[Address])");
    eval(
        &mut r,
        "fn city(u: Option[User]) -> Option[Str] { u?.address?.city }",
    );
    let rome = "User(name: \"a\", address: Address(city: \"Rome\"))";
    assert_eq!(eval(&mut r, &format!("city({rome})")), "\"Rome\"\n");
    assert_eq!(
        eval(&mut r, "city(User(name: \"a\", address: Empty))"),
        "Empty\n"
    );
    assert_eq!(eval(&mut r, "city(Empty)"), "Empty\n");
    // Calls, through UFCS or of a function in a field, run only with a
    // value, their arguments too.
    eval(&mut r, "let ages = [\"ada\": 36]");
    assert_eq!(eval(&mut r, "ages[\"ada\"]?.add(1)"), "37\n");
    assert_eq!(eval(&mut r, "ages[\"bob\"]?.add(1 / 0)"), "Empty\n");
    eval(&mut r, "type Step(next: (Int) -> Int)");
    eval(
        &mut r,
        "let step: Option[Step] = Step(next: { x -> x + 1 })",
    );
    assert_eq!(eval(&mut r, "step?.next(2)"), "3\n");
}

#[test]
fn updates_change_fields_by_paths_and_transforms() {
    // §6.7: a dotted path rebuilds the record below it, and a function
    // from the field's type to itself transforms the current value.
    let mut r = repl();
    eval(&mut r, "type Pos(x: Int, y: Int)");
    eval(&mut r, "type Shape(pos: Pos, size: Int)");
    eval(&mut r, "type Circle(..Shape, r: Int)");
    eval(&mut r, "let s = Shape(pos: Pos(x: 1, y: 2), size: 10)");
    assert_eq!(
        eval(&mut r, "Shape(..s, pos.x: 3, size: 50)"),
        "Shape(pos: Pos(x: 3, y: 2), size: 50)\n"
    );
    assert_eq!(
        eval(&mut r, "Shape(..s, size: _ * 2, pos.x: _ + 5, pos.y: 7)"),
        "Shape(pos: Pos(x: 6, y: 7), size: 20)\n"
    );
    eval(&mut r, "fn double(n: Int) -> Int { n * 2 }");
    assert_eq!(
        eval(&mut r, "Shape(..s, size: double)"),
        "Shape(pos: Pos(x: 1, y: 2), size: 20)\n"
    );
    // Anonymous records take the list too.
    eval(&mut r, "let p = (x: 1, y: 2)");
    assert_eq!(eval(&mut r, "(..p, x: _ + 1)"), "(x: 2, y: 2)\n");
    assert_eq!(
        eval(&mut r, "(..s, pos.y: 9)"),
        "(pos: Pos(x: 1, y: 9), size: 10)\n"
    );
    // §6.7.1: `update` keeps the value's own type, in generic code too.
    assert_eq!(
        eval(&mut r, "s.update(pos.x: _ + 1)"),
        "Shape(pos: Pos(x: 2, y: 2), size: 10)\n"
    );
    eval(
        &mut r,
        "fn nudge[S: Shape](v: S) -> S {\n  v.update(pos.x: _ + 1)\n}",
    );
    assert_eq!(
        eval(&mut r, "nudge(Circle(pos: Pos(x: 0, y: 0), size: 1, r: 5))"),
        "Circle(pos: Pos(x: 1, y: 0), size: 1, r: 5)\n"
    );
}
