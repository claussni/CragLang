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

#[test]
fn partial_application_fills_the_parameters_left() {
    // §6.6: each `_` is a parameter of the closure, of the type the call
    // takes there; the supplied arguments are evaluated once, here.
    let mut r = repl();
    eval(&mut r, "fn plus(a: Int, b: Int) -> Int { a + b }");
    eval(&mut r, "let n = 5");
    eval(&mut r, "let addTen = plus(n * 2, _)");
    assert_eq!(eval(&mut r, "addTen(1)"), "11\n");
    // An overloaded target is chosen as a call would be, with the
    // literals' default types.
    eval(&mut r, "let twice = multiply(_, 2)");
    assert_eq!(eval(&mut r, "[1, 2].map(twice)"), "[2, 4]\n");
    eval(&mut r, "let both = plus(_, _)");
    assert_eq!(eval(&mut r, "both(3, 4)"), "7\n");
    // A generic target takes its type arguments from what is supplied.
    eval(
        &mut r,
        "fn clamp[T: Ordered](x: T, min: T, max: T) -> T {\n  if x < min { min } else { if x > max { max } else { x } }\n}",
    );
    eval(&mut r, "let percent = clamp(_, min: 0, max: 100)");
    assert_eq!(eval(&mut r, "percent(150)"), "100\n");
    // Named arguments, and defaults left to their own.
    eval(
        &mut r,
        "fn resize(w: Int, h: Int = 1, width: Int) -> Int { w + h + width }",
    );
    eval(&mut r, "let thumb = resize(_, width: 256)");
    assert_eq!(eval(&mut r, "thumb(1)"), "258\n");
    // Types that stay open are an error.
    assert!(eval(&mut r, "let open = clamp(_, _, _)").contains("cannot be inferred"),);
}

#[test]
fn module_values_keep_what_their_closures_capture() {
    let mut r = repl();
    eval(
        &mut r,
        "let add = {\n  let m = 10\n  { x: Int -> m + x }\n}",
    );
    assert_eq!(eval(&mut r, "add(1)"), "11\n");
}

#[test]
fn collection_types_construct_empty_collections() {
    // §6.5: brackets after a type give its type arguments.
    let mut r = repl();
    assert_eq!(eval(&mut r, "List[Int]()"), "[]\n");
    assert_eq!(eval(&mut r, "Map[Str, Int]()"), "[:]\n");
    eval(&mut r, "let xs = Set[Int]()");
    assert_eq!(eval(&mut r, "xs.isEmpty()"), "True\n");
}

#[test]
fn let_else_passes_the_unmatched_value_on() {
    // §7.1.1: `else { rest -> … }` receives what the pattern does not
    // match, narrowed, and its `return` leaves the function.
    let mut r = repl();
    eval(&mut r, "type NotFound");
    eval(&mut r, "type DbError(code: Int)");
    eval(&mut r, "type User(name: Str)");
    eval(
        &mut r,
        "fn lookup(id: Int) -> User | NotFound | DbError {\n  if id == 1 { User(name: \"ada\") } else { if id == 2 { NotFound } else { DbError(code: 7) } }\n}",
    );
    eval(
        &mut r,
        "fn code(id: Int) -> Int {\n  let u: User = lookup(id) else { e ->\n    return case e {\n      NotFound -> 0\n      d: DbError -> d.code\n    }\n  }\n  1\n}",
    );
    assert_eq!(eval(&mut r, "code(1)"), "1\n");
    assert_eq!(eval(&mut r, "code(2)"), "0\n");
    assert_eq!(eval(&mut r, "code(3)"), "7\n");
    assert!(
        eval(
            &mut r,
            "fn bad(id: Int) -> Int {\n  let u: User = lookup(id) else { rest -> 5 }\n  1\n}"
        )
        .contains("must leave")
    );
}

#[test]
fn generic_records_take_their_type_arguments_from_their_fields() {
    let mut r = repl();
    eval(&mut r, "type Pair[A, B](a: A, b: B)");
    eval(&mut r, "let p = Pair(a: 1, b: 2.5)");
    assert_eq!(
        eval(&mut r, "Pair(..p, b: \"now\")"),
        "Pair(a: 1, b: \"now\")\n"
    );
    eval(&mut r, "type Step[T](x: T, f: (T) -> T)");
    eval(&mut r, "let s = Step(x: 2, f: { n -> n + 1 })");
    assert_eq!(eval(&mut r, "s.f(s.x)"), "3\n");
}

#[test]
fn closures_read_a_var_as_it_is_when_they_run() {
    // §6.4.1: a closure reads a captured `var`, never a copy of it.
    let mut r = repl();
    eval(
        &mut r,
        "fn f() -> Int {\n  var count = 0\n  let show = { -> count * 10 }\n  count = 5\n  let a = show()\n  count = count + 1\n  a + show()\n}",
    );
    assert_eq!(eval(&mut r, "f()"), "110\n");
    eval(
        &mut r,
        "fn g() -> Int {\n  var base = 1\n  fn plus(x: Int) -> Int { x + base }\n  base = 10\n  plus(5)\n}",
    );
    assert_eq!(eval(&mut r, "g()"), "15\n");
    assert!(
        eval(&mut r, "fn h() -> () -> Int {\n  var n = 1\n  { -> n }\n}")
            .contains("cannot capture the `var` `n`")
    );
}

#[test]
fn module_lets_bind_the_parts_their_patterns_name() {
    let mut r = repl();
    eval(&mut r, "type Point(x: Int, y: Int)");
    eval(&mut r, "let Point(x, y) = Point(x: 1, y: 2)");
    eval(&mut r, "let (a:, b:) = (a: 10, b: \"s\")");
    assert_eq!(eval(&mut r, "x * 10 + y"), "12\n");
    assert_eq!(eval(&mut r, "b"), "\"s\"\n");
}

#[test]
fn lifted_calls_fill_in_defaults() {
    // §4.6.1: each member's overload is called as a call would call it.
    let mut r = repl();
    eval(&mut r, "type A(n: Int)");
    eval(&mut r, "type B(n: Int)");
    eval(&mut r, "fn size(a: A, k: Int = 1) -> Int { a.n * k }");
    eval(&mut r, "fn size(b: B, k: Int = 10) -> Int { b.n * k }");
    eval(&mut r, "fn g(x: A | B) -> Int { size(x) }");
    assert_eq!(eval(&mut r, "g(A(n: 3))"), "3\n");
    assert_eq!(eval(&mut r, "g(B(n: 3))"), "30\n");
}
