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
    // Named arguments go to every member's call: as parameters, or as
    // the record they build (§5.6.2).
    eval(&mut r, "fn h(x: A | B) -> Int { size(x, k: 2) }");
    assert_eq!(eval(&mut r, "h(A(n: 3))"), "6\n");
    assert_eq!(eval(&mut r, "h(B(n: 3))"), "6\n");
    eval(&mut r, "type By(by: Int, plus: Int = 0)");
    eval(
        &mut r,
        "fn scaled(a: A, o: By) -> Int { a.n * o.by + o.plus }",
    );
    eval(
        &mut r,
        "fn scaled(b: B, o: By) -> Int { -b.n * o.by + o.plus }",
    );
    eval(
        &mut r,
        "fn s(x: A | B) -> Int { scaled(x, by: 5, plus: 1) }",
    );
    assert_eq!(eval(&mut r, "s(A(n: 3))"), "16\n");
    assert_eq!(eval(&mut r, "s(B(n: 3))"), "-14\n");
    eval(&mut r, "fn t(x: A | B) -> Int { scaled(x, by: 2) }");
    assert_eq!(eval(&mut r, "t(B(n: 3))"), "-6\n");
}

#[test]
fn conversions_go_through_convert() {
    // §5.6, §19.13: `T(x)` calls the `convert` that makes a `T`; one that
    // may not fit gives `Unconvertible`.
    let mut r = repl();
    assert_eq!(eval(&mut r, "Float(3)"), "3.0\n");
    assert_eq!(eval(&mut r, "Int8(100)"), "100\n");
    assert_eq!(eval(&mut r, "Int8(300)"), "Unconvertible()\n");
    assert_eq!(eval(&mut r, "UInt8(-1)"), "Unconvertible()\n");
    assert_eq!(eval(&mut r, "Int8.trunc(300)"), "44\n");
    assert_eq!(eval(&mut r, "Int(-2.9)"), "-2\n");
    assert_eq!(eval(&mut r, "Int(1.0e30)"), "Unconvertible()\n");
    assert_eq!(eval(&mut r, "Int.round(-2.5)"), "-3\n");
    assert_eq!(eval(&mut r, "Int.floor(-2.5)"), "-3\n");
    assert_eq!(eval(&mut r, "Int.ceil(2.1)"), "3\n");
    assert_eq!(eval(&mut r, "CodePoint(97)"), "'a'\n");
    assert_eq!(eval(&mut r, "Int('a')"), "97\n");
    // A module adds its own.
    eval(&mut r, "type Celsius(degrees: Float)");
    eval(
        &mut r,
        "fn convert(f: Float) -> Celsius { Celsius(degrees: f) }",
    );
    assert_eq!(eval(&mut r, "Celsius(21.5)"), "Celsius(degrees: 21.5)\n");
    assert!(eval(&mut r, "Celsius(\"warm\")").contains("error"));
}

#[test]
fn derived_forms_follow_the_structure() {
    // §19.11: a record fits by its fields, a union by its members; a
    // function fits none, and a type that is `not F` never fits `F`
    // (§3.11).
    let mut r = repl();
    eval(&mut r, "fn h[K: Hash](k: K) -> Int { 1 }");
    eval(&mut r, "type A(n: Int)");
    eval(&mut r, "type B(s: Str)");
    eval(&mut r, "let u: A | B = A(n: 1)");
    assert_eq!(eval(&mut r, "h(u)"), "1\n");
    assert_eq!(eval(&mut r, "A(n: 1) == A(n: 1)"), "True\n");
    eval(&mut r, "type F(f: () -> Int)");
    assert!(eval(&mut r, "h(F(f: { -> 1 }))").contains("does not hold"));
    assert!(eval(&mut r, "F(f: { -> 1 }) == F(f: { -> 1 })").contains("error"));
    eval(&mut r, "type Secret(n: Int) is not Hash");
    assert!(eval(&mut r, "h(Secret(n: 1))").contains("does not hold"));
    assert_eq!(
        eval(&mut r, "fn hash(s: Secret) -> Int { 1 }"),
        "error: Secret is `not Hash`, so no function may make it fit `Hash`\n --> input:1:4\n  |\n1 | fn hash(s: Secret) -> Int { 1 }\n  |    ^^^^\n"
    );
}

#[test]
fn a_sign_before_a_bare_number_is_part_of_the_literal() {
    // §6.2.1: `-5` is one literal, so it fits a narrow type and a
    // conditioned alias; `x-2` stays a subtraction.
    let mut r = repl();
    assert_eq!(eval(&mut r, "-5"), "-5\n");
    assert_eq!(eval(&mut r, "-1.5"), "-1.5\n");
    assert_eq!(eval(&mut r, "3 -1"), "2\n");
    eval(&mut r, "let x = 4");
    assert_eq!(eval(&mut r, "x-2"), "2\n");
    assert_eq!(eval(&mut r, "-(-5)"), "5\n");
    eval(&mut r, "type Temp = Int where this >= -273");
    eval(&mut r, "fn t(k: Temp) -> Temp { k }");
    assert_eq!(eval(&mut r, "t(-10)"), "-10\n");
    assert!(eval(&mut r, "t(-300)").contains("fails the condition"));
}

#[test]
fn grids_have_rows_and_columns() {
    // §12.3, §19.11.
    let mut r = repl();
    eval(&mut r, "let m = [1, 2, 3; 4, 5, 6]");
    assert_eq!(eval(&mut r, "m.row(0)"), "[1, 2, 3]\n");
    assert_eq!(eval(&mut r, "m.column(1)"), "[2, 5]\n");
    assert_eq!(eval(&mut r, "m[1, 2]"), "6\n");
    assert!(eval(&mut r, "m[2, 0]").starts_with("trap: index out of range"));
    assert_eq!(eval(&mut r, "m.get(5, 5)"), "Empty\n");
    assert_eq!(
        eval(&mut r, "m.transpose().rows()"),
        "[[1, 4], [2, 5], [3, 6]]\n"
    );
    assert_eq!(
        eval(&mut r, "m.map { x -> x * 10 }.row(1)"),
        "[40, 50, 60]\n"
    );
    assert_eq!(eval(&mut r, "m.set(0, 0, 9).row(0)"), "[9, 2, 3]\n");
    assert_eq!(eval(&mut r, "grid(2, 3, 0).height()"), "3\n");
    eval(
        &mut r,
        "fn total(g: Grid[Int]) -> Int {\n  var t = 0\n  for x in g { t = t + x }\n  t\n}",
    );
    assert_eq!(eval(&mut r, "total(m)"), "21\n");
    assert!(eval(&mut r, "[1, 2; 3]").contains("a grid's rows are of one width"));
    // A grid is shown as its literal, or as its record without one.
    assert_eq!(eval(&mut r, "m"), "[1, 2, 3; 4, 5, 6]\n");
    assert_eq!(eval(&mut r, "[\"a\"; \"b\"]"), "[\"a\"; \"b\"]\n");
    assert_eq!(
        eval(&mut r, "grid(2, 1, 0)"),
        "Grid(width: 2, height: 1, cells: [0, 0])\n"
    );
}

#[test]
fn a_type_s_own_show_writes_its_values() {
    // §19.11: a type's own `show` is chosen over the derived one where a
    // value is shown: in the REPL, in interpolation and through `Show`.
    let mut r = repl();
    eval(&mut r, "type P(x: Int)");
    eval(&mut r, "fn show(p: P) -> Str { \"p{p.x}\" }");
    assert_eq!(eval(&mut r, "P(x: 1)"), "p1\n");
    assert_eq!(eval(&mut r, "\"<{P(x: 2)}>\""), "\"<p2>\"\n");
    eval(&mut r, "fn angled[T: Show](x: T) -> Str { \"<{x}>\" }");
    assert_eq!(eval(&mut r, "angled(P(x: 3))"), "\"<p3>\"\n");
    assert_eq!(
        eval(&mut r, "[P(x: 1), P(x: 2); P(x: 3), P(x: 4)]"),
        "[p1, p2; p3, p4]\n"
    );
    // Strings and numbers are written as before.
    assert_eq!(eval(&mut r, "\"{\"a\"} {3}\""), "\"a 3\"\n");
}

#[test]
fn values_convert_to_the_wider_types_they_fit() {
    // §3.13.3: an immutable generic type fits one whose arguments its own
    // fit, and a function one whose parameters fit its own; the value is
    // built anew where the two lay out their parts differently.
    let mut r = repl();
    eval(&mut r, "fn first(xs: List[Int | Str]) -> Int | Str { xs[0] }");
    eval(&mut r, "let ys: List[Int] = [7, 8]");
    assert_eq!(eval(&mut r, "first(ys)"), "7\n");
    eval(&mut r, "let wide: List[Int | Str] = ys");
    assert_eq!(eval(&mut r, "wide"), "[7, 8]\n");
    eval(&mut r, "let nested: List[List[Int]] = [[1], [2, 3]]");
    eval(&mut r, "let wider: List[List[Int | Str]] = nested");
    assert_eq!(eval(&mut r, "wider"), "[[1], [2, 3]]\n");
    eval(&mut r, "let m: Map[Str, List[Int]] = [\"x\": [1, 2]]");
    eval(&mut r, "let mw: Map[Str, List[Int | Str]] = m");
    assert_eq!(eval(&mut r, "mw"), "[\"x\": [1, 2]]\n");
    eval(&mut r, "type Box[T](item: T)");
    eval(&mut r, "let bi = Box(item: 4)");
    eval(&mut r, "let bu: Box[Int | Str] = bi");
    assert_eq!(eval(&mut r, "bu"), "Box(item: 4)\n");
    eval(&mut r, "let o: Option[List[Int]] = [1]");
    eval(&mut r, "let ow: Option[List[Int | Str]] = o");
    assert_eq!(eval(&mut r, "ow"), "[1]\n");
    // Function values: by their parameters and by their results.
    eval(&mut r, "fn h(x: Int | Str) -> Int { case x {\n n: Int -> n\n _ -> 0\n } }");
    assert_eq!(eval(&mut r, "[7].map(h)"), "[7]\n");
    eval(&mut r, "let g: (Int) -> Int = h");
    assert_eq!(eval(&mut r, "g(9)"), "9\n");
    eval(&mut r, "fn twice(f: (Int) -> Int | Str, x: Int) -> Int | Str { f(x) }");
    eval(&mut r, "fn inc(x: Int) -> Int { x + 1 }");
    assert_eq!(eval(&mut r, "twice(inc, 4)"), "5\n");
    eval(&mut r, "let fs: List[(Int | Str) -> Int] = [h]");
    eval(&mut r, "let gs: List[(Int) -> Int] = fs");
    assert_eq!(eval(&mut r, "gs[0](5)"), "5\n");
    // `number` as a value converts and names the tag it meets (§3.1.4).
    assert_eq!(eval(&mut r, "[1.5].map(number)"), "[1.5]\n");
    eval(&mut r, "fn nan() -> Float | NonFinite { NaN }");
    eval(
        &mut r,
        "fn passed() -> Str {\n  on NotFinite { e -> \"tag {e.tag}\" }\n  \"{[nan()].map(number)}\"\n}",
    );
    assert_eq!(eval(&mut r, "passed()"), "\"tag NaN\"\n");
}

#[test]
fn a_tag_s_level_is_a_type() {
    // §3.6.1: `Empty`'s parameter names its level, which is a type.
    let mut r = repl();
    assert_eq!(eval(&mut r, "Empty[Int]"), "Empty\n");
    eval(&mut r, "let o: Option[Int] = Empty[Int]");
    assert_eq!(eval(&mut r, "o"), "Empty\n");
    let out = eval(&mut r, "Empty[123]");
    assert!(out.contains("other types a type"), "{out}");
    let out = eval(&mut r, "List[123]()");
    assert!(out.contains("other types a type"), "{out}");
}

#[test]
fn named_arguments_build_the_record_a_function_value_takes() {
    // §5.6.2: named arguments to a function value build its last
    // parameter, a record, with the record's defaults.
    let mut r = repl();
    eval(&mut r, "fn both(r: (a: Int, b: Int)) -> Int { r.a + r.b }");
    eval(&mut r, "let f = both");
    assert_eq!(eval(&mut r, "f(a: 1, b: 2)"), "3\n");
    eval(
        &mut r,
        "fn apply(g: ((a: Int, b: Int)) -> Int) -> Int { g(a: 3, b: 4) }",
    );
    assert_eq!(eval(&mut r, "apply(both)"), "7\n");
    assert_eq!(eval(&mut r, "apply { r -> r.a * r.b }"), "12\n");
    eval(&mut r, "type Opts(width: Int, fill: Str = \"-\")");
    eval(
        &mut r,
        "fn pad(n: Int, o: Opts) -> Str { \"{n}{o.fill}{o.width}\" }",
    );
    eval(&mut r, "let p = pad");
    assert_eq!(eval(&mut r, "p(1, width: 3)"), "\"1-3\"\n");
    assert_eq!(eval(&mut r, "p(1, width: 3, fill: \"*\")"), "\"1*3\"\n");
    assert!(eval(&mut r, "f(a: 1)").contains("the field `b` is missing"));
    // Its parameters have no names of their own.
    eval(&mut r, "let h = { x: Int -> x }");
    assert!(eval(&mut r, "h(x: 1)").contains("there is no parameter `x`"));
}

#[test]
fn derived_functions_use_the_own_functions_of_parts() {
    // §19.11: a part with a function of its own is written, compared and
    // hashed by it inside the derived functions: in fields, members,
    // elements, map values and the fields of a subtype's value.
    let mut r = repl();
    eval(&mut r, "type P(x: Int)");
    eval(&mut r, "fn show(p: P) -> Str { \"p{p.x}\" }");
    eval(
        &mut r,
        "fn equals(a: P, b: P) -> Bool { a.x % 10 == b.x % 10 }",
    );
    eval(&mut r, "fn hash(p: P) -> Int { p.x % 10 }");
    eval(
        &mut r,
        "fn compare(a: P, b: P) -> Ordering { compare(a.x % 10, b.x % 10) }",
    );
    eval(&mut r, "type Pair(a: P, b: Int)");
    eval(&mut r, "type Shape(name: Str)");
    eval(&mut r, "type Circle(..Shape, centre: P)");
    eval(&mut r, "type Tree(label: P, kids: List[Tree])");
    assert_eq!(eval(&mut r, "[P(x: 1), P(x: 2)]"), "[p1, p2]\n");
    assert_eq!(
        eval(&mut r, "Pair(a: P(x: 3), b: 4)"),
        "Pair(a: p3, b: 4)\n"
    );
    assert_eq!(eval(&mut r, "(q: P(x: 9), r: 1)"), "(q: p9, r: 1)\n");
    assert_eq!(eval(&mut r, "[\"a\": P(x: 1)]"), "[\"a\": p1]\n");
    assert_eq!(eval(&mut r, "[[1, 2; 3, 4]]"), "[[1, 2; 3, 4]]\n");
    assert_eq!(
        eval(&mut r, "\"{[Circle(name: \"c\", centre: P(x: 5))]}\""),
        "\"[Circle(name: \\\"c\\\", centre: p5)]\"\n"
    );
    assert_eq!(
        eval(
            &mut r,
            "Tree(label: P(x: 1), kids: [Tree(label: P(x: 2), kids: [])])"
        ),
        "Tree(label: p1, kids: [Tree(label: p2, kids: [])])\n"
    );
    eval(&mut r, "fn shape(s: Shape) -> Shape { s }");
    assert_eq!(
        eval(&mut r, "shape(Circle(name: \"c\", centre: P(x: 5)))"),
        "Circle(name: \"c\", centre: p5)\n"
    );
    assert_eq!(eval(&mut r, "[P(x: 1)] == [P(x: 11)]"), "True\n");
    assert_eq!(eval(&mut r, "[P(x: 1)] == [P(x: 12)]"), "False\n");
    assert_eq!(eval(&mut r, "[P(x: 1)] == [P(x: 1), P(x: 1)]"), "False\n");
    assert_eq!(
        eval(&mut r, "Pair(a: P(x: 3), b: 4) == Pair(a: P(x: 13), b: 4)"),
        "True\n"
    );
    assert_eq!(
        eval(&mut r, "Pair(a: P(x: 3), b: 4) == Pair(a: P(x: 13), b: 5)"),
        "False\n"
    );
    assert_eq!(
        eval(&mut r, "[\"a\": P(x: 1)] == [\"a\": P(x: 21)]"),
        "True\n"
    );
    assert_eq!(
        eval(&mut r, "[\"a\": P(x: 1)] == [\"b\": P(x: 1)]"),
        "False\n"
    );
    assert_eq!(
        eval(
            &mut r,
            "hash(Pair(a: P(x: 3), b: 4)) == hash(Pair(a: P(x: 23), b: 4))"
        ),
        "True\n"
    );
    assert_eq!(eval(&mut r, "compare([P(x: 1)], [P(x: 12)])"), "Less\n");
    assert_eq!(eval(&mut r, "compare([P(x: 3)], [P(x: 12)])"), "Greater\n");
    assert_eq!(
        eval(&mut r, "compare([P(x: 1)], [P(x: 11), P(x: 0)])"),
        "Less\n"
    );
    assert_eq!(eval(&mut r, "compare([P(x: 1)], [P(x: 11)])"), "Equal\n");
    // Members compare in the order the union is written.
    eval(&mut r, "fn either(x: Str | P) -> Str | P { x }");
    assert_eq!(eval(&mut r, "either(P(x: 4))"), "p4\n");
    assert_eq!(
        eval(&mut r, "compare(either(P(x: 4)), either(\"x\"))"),
        "Greater\n"
    );
    assert_eq!(
        eval(&mut r, "either(P(x: 4)) == either(P(x: 14))"),
        "True\n"
    );
}
