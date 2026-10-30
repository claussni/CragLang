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

//! Flat layouts as `:layout` shows them (Implementation Plan §11.10.10):
//! the examples of Compiler Architecture §A11.4.1 to §A11.4.6 have the
//! sizes stated there.

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

fn eval(r: &mut Repl, text: &str) -> String {
    match r.eval_input(text) {
        Ok(output) => output.render(),
        Err(errors) => errors,
    }
}

/// A session with the types of the examples.
fn session(definitions: &[&str]) -> Repl {
    let mut r = repl();
    for d in definitions {
        assert_eq!(eval(&mut r, d), "", "{d}");
    }
    r
}

fn layout(r: &mut Repl, ty: &str) -> String {
    eval(r, &format!(":layout {ty}"))
}

#[test]
fn single_values_and_their_unions() {
    let mut r = session(&[]);
    assert_eq!(
        layout(&mut r, "Int"),
        "Int: Immediate, 8 bytes, aligned to 8\n"
    );
    // A local tag before the payload; the tag past the last is the niche.
    assert_eq!(
        layout(&mut r, "Option[Int16]"),
        "Option[Int16]: Plain, 4 bytes, aligned to 2
  tag           offset 0, 1 byte
  Int16         tag 0, offset 2, 2 bytes
  Empty[Int16]  tag 1
  niche         2 at offset 0
"
    );
    assert_eq!(
        layout(&mut r, "Bool"),
        "Bool: Immediate, 1 byte, aligned to 1
  tag    offset 0, 1 byte
  False  tag 0
  True   tag 1
  niche  2 at offset 0
"
    );
    assert_eq!(
        layout(&mut r, "Str | Int"),
        "Str | Int: Inline, 24 bytes, aligned to 8
  tag       offset 0, 1 byte
  Int       tag 0, offset 8, 8 bytes
  Str       tag 1, offset 8, 16 bytes
  niche     2 at offset 0
  pointers  text at 8 if the tag at 0 is 1
"
    );
    assert_eq!(
        layout(&mut r, "(Int) -> Int"),
        "(Int) -> Int: Inline, 16 bytes, aligned to 8\n  pointers  environment at 8\n"
    );
    assert_eq!(layout(&mut r, "()"), "(): Zero, 0 bytes, aligned to 1\n");
}

#[test]
fn map_entries_and_list_elements() {
    let mut r = session(&[
        "type Stock(qty: Int32, reserved: Int32, onOrder: Bool)",
        "type Point(x: Float, y: Float)",
        "type Label(text: Str, at: Point)",
    ]);
    // With its `UInt32` key, an entry takes 16 bytes.
    assert_eq!(
        layout(&mut r, "Stock"),
        "Stock: Plain, 12 bytes, aligned to 4
  qty: Int32             offset 0, 4 bytes
  reserved: Int32        offset 4, 4 bytes
  onOrder: False | True  offset 8, bit 0
  niche                  bit 1 at offset 8
"
    );
    assert_eq!(
        layout(&mut r, "Point"),
        "Point: Plain, 16 bytes, aligned to 8
  x: Float  offset 0, 8 bytes
  y: Float  offset 8, 8 bytes
"
    );
    assert_eq!(
        layout(&mut r, "Label"),
        "Label: Inline, 32 bytes, aligned to 8
  at: Point  offset 0, 16 bytes
  text: Str  offset 16, 16 bytes
  pointers   text at 16
"
    );
    assert_eq!(
        layout(&mut r, "Map[UInt32, Stock]"),
        "Map[UInt32, Stock]: Boxed, a collection, whose size varies\n"
    );
    assert_eq!(
        layout(&mut r, "List[Point]"),
        "List[Point]: Boxed, a collection, whose size varies\n"
    );
}

#[test]
fn records_inline_narrow_and_pack() {
    let mut r = session(&[
        "type Point(x: Float, y: Float)",
        "type Glyph(code: CodePoint, size: Int, bold: Bool, italic: Bool, at: Point)
    where size >= 1 and size <= 255",
        "type Port = Int where this >= 1 and this <= 65535",
    ]);
    assert_eq!(
        layout(&mut r, "Glyph"),
        "Glyph: Plain, 24 bytes, aligned to 8
  at: Point             offset 0, 16 bytes
  code: CodePoint       offset 16, 4 bytes
  size: Int             offset 20, 1 byte as UInt8
  bold: False | True    offset 21, bit 0
  italic: False | True  offset 21, bit 1
  niche                 0 at offset 20
"
    );
    // `size` is never 0, so 0 is `Empty`.
    assert_eq!(
        layout(&mut r, "Option[Glyph]"),
        "Option[Glyph]: Plain, 24 bytes, aligned to 8
  Glyph         offset 0, 24 bytes
  Empty[Glyph]  0 at offset 20
"
    );
    assert_eq!(
        layout(&mut r, "Port"),
        "Port: Immediate, 2 bytes, aligned to 2
  stored as  UInt16
  niche      0 at offset 0
"
    );
    assert_eq!(
        layout(&mut r, "Option[Port]"),
        "Option[Port]: Plain, 2 bytes, aligned to 2
  Port         offset 0, 2 bytes
  Empty[Port]  0 at offset 0
"
    );
}

#[test]
fn grid_cells() {
    let mut r = session(&[
        "type Grass",
        "type Water",
        "type Rock",
        "type Sand",
        "type Terrain = Grass | Water | Rock | Sand",
        "type Tile(kind: Terrain, cost: UInt8, seen: Bool)",
    ]);
    assert_eq!(
        layout(&mut r, "Tile"),
        "Tile: Plain, 2 bytes, aligned to 1
  cost: UInt8                        offset 0, 1 byte
  kind: Grass | Rock | Sand | Water  offset 1, bits 0–1
  seen: False | True                 offset 1, bit 2
  niche                              bit 3 at offset 1
"
    );
    assert_eq!(
        layout(&mut r, "Grid[Tile]"),
        "Grid[Tile]: Boxed, a collection, whose size varies\n"
    );
}

#[test]
fn forced_boxes_name_their_reasons() {
    let mut r = session(&[
        "type Node(v: Int, next: Option[Node])",
        "type Triple(a: Str, b: Str, c: Str)",
        "distinct type Token(n: Int)\n  on Dispose closeToken\nfn closeToken(t: Token) -> () {}",
        "type Shape(sides: Int)\ntype Square(..Shape, side: Float)",
        "type Nest[T](inner: Option[Nest[List[T]]])",
        "type Even(odd: Option[Odd])\ntype Odd(even: Option[Even])",
        "type Holder(kid: Option[Kid])\ntype Kid(..Holder, age: Int)",
    ]);
    // Only the recursive edge is boxed, with null as `Empty`.
    assert_eq!(
        layout(&mut r, "Node"),
        "Node: Inline, 16 bytes, aligned to 8
  next: Empty[Node] | Node  offset 0, 8 bytes, boxed: it contains itself
  v: Int                    offset 8, 8 bytes
  pointers                  box at 0
"
    );
    assert_eq!(
        layout(&mut r, "Triple"),
        "Triple: Boxed, flat it would take 48 bytes and 3 managed pointers, more than 32 and 2\n"
    );
    assert_eq!(
        layout(&mut r, "Token"),
        "Token: Boxed, it has a lifecycle: a Dispose handler, is Secret, a CPtr or a runtime \
         object\n"
    );
    assert_eq!(
        layout(&mut r, "Ref[Int]"),
        "Ref[Int]: Boxed, it has a lifecycle: a Dispose handler, is Secret, a CPtr or a runtime \
         object\n"
    );
    assert_eq!(
        layout(&mut r, "Shape"),
        "Shape: Boxed, it may hold a subtype\n"
    );
    // A subtype lays out its parent's fields first.
    assert_eq!(
        layout(&mut r, "Square"),
        "Square: Plain, 16 bytes, aligned to 8
  sides: Int   offset 0, 8 bytes
  side: Float  offset 8, 8 bytes
"
    );
    assert_eq!(
        layout(&mut r, "Nest[Int]"),
        "Nest[Int]: Inline, 8 bytes, aligned to 8
  inner: Empty[Nest[List[Int]]] | Nest[List[Int]]  offset 0, 8 bytes, boxed: its fields unfold \
         into ever new types
  pointers                                         box at 0
"
    );
    // Each type of a cycle boxes its edge into it.
    // A parent's field that holds its subtype.
    assert_eq!(
        layout(&mut r, "Kid"),
        "Kid: Inline, 16 bytes, aligned to 8
  kid: Empty[Kid] | Kid  offset 0, 8 bytes, boxed: it contains itself
  age: Int               offset 8, 8 bytes
  pointers               box at 0
"
    );
    assert_eq!(
        layout(&mut r, "Even"),
        "Even: Inline, 8 bytes, aligned to 8
  odd: Empty[Odd] | Odd  offset 0, 8 bytes, boxed: it contains itself
  pointers               box at 0
"
    );
}

#[test]
fn what_has_no_layout() {
    let mut r = session(&[]);
    assert_eq!(layout(&mut r, ""), "error: :layout takes a type\n");
    assert_eq!(
        layout(&mut r, "Nope"),
        "error: `Nope` is not a type\n --> input:1:1\n  |\n1 | Nope\n  | ^^^^\n"
    );
    // The session is as it was.
    assert_eq!(eval(&mut r, "1 + 1"), "2\n");
}

#[test]
fn flat_values_pass_by_value() {
    // Records and unions pass to the parameters of functions and back in
    // storage form, with flat layouts on: narrowed integers, flag bits,
    // tags and niches converted.
    let mut r = session(&[
        "type Grass",
        "type Water",
        "type Rock",
        "type Sand",
        "type Terrain = Grass | Water | Rock | Sand",
        "type Tile(kind: Terrain, cost: UInt8, seen: Bool)",
        "type Point(x: Int, y: Int)",
        "type Glyph(code: CodePoint, size: Int, bold: Bool, italic: Bool, at: Point)
    where size >= 1 and size <= 255",
        "type Stock(qty: Int32, reserved: Int32, onOrder: Bool)",
        "type Small(a: Int8, b: Int16, c: UInt8, d: Float)",
        "type Label(text: Str, at: Point)",
        r#"fn tile(t: Tile) -> Str { "{t.kind} {t.cost} {t.seen} {t}" }"#,
        r#"fn glyph(g: Glyph) -> Str { "{g.code} {g.size} {g.bold} {g.italic} {g}" }"#,
        r#"fn stock(s: Stock) -> Str { "{s.qty - s.reserved} {s.onOrder}" }"#,
        r#"fn small(s: Small) -> Str { "{s.a} {s.b} {s.c} {s.d} {s}" }"#,
        r#"fn label(l: Label) -> Str { "{l.text} at {l.at.x}, {l.at.y}" }"#,
        "fn steps(p: Point, n: Int) -> Int {
  if n == 0 { p.x } else { steps(Point(x: p.x + p.y, y: p.y), n - 1) }
}",
        "fn make(a: Int) -> Point { Point(x: a, y: -a) }",
        "fn total(p: Point) -> Int { p.x * 10 + p.y }",
        "fn twice(a: Int) -> Int { let p = make(a)\n total(p) + total(p) }",
        "fn wrap(p: Point) -> List[Point] { [p, p] }",
        "type Spot(at: Option[Point], n: Int16)",
        r#"fn glyphs(g: Option[Glyph]) -> Str { "{g}" }"#,
        r#"fn tiles(t: Option[Tile], n: Int) -> Str { "{n} {t}" }"#,
        r#"fn points(p: Option[Point]) -> Str { "{p}" }"#,
        r#"fn shorts(n: Option[Int16]) -> Str { "{n}" }"#,
        r#"fn spots(s: Spot) -> Str { "{s.n} {s.at} {s}" }"#,
        "fn find(n: Int) -> Option[Point] { if n == 0 { Empty } else { Point(x: n, y: -n) } }",
        "fn bold(g: Glyph, b: Bool) -> Option[Glyph] { if b { Glyph(code: g.code, size: g.size, bold: True, italic: g.italic, at: g.at) } else { Empty } }",
        "fn spot(n: Int, k: Int16) -> Spot { Spot(at: find(n), n: k) }",
    ]);
    let cases = [
        (
            "tile(Tile(kind: Rock, cost: 200, seen: True))",
            "Rock 200 True Tile(kind: Rock, cost: 200, seen: True)",
        ),
        (
            "tile(Tile(kind: Water, cost: 0, seen: False))",
            "Water 0 False Tile(kind: Water, cost: 0, seen: False)",
        ),
        (
            "glyph(Glyph(code: 'é', size: 200, bold: False, italic: True, at: Point(x: -3, y: 4)))",
            "é 200 False True Glyph(code: 'é', size: 200, bold: False, italic: True, at: Point(x: -3, y: 4))",
        ),
        (
            "stock(Stock(qty: -7, reserved: 2147483000, onOrder: True))",
            "-2147483007 True",
        ),
        (
            "small(Small(a: -128, b: -300, c: 255, d: 1.5))",
            "-128 -300 255 1.5 Small(a: -128, b: -300, c: 255, d: 1.5)",
        ),
        (
            r#"label(Label(text: "a string longer than the inline bytes", at: Point(x: 1, y: -2)))"#,
            "a string longer than the inline bytes at 1, -2",
        ),
        // A tail call in a loop of 100000 turns passes its point by value.
        ("steps(Point(x: 0, y: 3), 100000)", "300000"),
        // A point a call returned in its box passes twice.
        ("twice(4)", "72"),
        // A parameter that escapes twice is boxed once.
        (
            "wrap(Point(x: 3, y: 4))",
            "[Point(x: 3, y: 4), Point(x: 3, y: 4)]",
        ),
        (
            "glyphs(Glyph(code: 'a', size: 1, bold: True, italic: False, at: Point(x: 1, y: 2)))",
            "Glyph(code: 'a', size: 1, bold: True, italic: False, at: Point(x: 1, y: 2))",
        ),
        ("glyphs(Empty)", "Empty"),
        (
            "tiles(Tile(kind: Sand, cost: 255, seen: True), 3)",
            "3 Tile(kind: Sand, cost: 255, seen: True)",
        ),
        ("tiles(Empty, 4)", "4 Empty"),
        ("points(Point(x: -1, y: 1))", "Point(x: -1, y: 1)"),
        ("points(Empty)", "Empty"),
        ("shorts(-32768)", "-32768"),
        ("shorts(Empty)", "Empty"),
        (
            "spots(Spot(at: Point(x: 5, y: 6), n: -2))",
            "-2 Point(x: 5, y: 6) Spot(at: Point(x: 5, y: 6), n: -2)",
        ),
        (
            "spots(Spot(at: Empty, n: 7))",
            "7 Empty Spot(at: Empty, n: 7)",
        ),
        ("find(0)", "Empty"),
        ("find(9)", "Point(x: 9, y: -9)"),
        (
            "bold(Glyph(code: 'z', size: 255, bold: False, italic: True, at: Point(x: 0, y: 0)), True)",
            "Glyph(code: 'z', size: 255, bold: True, italic: True, at: Point(x: 0, y: 0))",
        ),
        (
            "bold(Glyph(code: 'z', size: 255, bold: False, italic: True, at: Point(x: 0, y: 0)), False)",
            "Empty",
        ),
        ("spot(3, 30)", "Spot(at: Point(x: 3, y: -3), n: 30)"),
        ("spot(0, -30)", "Spot(at: Empty, n: -30)"),
    ];
    for (input, expected) in cases {
        let shown = eval(&mut r, input);
        assert_eq!(shown.trim_end().trim_matches('"'), expected, "{input}");
    }
}

#[test]
fn flat_fields_live_in_their_box() {
    // A record's box holds the flat records and unions of its fields in
    // their storage form: narrowed, packed, with tags and niches.
    let mut r = session(&[
        "type Point(x: Float, y: Float)",
        "type Glyph(code: CodePoint, size: Int, bold: Bool, italic: Bool, at: Point)
    where size >= 1 and size <= 255",
        "type Line(first: Glyph, rest: Option[Glyph], label: Str, count: Int)",
        "fn glyph(n: Int) -> Glyph { Glyph(code: 'A', size: n, bold: n == 200, italic: False, at: Point(x: 1.5, y: -2.0)) }",
        "fn line(n: Int) -> Line { Line(first: glyph(n), rest: if n == 1 { Empty } else { glyph(n - 1) }, label: \"a label made at {n}\", count: n) }",
        "fn lines(n: Int) -> List[Line] { [line(n), line(1)] }",
        "fn sizes(ls: List[Line]) -> Int { ls.fold(0) { t, l -> t + l.first.size + (case l.rest { Empty -> 0\n g: Glyph -> g.size }) } }",
    ]);
    assert_eq!(
        eval(&mut r, "line(200)"),
        "Line(first: Glyph(code: 'A', size: 200, bold: True, italic: False, \
         at: Point(x: 1.5, y: -2.0)), rest: Glyph(code: 'A', size: 199, bold: False, \
         italic: False, at: Point(x: 1.5, y: -2.0)), label: \"a label made at 200\", count: 200)\n"
    );
    assert_eq!(eval(&mut r, "line(1).rest"), "Empty\n");
    assert_eq!(
        eval(&mut r, "\"{line(200).first.size} {line(200).first.at.x}\""),
        "\"200 1.5\"\n"
    );
    assert_eq!(eval(&mut r, "sizes(lines(250))"), "500\n");
    assert_eq!(eval(&mut r, "line(7) == line(7)"), "True\n");
    assert_eq!(eval(&mut r, "line(7) == line(8)"), "False\n");
    let out = eval(&mut r, "line(256)");
    assert!(out.contains("size <= 255"), "{out}");
}

#[test]
fn flat_elements_live_in_their_collections() {
    // Lists, maps and grids hold flat records and unions in their storage
    // form, and the prelude's functions on them read and write it.
    let mut r = session(&[
        "type Point(x: Int, y: Int)",
        "type Glyph(code: CodePoint, size: Int, bold: Bool, italic: Bool, at: Point)
    where size >= 1 and size <= 255",
        "type Label(text: Str, at: Point)",
        "type Stock(qty: Int, reserved: Int, onOrder: Bool)",
        "type Grass",
        "type Water",
        "type Terrain = Grass | Water",
        "type Tile(kind: Terrain, cost: UInt8, seen: Bool)",
        "fn path(n: Int) -> List[Point] { (1..n).fold([]) { ps, i -> ps.append(Point(x: i, y: i * 2)) } }",
        "fn walk(n: Int) -> Int {
  var total = 0
  for p in path(n) {
    total = total + p.x + p.y
  }
  total
}",
        "fn glyphs(n: Int) -> List[Glyph] { (1..n).fold([]) { gs, i -> gs.append(Glyph(code: 'A', size: i, bold: i > 2, italic: False, at: Point(x: i, y: 0))) } }",
        "fn bold(n: Int) -> Int {
  let gs = glyphs(n).set(0, Glyph(code: 'B', size: 200, bold: True, italic: True, at: Point(x: 7, y: 8)))
  gs.fold(0) { t, g -> if g.bold { t + g.size + g.at.x } else { t } } * 10 + gs.drop(1).count()
}",
        "fn labels(n: Int) -> List[Label] { (1..n).fold([]) { ls, i -> ls.append(Label(text: \"{i} is a label long enough for a heap buffer\", at: Point(x: i, y: i))) } }",
        "fn stock() -> Map[Int, Stock] { [1001: Stock(qty: 40, reserved: 5, onOrder: False), 1002: Stock(qty: 0, reserved: 0, onOrder: True)] }",
        "fn ordered() -> Int { stock().set(1003, Stock(qty: 7, reserved: 1, onOrder: False)).values().fold(0) { t, s -> t + s.qty } }",
        "fn world(w: Int, h: Int) -> Grid[Tile] { grid(w, h, Tile(kind: Grass, cost: 1, seen: False)).set(1, 2, Tile(kind: Water, cost: 5, seen: True)) }",
    ]);
    assert_eq!(eval(&mut r, "walk(100)"), "15150\n");
    assert_eq!(
        eval(&mut r, "path(3)"),
        "[Point(x: 1, y: 2), Point(x: 2, y: 4), Point(x: 3, y: 6)]\n"
    );
    assert_eq!(
        eval(&mut r, "path(40).reverse()[0]"),
        "Point(x: 40, y: 80)\n"
    );
    assert_eq!(eval(&mut r, "bold(5)"), "2314\n");
    assert_eq!(
        eval(&mut r, "glyphs(2)"),
        "[Glyph(code: 'A', size: 1, bold: False, italic: False, at: Point(x: 1, y: 0)), \
         Glyph(code: 'A', size: 2, bold: False, italic: False, at: Point(x: 2, y: 0))]\n"
    );
    assert_eq!(eval(&mut r, "labels(3) == labels(3)"), "True\n");
    assert_eq!(eval(&mut r, "labels(2) < labels(3)"), "True\n");
    assert_eq!(
        eval(&mut r, "labels(2)[1]"),
        "Label(text: \"2 is a label long enough for a heap buffer\", at: Point(x: 2, y: 2))\n"
    );
    assert_eq!(
        eval(&mut r, "stock()[1001]"),
        "Stock(qty: 40, reserved: 5, onOrder: False)\n"
    );
    assert_eq!(eval(&mut r, "stock()[7]"), "Empty\n");
    assert_eq!(eval(&mut r, "ordered()"), "47\n");
    assert_eq!(
        eval(&mut r, "world(3, 2).column(2)"),
        "[Tile(kind: Grass, cost: 1, seen: False), Tile(kind: Water, cost: 5, seen: True)]\n"
    );
    assert_eq!(
        eval(&mut r, "world(3, 2).get(1, 2)"),
        "Tile(kind: Water, cost: 5, seen: True)\n"
    );
    assert_eq!(
        eval(
            &mut r,
            "fn maybe() -> List[Option[Point]] { [Point(x: 1, y: 2), Empty] }"
        ),
        ""
    );
    assert_eq!(eval(&mut r, "maybe()"), "[Point(x: 1, y: 2), Empty]\n");
    assert_eq!(eval(&mut r, "maybe()[0]"), "Point(x: 1, y: 2)\n");
}

#[test]
fn types_marked_flat_must_not_be_boxed() {
    let mut r = session(&["type Point(x: Int, y: Int)\n  is Flat"]);
    // A type too large, or one with a lifecycle, is an error that says
    // why.
    let big = eval(
        &mut r,
        "type Big(a: Int, b: Int, c: Int, d: Int, e: Int)\n  is Flat",
    );
    assert!(
        big.contains(
            "`Big` is marked `is Flat` but is boxed: flat it would take 40 bytes and 0 managed \
             pointers, more than 32 and 2"
        ),
        "{big}"
    );
    let key = eval(&mut r, "type Key(k: Int)\n  is Secret\n  is Flat");
    assert!(
        key.contains("`Key` is marked `is Flat` but is boxed: it has a lifecycle"),
        "{key}"
    );
    // A record that holds a list's box is flat itself.
    assert_eq!(eval(&mut r, "type Listed(items: List[Int])\n  is Flat"), "");
    // A generic type is checked at the instances the program names.
    assert_eq!(eval(&mut r, "type Pair[T](a: T, b: T)\n  is Flat"), "");
    assert_eq!(eval(&mut r, "fn small(p: Pair[Int]) -> Int { p.a }"), "");
    assert_eq!(eval(&mut r, "type Wide(a: Int, b: Int, c: Int)"), "");
    let wide = eval(&mut r, "fn wide(p: Pair[Wide]) -> Int { 0 }");
    assert!(
        wide.contains("`Pair[Wide]` is marked `is Flat` but is boxed: flat it would take 48 bytes"),
        "{wide}"
    );
}
