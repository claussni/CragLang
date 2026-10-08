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

extern crate crag_db as salsa;

use std::sync::atomic::{AtomicUsize, Ordering};

use crag_db::{Db, RootDatabase, Setter};
use crag_hir::{ItemKind, ModuleId, Owner, Program, SourceFile, lower_body, owners};
use crag_types::{body_types, module_type_errors};

const PRELUDE: &str = r#"pub type Int
pub type Int8
pub type Float
pub type Fixed[S]
pub type Str
pub type CodePoint
pub type Bytes
pub type List[T]
pub type Map[K, V]
pub type Set[T]
pub type Lazy[T]
pub type True
pub type False
pub type Bool = True | False
pub type Empty[T]
pub type Option[T] = T | Empty[T]
pub type Less
pub type Equal
pub type Greater
pub type Ordering = Less | Equal | Greater
pub type Range[T](first: T, last: T)
pub type RangeFrom[T](first: T)
pub fn add(a: Int, b: Int) -> Int
pub fn add(a: Int8, b: Int8) -> Int8
pub fn add(a: Float, b: Float) -> Float
pub fn add(a: Fixed[2], b: Fixed[2]) -> Fixed[2]
pub fn subtract(a: Int, b: Int) -> Int
pub fn multiply(a: Int, b: Int) -> Int
pub fn multiply(a: Float, b: Float) -> Float
pub fn negate(a: Int) -> Int
pub fn negate(a: Int8) -> Int8
pub fn negate(a: Fixed[2]) -> Fixed[2]
pub fn equals(a: Int, b: Int) -> Bool
pub fn equals(a: Str, b: Str) -> Bool
pub fn lessThan(a: Int, b: Int) -> Bool
pub fn size(xs: List[Int]) -> Int
pub fn size(s: Str) -> Int
pub fn map[T, U](xs: List[T], f: (T) -> U) -> List[U]
pub fn slice(xs: List[Int], r: Range[Int]) -> List[Int]
pub fn draw(r: Range[Int]) -> Int
pub fn draw(r: Range[Int8]) -> Int8
"#;

struct Checked {
    /// Each owner's named bindings with their types, as `name: Type`.
    bindings: Vec<String>,
    /// Each error as ``text`: message``.
    errors: Vec<String>,
}

fn setup(db: &RootDatabase, text: &str) -> (Program, ModuleId, ModuleId) {
    let core = ModuleId::new(
        db,
        "std.core".to_string(),
        SourceFile::new(db, PRELUDE.to_string()),
    );
    let module = ModuleId::new(db, "app".to_string(), SourceFile::new(db, text.to_string()));
    (Program::new(db, vec![core, module]), core, module)
}

fn check(text: &str) -> Checked {
    let db = RootDatabase::new();
    let (program, core, module) = setup(&db, text);
    let mut bindings = Vec::new();
    for owner in owners(&db, module) {
        if matches!(owner, Owner::Item(item) if *item.kind(&db) == ItemKind::Type) {
            continue;
        }
        let body = &lower_body(&db, program, owner).body;
        let types = body_types(&db, program, owner);
        let mut line = Vec::new();
        for (i, binding) in body.bindings.iter().enumerate() {
            if let Some(name) = binding.name {
                let ty = types.bindings[i].map_or("?".into(), |t| t.display(&db));
                line.push(format!("{}: {ty}", name.text(&db)));
            }
        }
        if let Some(result) = types.result {
            line.push(format!("-> {}", result.display(&db)));
        }
        bindings.push(line.join(", "));
    }
    let syntax = crag_hir::parse(&db, *module.file(&db))
        .errors
        .iter()
        .map(|e| {
            let snippet = &text[e.range.start as usize..e.range.end as usize];
            format!("`{snippet}`: {}", e.message)
        });
    let errors = syntax
        .chain(
            module_type_errors(&db, program, module)
                .into_iter()
                .map(|(owner, error)| {
                    let map = &lower_body(&db, program, owner).source_map;
                    let range = error.site.range(map).unwrap_or(0..0);
                    let snippet = &text[range.start as usize..range.end as usize];
                    format!("`{snippet}`: {}", error.kind.message(&db))
                }),
        )
        .collect();
    // The prelude itself must check.
    let prelude: Vec<String> = module_type_errors(&db, program, core)
        .into_iter()
        .map(|(_, e)| e.kind.message(&db))
        .collect();
    assert_eq!(prelude, Vec::<String>::new());
    Checked { bindings, errors }
}

fn ok(text: &str) -> Vec<String> {
    let checked = check(text);
    assert_eq!(checked.errors, Vec::<String>::new());
    checked.bindings
}

fn errors(text: &str) -> Vec<String> {
    check(text).errors
}

#[test]
fn literals_take_their_type_from_the_context() {
    assert_eq!(
        ok(
            "fn f(x: Int8) -> Fixed[2] {\n  let a = 1 + 2\n  let b: Int8 = -128\n  let c = x + 1\n  let d = 1.5\n  let e: Fixed[2] = 19.99\n  e + 0.01\n}"
        ),
        ["x: Int8, a: Int, b: Int8, c: Int8, d: Float, e: Fixed[2], -> Fixed[2]"]
    );
    assert_eq!(
        errors("fn f() {\n  let a: Int8 = 128\n  let b: Fixed[2] = 1.005\n  let c: Str = 1\n}"),
        [
            "`128`: the literal does not fit Int8",
            "`1.005`: the literal does not fit Fixed[2]",
            "`1`: expected Str, found Int",
        ]
    );
}

#[test]
fn records_are_built_by_name_and_read_by_field() {
    let text = "type Point(x: Int, y: Int = 0)
type Shape(pos: Point)
type Circle(..Shape, r: Float)
fn f(c: Circle) -> Shape {
  let p = Point(x: 1)
  let q = Point(..p, y: 2)
  let s = Shape(pos: q)
  let r = c.r
  let a = (y: 2, x: 1)
  let b: (x: Int, y: Int) = a
  let n = c.pos.x + b.x
  let Point(i, j) = p
  let (x, y) = a
  c
}";
    assert_eq!(
        ok(text),
        [
            "c: Circle, p: Point, q: Point, s: Shape, r: Float, a: (x: Int, y: Int), \
          b: (x: Int, y: Int), n: Int, i: Int, j: Int, x: Int, y: Int, -> Shape"
        ]
    );
    let text = "type Point(x: Int, y: Int = 0)
fn f(p: Point) {
  let a = Point(y: 1)
  let b = Point(x: 1, z: 2)
  let c = Point(x: 1, x: 2)
  let d = Point(x: \"one\")
  let e = p.z
  let g: Point = (x: 1, y: 2)
}";
    assert_eq!(
        errors(text),
        [
            "`Point(y: 1)`: the field `x` is missing",
            "`2`: there is no field `z`",
            "`2`: the field `x` is given twice",
            "`\"one\"`: expected Int, found Str",
            "`p.z`: Point has no field `z`",
            "`(x: 1, y: 2)`: expected Point, found (x: Int, y: Int)",
        ]
    );
}

#[test]
fn subtypes_spread_their_parents() {
    let text = "type Shape(pos: Int)
type Circle(..Shape, r: Float)
type Other(pos: Int)
fn area(s: Shape) -> Int { s.pos }
fn norm(p: (pos: Int, ..)) -> Int { p.pos }
fn f(c: Circle, o: Other) {
  let a = area(c)
  let b = norm(c)
  let d = norm(o)
  let e = area(o)
  let g: (pos: Int) = c
  let h: (Circle) -> Int = area
  let i: (Shape) -> Int = { k: Circle -> 1 }
  let j = norm((pos: 1, extra: 2))
}";
    assert_eq!(
        errors(text),
        [
            "`o`: expected Shape, found Other",
            "`c`: expected (pos: Int), found Circle",
            "`Circle`: expected Shape, found Circle",
        ]
    );
}

#[test]
fn calls_resolve_by_arguments_names_and_expected_type() {
    let text = "type Options(width: Int, height: Int = 1)
fn parse(s: Str) -> Int { 1 }
fn parse(s: Str) -> Float { 1.0 }
fn clamp(x: Int, min: Int = 0, max: Int = 100) -> Int { x }
fn layout(o: Options) -> Int { o.width }
fn twice(f: (Int) -> Int, x: Int) -> Int { f(f(x)) }
fn inc(x: Int) -> Int { x + 1 }
fn f(s: Str) {
  let a: Int = parse(s)
  let b = Int.parse(s)
  let c = Float.parse(s)
  let d = clamp(5, max: 10)
  let e = layout(width: 3)
  let g = s.size
  let h = s.size()
  let i = twice({ x -> x * 2 }, 1)
  let j = twice(inc, 2)
  let k = twice(_ + 1, 3)
  let l = 1.5 * 2.0
}";
    assert_eq!(
        ok(text),
        [
            "s: Str, -> Int",
            "s: Str, -> Float",
            "x: Int, min: Int, max: Int, -> Int",
            "o: Options, -> Int",
            "f: (Int) -> Int, x: Int, -> Int",
            "x: Int, -> Int",
            "s: Str, a: Int, b: Int, c: Float, d: Int, e: Int, g: Int, h: Int, x: Int, \
             i: Int, j: Int, k: Int, l: Float, -> ()",
        ]
    );
    let text = "fn parse(s: Str) -> Int { 1 }
fn parse(s: Str) -> Float { 1.0 }
fn clamp(x: Int, max: Int = 100) -> Int { x }
fn f(s: Str) {
  let a = parse(s)
  let b = clamp(\"x\")
  let c = clamp(1, min: 0)
  let d = clamp()
  let e = size(1.5)
  let g = s.length
  let h = 3(1)
  let i = clamp(1, 2, 3)
}";
    assert_eq!(
        errors(text),
        [
            "`parse(s)`: the call of `parse` fits 2 functions",
            "`\"x\"`: expected Int, found Str",
            "`0`: there is no parameter `min`",
            "`clamp()`: the argument `x` is missing",
            "`size(1.5)`: no function `size` takes (Float)",
            "`s.length`: Str has no field `length`",
            "`3(1)`: Int cannot be called",
            "`clamp(1, 2, 3)`: expected 2 arguments, found 3",
        ]
    );
}

#[test]
fn branches_join_into_unions() {
    let text = "type NotFound
type Shape = Circle | Rect
type Round(r: Float)
type Circle(..Round)
type Rect(w: Float, h: Float)
fn find(k: Int) -> Int | NotFound {
  if k == 0 { NotFound } else { k }
}
fn guess(k: Int) {
  if k == 0 { NotFound } else { k }
}
fn area(s: Shape) -> Float {
  case s {
    Circle(r:) -> r * r
    r: Rect -> r.w * r.h
  }
}
fn wide(x: Circle | Int) -> Float {
  case x {
    s: Round -> s.r
    n: Int -> 2.0
  }
}
fn get(m: Map[Str, Int], k: Str) -> Int {
  case m[k] {
    n: Int -> n
    Empty -> 0
  }
}
fn f(xs: List[Int]) {
  let a: Option[Int] = Empty
  let b = [1, 2, 3]
  let c: List[Float] = [1, 2.5]
  let d = [\"a\": 1]
  let e = case xs {
    [first, ..rest] -> rest
    [] -> xs
  }
  let ok = True
}";
    assert_eq!(
        ok(text),
        [
            "k: Int, -> Int | NotFound",
            "k: Int, -> Int | NotFound",
            "s: Circle | Rect, r: Float, r: Rect, -> Float",
            "x: Circle | Int, s: Circle, n: Int, -> Float",
            "m: Map[Str, Int], k: Str, n: Int, -> Int",
            "xs: List[Int], a: Empty[Int] | Int, b: List[Int], c: List[Float], \
             d: Map[Str, Int], first: Int, rest: List[Int], e: List[Int], ok: True, -> ()",
        ]
    );
    let text = "type NotFound
type Error
type LookupError(..Error)
type Missing(..LookupError)
fn f(x: Int | NotFound) {
  let a: Missing | LookupError = Missing()
  let b = case x {
    s: Str -> 1
    _ -> 2
  }
  let c = if x { 1 } else { 2 }
  let d = []
  let e: Option[Int] = Empty[Str]
}";
    assert_eq!(
        errors(text),
        [
            "`Missing | LookupError`: Missing is already part of LookupError",
            "`Str`: a Str pattern never matches a Int | NotFound",
            "`x`: expected False | True, found Int | NotFound",
            "`[]`: the type cannot be inferred here; write it",
            "`Empty[Str]`: expected Empty[Int] | Int, found Empty[Str]",
        ]
    );
}

#[test]
fn statements_and_success_types() {
    let text = "fn total(xs: List[Int]) -> Int {
  var sum = 0
  for x in xs { sum = sum + x }
  for i in 1..3 { sum = sum + i }
  for (key, value) in [\"a\": 1] { sum = sum + value }
  sum
}
fn sign(x: Int) {
  if x < 0 { return -1 }
  1
}
fn depth(n: Int) -> Int {
  fn go(k: Int) -> Int { if k == 0 { 0 } else { go(k - 1) + 1 } }
  go(n)
}
fn first(xs: List[Int]) -> Int {
  let [x, ..] = xs else { return 0 }
  x
}
let limit = sign(3) + 1
";
    assert_eq!(
        ok(text),
        [
            "xs: List[Int], sum: Int, x: Int, i: Int, key: Str, value: Int, -> Int",
            "x: Int, -> Int",
            "n: Int, go: (Int) -> Int, k: Int, -> Int",
            "xs: List[Int], x: Int, -> Int",
            "limit: Int, -> Int",
        ]
    );
    let text = "fn ping(n: Int) { pong(n) }
fn pong(n: Int) { ping(n) }
fn f(xs: List[Int]) -> Str {
  var n = 0
  n = \"x\"
  for x in 3 { }
  let [y] = xs else { 0 }
  return 1
}
let a = b
let b = a
";
    assert_eq!(
        errors(text),
        [
            "`pong(n)`: `pong` is recursive, so it must state its success type",
            "`ping(n)`: `ping` is recursive, so it must state its success type",
            "`\"x\"`: expected Int, found Str",
            "`3`: Int cannot be iterated",
            "`{ 0 }`: the `else` of a `let … else` must leave",
            "`1`: expected Str, found Int",
            "`b`: the value `b` depends on itself",
            "`a`: the value `a` depends on itself",
        ]
    );
}

#[test]
fn ranges_are_increasing_sequences_of_discrete_values() {
    let text = "distinct type Grade(rank: Int)
fn compare(a: Grade, b: Grade) -> Ordering { Less }
fn next(g: Grade) -> Grade { Grade(rank: g.rank + 1) }
fn f(xs: List[Int], n: Int8, lo: Grade, hi: Grade, p: Fixed[2]) {
  let a = 1..3
  let b = 1..n
  let c: RangeFrom[Int8] = (-1..)
  let d = xs.slice(0..1)
  let e = draw(1..6)
  let g: Int8 = draw(1..6)
  for c in 'a'..'e' { }
  for x in a { }
  for y in lo..hi { }
  let k = case n {
    1..5 -> 1
    _ -> 2
  }
  let m = 0.00..2.00
  let o = -0.50..p
  let q: Range[Fixed[2]] = 0..1
  for z in 0.0..0.5 { }
  let t = case p {
    0.00..9.99 -> 1
    _ -> 2
  }
}";
    assert_eq!(
        ok(text),
        [
            "a: Grade, b: Grade, -> Equal | Greater | Less",
            "g: Grade, -> Grade",
            "xs: List[Int], n: Int8, lo: Grade, hi: Grade, p: Fixed[2], a: Range[Int], b: Range[Int8], \
             c: RangeFrom[Int8], d: List[Int], e: Int, g: Int8, c: CodePoint, x: Int, \
             y: Grade, k: Int, m: Range[Fixed[2]], o: Range[Fixed[2]], q: Range[Fixed[2]], \
             z: Fixed[1], t: Int, -> ()",
        ]
    );
    let text = "type Grade(rank: Int)
fn f(x: Float, g: Grade, p: Fixed[2]) {
  let a = x..2.5
  let b = g..g
  let c = 3..1
  let d = 1..\"z\"
  let e = case x {
    1.0..2.0 -> 1
    _ -> 2
  }
  let h = case 3 {
    5..1 -> 1
    _ -> 2
  }
  let i = 0.0..2.00
  let j = 0.00..2.0
  let k = 0.5..p
  let l = 2.50..-1.00
  let m = case p {
    0.0..1.00 -> 1
    2.00..1.00 -> 2
    _ -> 3
  }
}";
    assert_eq!(
        errors(text),
        [
            "`x..2.5`: Float is not Discrete, so it forms no range",
            "`g..g`: Grade is not Discrete, so it forms no range",
            "`3..1`: the range decreases; its first end must not exceed its last",
            "`\"z\"`: expected Int, found Str",
            "`1.0..2.0`: Float is not Discrete, so it forms no range",
            "`5..1`: the range decreases; its first end must not exceed its last",
            "`2.00`: expected Fixed[1], found Fixed[2]",
            "`2.0`: expected Fixed[2], found Fixed[1]",
            "`0.5`: expected Fixed[2], found Fixed[1]",
            "`2.50..-1.00`: the range decreases; its first end must not exceed its last",
            "`0.0..1.00`: expected Fixed[2], found Fixed[1]",
            "`2.00..1.00`: the range decreases; its first end must not exceed its last",
        ]
    );
}

#[test]
fn type_declarations() {
    let text = "type A = B
type B = A
type Pair[T](left: T, right: T)
type Tree(left: Tree | Leaf, right: Tree | Leaf)
type Leaf
type Bad(x: Int, x: Str)
type Money(amount: Fixed[2], note: Str = 1)
fn f(p: Pair[Int], q: Pair, r: Fixed[Int], t: Tree) -> Int {
  p.left + p.right
}";
    assert_eq!(
        errors(text),
        [
            "`B`: the alias refers to itself",
            "`A`: the alias refers to itself",
            "`Str`: the field `x` is given twice",
            "`1`: expected Str, found Int",
            "`Pair`: expected 1 type arguments, found 0",
            "`Fixed[Int]`: `Fixed` takes a number of digits, other types a type",
        ]
    );
}

#[test]
fn not_yet_supported_is_reported() {
    let text = "fn f(xs: List[Int]) {
  let a = xs.map { x -> x }
  ref r = 1
}";
    assert_eq!(
        errors(text),
        [
            "`xs.map { x -> x }`: calls of generic functions are not supported yet",
            "`r`: `ref` and `ext` bindings are not supported yet",
        ]
    );
}

/// A query that reads the types of a body and counts its runs.
static RUNS: AtomicUsize = AtomicUsize::new(0);

#[crag_db::tracked]
fn error_count<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> usize {
    RUNS.fetch_add(1, Ordering::SeqCst);
    body_types(db, program, owner).errors.len()
}

#[test]
fn callers_are_not_rechecked_while_a_success_type_stays() {
    let mut db = RootDatabase::new();
    let text = "fn helper() { 1 }\nfn user() -> Int { helper() + 1 }\n";
    let (program, _, module) = setup(&db, text);
    // `user`, looked up again after every edit.
    let runs = |db: &RootDatabase| {
        error_count(db, program, owners(db, module)[1]);
        RUNS.load(Ordering::SeqCst)
    };
    let start = runs(&db);
    let edit = |db: &mut RootDatabase, text: String| {
        let file = *module.file(db);
        file.set_text(db).to(text);
    };
    edit(&mut db, text.replace("{ 1 }", "{ 40 + 2 }"));
    assert_eq!(runs(&db), start, "`helper` still returns an Int");
    edit(&mut db, text.replace("{ 1 }", "{ \"one\" }"));
    assert_eq!(runs(&db), start + 1, "`helper` returns a Str now");
}

const FRAGMENTS: &[&str] = &[
    "\"", "{", "}", "(", ")", "[", "]", "_", "\n", ".", "..", "else", "x", " ", "+", "->", ",",
    "1", "1.5", "=", "let", "case", "if", "{ x -> }", "?.", ":", "|", "var", "fn", "pass", "Point",
    "Empty", "-", "return", "\"{a}\"",
];

/// A small deterministic generator, so failures reproduce.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: usize) -> usize {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        (self.0 % n as u64) as usize
    }
}

#[test]
fn broken_code_types_without_panicking() {
    let base = r#"type Point(x: Int, y: Int = 0)
type Shape = Point | Empty[Int]
fn s(pairs: List[Int], p: Point, m: Map[Str, Int]) -> Int {
  var total = 0
  for v in pairs { total = total + v }
  let [a, ..] = pairs else { return 0 }
  let q = Point(..p, x: 2)
  let o: Option[Int] = m["k"]
  case o {
    n: Int where n < 10 -> n
    Empty -> -1
  }
  fn go(k: Int) -> Int { if k == 0 { 0 } else { go(k - 1) } }
  let f = { z: Int -> z * 2 }
  f(q.x) + go(a) + "s".size
}
let limit = s([1], Point(x: 1), ["a": 1])
test "t" { s([], Point(x: 1, y: 2), ["a": 1]) }
"#;
    assert_eq!(check(base).errors, Vec::<String>::new());
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    for _ in 0..300 {
        let mut text = base.to_string();
        for _ in 0..rng.below(4) + 1 {
            let mut start = rng.below(text.len() + 1);
            while !text.is_char_boundary(start) {
                start -= 1;
            }
            let mut end = (start + rng.below(6)).min(text.len());
            while !text.is_char_boundary(end) {
                end -= 1;
            }
            let insert = FRAGMENTS[rng.below(FRAGMENTS.len())];
            text.replace_range(start..end, insert);
        }
        let db = RootDatabase::new();
        let (program, _, module) = setup(&db, &text);
        for (owner, error) in module_type_errors(&db, program, module) {
            let map = &lower_body(&db, program, owner).source_map;
            assert!(error.site.range(map).is_some(), "{text:?}");
            error.kind.message(&db);
        }
        for owner in owners(&db, module) {
            let body = &lower_body(&db, program, owner).body;
            let types = body_types(&db, program, owner);
            assert_eq!(types.exprs.len(), body.exprs.len(), "{text:?}");
            assert_eq!(types.pats.len(), body.pats.len(), "{text:?}");
        }
    }
}
