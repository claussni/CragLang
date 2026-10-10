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
pub distinct type Error
pub type Oks[X]
pub type Errs[X]
pub fn discard[X](x: X) -> () | Errs[X] prefix "~"
pub fn check[X](x: X) -> Option[Oks[X]] prefix "?"
pub fn expect[X](x: X) -> Oks[X] prefix "!!"
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
pub fn greaterThan(a: Int, b: Int) -> Bool
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
        if matches!(owner, Owner::Item(item) if matches!(*item.kind(&db), ItemKind::Type | ItemKind::Form))
        {
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
    // Lowering errors show as their debug form: a test expects none.
    let lowering = owners(&db, module)
        .into_iter()
        .flat_map(|owner| lower_body(&db, program, owner).errors.clone())
        .map(|e| format!("{e:?}"));
    let errors = syntax
        .chain(lowering)
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
            "`pong(n)`: this call makes `ping` and `pong` recursive, so `ping` and `pong` must \
             state their success types",
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
  for ch in 'a'..'e' { }
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
    -9.99..-0.01 -> 3
    _ -> 2
  }
}";
    assert_eq!(
        ok(text),
        [
            "a: Grade, b: Grade, -> Equal | Greater | Less",
            "g: Grade, -> Grade",
            "xs: List[Int], n: Int8, lo: Grade, hi: Grade, p: Fixed[2], a: Range[Int], b: Range[Int8], \
             c: RangeFrom[Int8], d: List[Int], e: Int, g: Int8, ch: CodePoint, x: Int, \
             y: Grade, k: Int, m: Range[Fixed[2]], o: Range[Fixed[2]], q: Range[Fixed[2]], \
             z: Fixed[1], t: Int, -> ()",
        ]
    );
    let text = "type Grade(rank: Int)
fn f(x: Float, g: Grade, p: Fixed[2], t: Int8) {
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
  let n = case t {
    -129 -> 1
    -1..-5 -> 2
    _ -> 3
  }
  let o = case p {
    -0.5..0.50 -> 1
    _ -> 2
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
            "`-129`: the literal does not fit Int8",
            "`-1..-5`: the range decreases; its first end must not exceed its last",
            "`-0.5..0.50`: expected Fixed[2], found Fixed[1]",
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
  fn local[T](x: T) -> T { x }
  ref r = 1
}";
    assert_eq!(
        errors(text),
        [
            "`local`: generic local functions are not supported yet",
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
fn case_arms_cover_every_value_once() {
    let text = "type Error(message: Str)
type LookupError(..Error)
type NotFound(..LookupError)
type Timeout(..Error, after: Int)
type Rejected(..Error, code: Int, reason: Str)
type Point(x: Int, y: Int)
fn f(r: Int | Error, b: Bool, t: Int8, c: CodePoint, s: Str, xs: List[Int], p: Point, o: Option[Int]) {
  let a = case r {
    n: Int -> 1
    NotFound -> 2
    Timeout(after:) -> after
    Rejected(code: 404, reason) -> 3
    Rejected(code, reason:) -> code
    _ -> 4
  }
  let d = case b {
    True -> 1
    False -> 2
  }
  let e = case t {
    1 | 2 -> 2
    0..127 -> 1
    _ -> 3
  }
  let g = case t {
    -128..-1 -> 0
    0 -> 1
    1..127 -> 2
  }
  let h = case c {
    '\\u{0}'..'\\u{d7ff}' -> 1
    '\\u{e000}'..'\\u{10ffff}' -> 2
  }
  let i = case s {
    \"a\" -> 1
    \"b\" -> 2
    _ -> 3
  }
  let j = case xs {
    [] -> 0
    [x] -> x
    [x, y, ..] -> y
  }
  let k = case p {
    Point(x: 0, y:) -> y
    Point(x:, y: 0) -> x
    Point(x:, y:) -> x + y
  }
  let l = case o {
    n: Int where n > 0 -> n
    n: Int -> 0
    Empty -> 1
  }
  let m = case (q: p, u: b) {
    (q: Point(x: 0), u: True) -> 1
    (q: _, u: False) -> 2
    (q: _, u: True) -> 3
  }
  let Point(x:, y:) = p
  for (key, value) in [\"a\": 1] { }
}";
    assert_eq!(check(text).errors, Vec::<String>::new());
    let text = "type Error(message: Str)
type LookupError(..Error)
type NotFound(..LookupError)
type Point(x: Int, y: Int)
fn f(r: Int | Error, b: Bool, t: Int8, c: CodePoint, s: Str, xs: List[Int], p: Point, o: Option[Int]) {
  let a = case r {
    n: Int -> 1
    LookupError -> 2
    NotFound -> 3
  }
  let d = case b {
    True -> 1
    True | False -> 2
    _ -> 3
  }
  let e = case t {
    1..5 -> 1
    3 -> 2
    6..127 -> 3
  }
  let g = case c {
    'a'..'z' -> 1
  }
  let h = case s {
    \"a\" -> 1
    \"a\" -> 2
  }
  let i = case xs {
    [] -> 0
    [x, y, ..] -> y
  }
  let j = case p {
    Point(x: 0, y:) -> y
    Point(x:, y: 0) -> x
  }
  let k = case o {
    n: Int where n > 0 -> n
    Empty -> 1
  }
  let Point(x: 1, y:) = p
  for [z] in [xs] { }
}";
    assert_eq!(
        errors(text),
        [
            "`NotFound`: the pattern is unreachable; earlier arms cover it",
            "`r`: the `case` does not cover `Error`",
            "`True`: the pattern is unreachable; earlier arms cover it",
            "`_`: the pattern is unreachable; earlier arms cover it",
            "`3`: the pattern is unreachable; earlier arms cover it",
            "`t`: the `case` does not cover `Int8.min..0`",
            "`c`: the `case` does not cover `'\\0'..'`'`",
            "`\"a\"`: the pattern is unreachable; earlier arms cover it",
            "`s`: the `case` does not cover `Str`",
            "`xs`: the `case` does not cover `[_]`",
            "`p`: the `case` does not cover `Point(x: Int.min..-1, y: Int.min..-1)`",
            "`o`: the `case` does not cover `Int`",
            "`Point(x: 1, y:)`: the pattern does not cover `Point(x: Int.min..0, y: _)`",
            "`[z]`: the pattern does not cover `[]`",
        ]
    );
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
    _ -> 10
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

#[test]
fn tests_narrow_bindings_where_they_hold() {
    let text = "type NotFound
type Timeout
type Error
type LookupError(..Error)
type Missing(..LookupError)
fn early(v: Int | NotFound) -> Int {
  if v is NotFound { return 0 }
  let a = v
  a + 1
}
fn both(v: Int | NotFound, w: Int | Str) {
  if v is Int and w is Int {
    let a = v
    let b = w
  } else {
    let c = v
  }
  if not (v is Int) or w is Str {
    let d = v
  } else {
    let e = v
    let g = w
  }
}
fn arms(r: Int | LookupError | Timeout) {
  case r {
    Missing -> { let a = r }
    Int where r < 5 -> { let b = r }
    Int -> { let c = r }
    _ -> { let d = r }
  }
}
fn after(r: Int | NotFound | Timeout) -> Int {
  case r {
    NotFound -> { return 0 }
    _ -> {}
  }
  let a = r
  if a is Timeout { return 1 }
  a
}
fn unwrap(o: Option[Int], r: Int | NotFound | Timeout) -> Int {
  let n: Int = o else {
    let e = o
    return 0
  }
  let m = o
  let k: Int = r else {
    let rest = r
    return 1
  }
  n + k
}
fn vars(x: Int | NotFound) {
  if x is NotFound { return }
  var v: Int | NotFound = x
  if v is NotFound { return }
  let a = v
  let f = { n: Int ->
    let q = v
    let y = x
    n
  }
  for i in [1, 2] {
    let b = v
    v = i
  }
  let c = v
  v = NotFound
  let d = v
}";
    assert_eq!(
        ok(text),
        [
            "v: Int | NotFound, a: Int, -> Int",
            "v: Int | NotFound, w: Int | Str, a: Int, b: Int, c: Int | NotFound, \
             d: Int | NotFound, e: Int, g: Int, -> ()",
            "r: Int | LookupError | Timeout, a: Missing, b: Int, c: Int, \
             d: LookupError | Timeout, -> ()",
            "r: Int | NotFound | Timeout, a: Int | Timeout, -> Int",
            "o: Empty[Int] | Int, r: Int | NotFound | Timeout, e: Empty[Int], n: Int, m: Int, \
             rest: NotFound | Timeout, k: Int, -> Int",
            "x: Int | NotFound, v: Int | NotFound, a: Int, n: Int, q: Int | NotFound, y: Int, \
             f: (Int) -> Int, i: Int, b: Int | NotFound, c: Int | NotFound, \
             d: Int | NotFound, -> ()",
        ]
    );
    let text = "type NotFound
fn f(x: Int | NotFound) {
  let a = x is Str
  let n: Str = x else { return }
}";
    assert_eq!(
        errors(text),
        [
            "`x is Str`: a Str pattern never matches a Int | NotFound",
            "`Str`: a Str pattern never matches a Int | NotFound",
        ]
    );
}

#[test]
fn errors_are_inferred_over_recursive_groups() {
    let text = "type NotFound(..Error)
type Expired(..Error)
type Session(user: Str)
fn session(id: Int) -> Session {
  if id == 0 { return NotFound() }
  if id == 1 { Expired() } else { Session(user: \"ada\") }
}
fn greet(id: Int) -> Str {
  case session(id) {
    Session -> \"hello\"
    Expired -> \"log in again\"
    pass
  }
}
fn count(n: Int) -> Int {
  if n == 0 { return NotFound() }
  down(n)
}
fn down(n: Int) -> Int {
  if n == 1 { return Expired() }
  count(n - 1)
}
fn deep(n: Int) -> Int {
  if n == 0 { return Expired() }
  case deep(n - 1) {
    k: Int -> k + 1
    pass
  }
}
fn plain(id: Int) {
  let s = session(id)
  let c = count(id)
  let d = deep(id)
  session(id)
}";
    assert_eq!(
        ok(text),
        [
            "id: Int, -> Expired | NotFound | Session",
            "id: Int, -> NotFound | Str",
            "n: Int, -> Expired | Int | NotFound",
            "n: Int, -> Expired | Int | NotFound",
            "n: Int, k: Int, -> Expired | Int",
            "id: Int, s: Expired | NotFound | Session, c: Expired | Int | NotFound, \
             d: Expired | Int, -> Expired | NotFound | Session",
        ]
    );
    let text = "type NotFound(..Error)
type Expired(..Error)
type Bad
fn session(id: Int) -> Int {
  if id == 0 { return NotFound() }
  if id == 1 { return Bad }
  Expired()
}
fn closed(id: Int) -> Int | NotFound {
  session(id)
}
fn stray(id: Int) -> Int {
  let x = case id {
    0 -> 1
    _ -> { pass }
  }
  x
}";
    assert_eq!(
        errors(text),
        [
            "`Bad`: expected Int, found Bad",
            "`{\n  session(id)\n}`: expected Int | NotFound, found Expired | Int | NotFound",
            "`pass`: `pass` stands only as the body of a `case` arm",
        ]
    );
}

/// Each generic call of the module, its function with type arguments and
/// slot fillings, as `name[Args] {fillings}`.
fn instances(text: &str) -> Vec<String> {
    fn show(db: &RootDatabase, i: &crag_types::Instance) -> String {
        let args: Vec<String> = i.args.iter().map(|t| t.display(db)).collect();
        let fillings: Vec<String> = i
            .fillings
            .iter()
            .map(|f| match f {
                crag_types::Filling::Function(f) if f.args.is_empty() => {
                    f.function.name(db).text(db).clone()
                }
                crag_types::Filling::Function(f) => show(db, f),
                crag_types::Filling::Slot(k) => format!("slot {k}"),
            })
            .collect();
        format!(
            "{}[{}] {{{}}}",
            i.function.name(db).text(db),
            args.join(", "),
            fillings.join(", ")
        )
    }
    let db = RootDatabase::new();
    let (program, _, module) = setup(&db, text);
    let mut out = Vec::new();
    for owner in owners(&db, module) {
        for (_, callee) in &body_types(&db, program, owner).callees {
            match callee {
                crag_types::Callee::Instance(i) => out.push(show(&db, i)),
                crag_types::Callee::Slot(k) => out.push(format!("slot {k}")),
                _ => {}
            }
        }
    }
    out
}

#[test]
fn generic_calls_infer_type_arguments_and_fill_slots() {
    let text = "type Shape(pos: Int)
type Circle(..Shape, r: Int)
type Point(x: Int, y: Int)
form Sizable[U] {
  size(u: U) -> Int
}
form Convert[A, B] {
  convert(a: A) -> B
}
form Measured[T] where Sizable[T] {}
fn size(p: Point) -> Int { p.x }
fn convert(n: Int) -> Str { \"n\" }
fn identity[T](x: T) -> T { x }
fn biggest[T: Sizable](a: T, b: T) -> T {
  if size(a) < size(b) { b } else { a }
}
fn measure(m: Measured) -> Int { m.size() }
fn pos[S: Shape](s: S) -> Int { s.pos }
fn keep[S: Shape](s: S) -> S { s }
fn apply[A, B](a: A, f: (A) -> B) -> B { f(a) }
fn twice[A: Sizable](a: A) -> Int { size(biggest(a, a)) }
fn conv[A, B](a: A) -> B where Convert[A, B] { convert(a) }
fn f(p: Point, c: Circle) {
  let a = identity(1)
  let b = identity(p)
  let d = biggest(p, p)
  let e = measure(p)
  let g = pos(c)
  let h = keep(c)
  let i = apply(2, { n -> n + 1 })
  let j: Str = conv(3)
  let k = identity[Int8](1)
  let l: (Int) -> Int = identity
  let m = twice(p)
  let o: Option[Int] = identity(Empty)
}";
    assert_eq!(
        ok(text),
        [
            "p: Point, -> Int",
            "n: Int, -> Str",
            "x: T, -> T",
            "a: T, b: T, -> T",
            "m: Measured, -> Int",
            "s: S, -> Int",
            "s: S, -> S",
            "a: A, f: (A) -> B, -> B",
            "a: A, -> Int",
            "a: A, -> B",
            "p: Point, c: Circle, a: Int, b: Point, d: Point, e: Int, g: Int, h: Circle, \
             n: Int, i: Int, j: Str, k: Int8, l: (Int) -> Int, m: Int, o: Empty[Int] | Int, -> ()",
        ]
    );
    assert_eq!(
        instances(text),
        [
            // In the generic bodies: `size` and `convert` through their
            // slots, and `biggest` with `twice`'s slot.
            "slot 0",
            "slot 0",
            "slot 0",
            "biggest[A] {slot 0}",
            "slot 0",
            "slot 0",
            "identity[Int] {}",
            "identity[Point] {}",
            "biggest[Point] {size}",
            "measure[Point] {size}",
            "pos[Circle] {}",
            "keep[Circle] {}",
            "apply[Int, Int] {}",
            "conv[Int, Str] {convert}",
            "identity[Int8] {}",
            "identity[Int] {}",
            "twice[Point] {size}",
            "identity[Empty[Int] | Int] {}",
        ]
    );
}

#[test]
fn bounds_and_forms_are_checked() {
    let text = "type Shape(pos: Int)
type Circle(..Shape, r: Int)
form Sizable[U] {
  size(u: U) -> Int
}
form Convert[A, B] {
  convert(a: A) -> B
}
fn size(c: Circle) -> Int { c.r }
fn size(c: Circle) -> Int8 { 1 }
fn biggest[T: Sizable](a: T, b: T) -> T { a }
fn pos[S: Shape](s: S) -> Int { s.pos }
fn conv[A, B](a: A) -> B where Convert[A, B] { convert(a) }
fn identity[T](x: T) -> T { x }
fn f(c: Circle, n: Int) {
  let a = biggest(n, n)
  let b = pos(n)
  let d = conv(n)
  let e = identity[Int, Int](n)
  let g = identity
}
fn hidden[T](x: T) -> Int { x.pos }
fn mixed[T: Sizable | Int](x: T) {}
fn noForm[T](x: T) where Int {}
form Wrong[T] where Shape {}";
    assert_eq!(
        errors(text),
        [
            "`biggest(n, n)`: Sizable[Int] does not hold: no visible function `size` has the type (Int) -> Int",
            "`pos(n)`: Int does not fit the bound Shape of `S`",
            "`conv(n)`: the type parameter `B` of `conv` cannot be inferred",
            "`identity[Int, Int](n)`: expected 1 type arguments, found 2",
            "`identity`: the type parameter `T` of `identity` cannot be inferred",
            "`x.pos`: T does not fit the bound Shape of `S`",
            "`Sizable | Int`: a bound unites forms or types, not both",
            "`Int`: Int is not a form",
            "`Shape`: Shape is not a form",
        ]
    );
}

#[test]
fn type_mapping_functions_map_errors() {
    let text = "type NotFound(..Error)
type Config(port: Int)
fn load(path: Str) -> Config {
  if path == \"\" { return NotFound() }
  Config(port: 80)
}
fn errs[X](x: X) -> Errs[X] { ??? }
fn f() {
  let a = ? load(\"a\")
  let b = !! load(\"b\")
  let c = ~ load(\"c\")
  let d = errs(load(\"d\"))
}";
    assert_eq!(
        ok(text),
        [
            "path: Str, -> Config | NotFound",
            "x: X, -> Errs[X]",
            "a: Config | Empty[Config], b: Config, c: () | NotFound, d: NotFound, -> ()",
        ]
    );
    let text = "type NotFound(..Error)
fn find(n: Int) -> Int | Empty[Int] {
  if n == 0 { return NotFound() }
  n
}
fn f() {
  let a = ? 1
  let b = !! 2
  let c = ? find(3)
}";
    assert_eq!(
        errors(text),
        [
            "`? 1`: `check` of a value that has no errors",
            "`!! 2`: `expect` of a value that has no errors",
            "`? find(3)`: `check` of a value that can be `Empty` would merge success and failure",
        ]
    );
}

#[test]
fn a_union_of_forms_needs_one_to_hold() {
    let text = "form Hash[T] {
  hash(x: T) -> Int
}
form Ordered[T] {
  compare(a: T, b: T) -> Ordering
}
form Keyable[T] = Hash[T] | Ordered[T]
type Point(x: Int)
type Label(s: Str)
fn hash(p: Point) -> Int { p.x }
fn compare(a: Label, b: Label) -> Ordering { Less }
fn key[K: Keyable](k: K) -> Int { hash(k) }
fn either[K: Hash | Ordered](k: K) -> Int { 2 }
fn f(p: Point, l: Label, i: Int) {
  let a = key(p)
  let b = key(l)
  let c = either(p)
  let d = either(i)
}";
    assert_eq!(
        errors(text),
        [
            // A union of forms gives no slots: which one holds is known only
            // for each type argument.
            "`k`: expected Point, found K",
            "`either(i)`: none of Hash[Int] | Ordered[Int] holds",
        ]
    );
}

#[test]
fn the_most_specific_overload_wins() {
    // §5.6.1: a concrete type beats a type parameter, a subtype its parent,
    // and a larger requirement set a smaller one. The result types tell
    // the candidates apart.
    let text = "form Show[T] {
  show(x: T) -> Str
}
form Hash[T] {
  hash(x: T) -> Int
}
type Shape(pos: Int)
type Circle(..Shape, r: Int)
type Point(x: Int)
fn show(n: Int) -> Str { \"i\" }
fn show(s: Str) -> Str { s }
fn show(p: Point) -> Str { \"p\" }
fn hash(p: Point) -> Int { 1 }
fn describe[T: Show](x: T) -> Str { \"A\" }
fn describe[T: Show](xs: List[T]) -> Int { 1 }
fn describe(xs: List[Int]) -> Float { 1.0 }
fn area(s: Shape) -> Int { 1 }
fn area(c: Circle) -> Float { 1.0 }
fn key[K: Show](k: K) -> Int { 1 }
fn key[K](k: K) -> Float where Show[K], Hash[K] { 1.0 }
fn f(c: Circle, s: Shape, n: Int, p: Point) {
  let a = describe(3)
  let b = describe([\"a\", \"b\"])
  let d = describe([1, 2])
  let e = area(c)
  let g = area(s)
  let h = key(n)
  let i = key(p)
  let j = c.area()
}";
    let bindings = ok(text);
    assert_eq!(
        bindings.last().unwrap(),
        "c: Circle, s: Shape, n: Int, p: Point, a: Str, b: Int, d: Float, e: Float, g: Int, \
         h: Int, i: Float, j: Float, -> ()"
    );
}

#[test]
fn incomparable_overloads_need_their_combination() {
    let text = "form Show[T] {
  show(x: T) -> Str
}
form Hash[T] {
  hash(x: T) -> Int
}
fn describe[T: Show](xs: List[T]) -> Str { \"B\" }
fn describe[T: Hash](xs: List[T]) -> Str { \"D\" }
fn lookup[K: Show](k: K) -> Int { 1 }
fn lookup[K: Hash](k: K) -> Int { 2 }
fn lookup[K](k: K) -> Int where Show[K], Hash[K] { 3 }";
    assert_eq!(
        errors(text),
        [
            "`describe`: this overload and an earlier `describe` take the same parameters with \
          incomparable bounds; add `fn describe[T](xs: List[T]) -> Str where Show[T], Hash[T]`"
        ]
    );
}

#[test]
fn candidates_of_several_modules_are_not_ranked() {
    // The prelude's `size(s: Str)` and this module's both fit.
    let text = "type Text(s: Str)
fn size(s: Str) -> Int { 1 }
fn size(t: Text) -> Int { 2 }
fn f(t: Text) {
  let a = size(\"a\")
  let b = size(t)
}";
    assert_eq!(
        errors(text),
        [
            "`size(\"a\")`: `size` has viable candidates from several modules (app, std.core); \
          import one of them selectively"
        ]
    );
}

#[test]
fn union_arguments_are_lifted_over_overloads() {
    // §4.6.1: with an overload for every member, a call dispatches on the
    // union's tag and gives the union of the chosen results.
    let text = "type Circle(r: Int)
type Rect(w: Int, h: Int)
fn area(c: Circle) -> Float { 1.0 }
fn area(r: Rect) -> Int { 1 }
fn mix(c: Circle, n: Int) -> Int { n }
fn mix(r: Rect, n: Int) -> Str { \"r\" }
fn pair(a: Circle, b: Circle) -> Int { 1 }
fn pair(a: Circle, b: Rect) -> Int { 2 }
fn pair(a: Rect, b: Circle | Rect) -> Str { \"x\" }
fn whole(s: Circle | Rect) -> Str { \"w\" }
fn whole(c: Circle) -> Int { 1 }
fn f(s: Circle | Rect, t: Circle | Rect, shapes: List[Circle | Rect]) {
  let a = area(s)
  let b = s.area()
  let c = mix(s, 1)
  let d = pair(s, t)
  let e = whole(s)
  let g: (Circle | Rect) -> Float | Int = area
  let h = shapes.map(area)
}";
    assert_eq!(
        ok(text).last().unwrap(),
        "s: Circle | Rect, t: Circle | Rect, shapes: List[Circle | Rect], a: Float | Int, \
         b: Float | Int, c: Int | Str, d: Int | Str, e: Str, g: (Circle | Rect) -> Float | Int, \
         h: List[Float | Int], -> ()"
    );
}

#[test]
fn lifting_needs_a_function_for_every_member() {
    let text = "type Circle(r: Int)
type Rect(w: Int, h: Int)
type Square(s: Int)
type Point(x: Int)
fn area(c: Circle) -> Float { 1.0 }
fn area(r: Rect) -> Float { 1.0 }
fn scale(c: Circle, k: Int) -> Int { 1 }
fn scale(r: Rect, k: Float) -> Int { 1 }
fn f(k: Circle | Square, q: Square | Point, s: Circle | Rect) {
  let a = area(k)
  let b = area(q)
  let c = scale(s, 2)
}";
    assert_eq!(
        errors(text),
        [
            "`area(k)`: no function `area` takes (Square), which union lifting needs for each \
             member",
            "`area(q)`: no function `area` takes (Point | Square)",
            "`scale(s, 2)`: lifted calls whose arguments typed by the context differ by member \
             are not supported yet",
        ]
    );
}

#[test]
fn recursive_groups_are_reported_once() {
    // §3.13.1: every member of a recursive group states its success type,
    // even where one written type would break the cycle; one diagnostic
    // names the members missing one, at the call that links them, and
    // calls of them report nothing more.
    let text = "fn depth(n: Int) { if n == 0 { 0 } else { depth(n - 1) + 1 } }
fn even(n: Int) -> Bool { if n == 0 { True } else { odd(n - 1) } }
fn odd(n: Int) { even(n - 1) }
fn size(x: Int) -> Int { 1 }
fn size(x: Str) { measure(x) }
fn measure(x: Str) { size(1) }
fn a(n: Int) { b(n) }
fn b(n: Int) { c(n) }
fn c(n: Int) { a(n) }
fn user(n: Int) -> Int { depth(n) }";
    assert_eq!(
        errors(text),
        [
            "`depth(n - 1)`: this call makes `depth` recursive, so `depth` must state its success \
             type",
            "`even(n - 1)`: this call makes `even` and `odd` recursive, so `odd` must state its \
             success type",
            "`measure(x)`: this call makes `size` and `measure` recursive, so `size` and \
             `measure` must state their success types",
            "`b(n)`: this call makes `a`, `b` and `c` recursive, so `a`, `b` and `c` must state \
             their success types",
        ]
    );
}
