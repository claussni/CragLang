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
use crag_hir::{
    LowerError, ModuleId, Owner, Program, SourceFile, hir_body, lower_body, owners, pretty,
};

const PRELUDE: &str = r#"pub type Int
pub type Str
pub type Float
pub type List[T]
pub type Point(x: Int, y: Int)
pub type Done
pub fn add(a: Int, b: Int) -> Int
pub fn subtract(a: Int, b: Int) -> Int
pub fn multiply(a: Int, b: Int) -> Int
pub fn negate(a: Int) -> Int
pub fn equals(a: Int, b: Int) -> Bool
pub fn lessThan(a: Int, b: Int) -> Bool
pub fn greaterThan(a: Int, b: Int) -> Bool
pub fn map[T, U](xs: List[T], f: (T) -> U) -> List[U]
pub fn size(xs: List[Int]) -> Int
pub fn parse(s: Str) -> Int
pub fn discard[X](x: X) -> () prefix "~"
pub fn check[X](x: X) -> X prefix "?"
pub fn expect[X](x: X) -> X prefix "!!"
"#;

fn setup(db: &RootDatabase, text: &str) -> (Program, ModuleId) {
    let core = ModuleId::new(
        db,
        "std.core".to_string(),
        SourceFile::new(db, PRELUDE.to_string()),
    );
    let module = ModuleId::new(db, "app".to_string(), SourceFile::new(db, text.to_string()));
    (Program::new(db, vec![core, module]), module)
}

/// Every body of the module, printed, and the errors lowering them.
fn lower(text: &str) -> (Vec<String>, Vec<String>) {
    let db = RootDatabase::new();
    let (program, module) = setup(&db, text);
    let line = |offset: u32| text[..offset as usize].matches('\n').count() + 1;
    let mut bodies = Vec::new();
    let mut errors = Vec::new();
    for owner in owners(&db, module) {
        let lowered = lower_body(&db, program, owner);
        bodies.push(pretty(&db, &lowered.body));
        for error in &lowered.errors {
            let (what, range) = match error {
                LowerError::Unresolved { name, range } => (format!("unresolved {name}"), range),
                LowerError::UnknownType { name, range } => (format!("unknown type {name}"), range),
                LowerError::Redeclared(r) => (format!("redeclared {}", r.name), &r.range),
                LowerError::NotInEveryAlternative { name, range } => {
                    (format!("{name} not in every alternative"), range)
                }
                LowerError::UnnamedField { range } => ("unnamed field".into(), range),
                LowerError::Literal { message, range } => (message.clone(), range),
                LowerError::UnknownPrefix { text, range } => {
                    (format!("unknown prefix {text}"), range)
                }
                LowerError::NoOperator { function, range } => (format!("no {function}"), range),
                LowerError::NotAVar { name, range } => (format!("{name} is not a var"), range),
                LowerError::VarWrittenInClosure { name, range } => {
                    (format!("{name} written in a closure"), range)
                }
                LowerError::MisplacedSpread { range } => ("misplaced spread".into(), range),
                LowerError::ExpectedType { range } => ("expected a type".into(), range),
                LowerError::ExpectedValue { range } => ("expected a value".into(), range),
                LowerError::Marker { range } => ("not a function marker".into(), range),
            };
            errors.push(format!("line {}: {what}", line(range.start)));
        }
    }
    (bodies, errors)
}

#[test]
fn operators_become_calls() {
    let (bodies, errors) = lower(
        "fn f(a: Int, b: Int = a) -> Int {\n  let c = a + b * 2\n  -c == 1 and not (a < b) or a != b\n}",
    );
    assert_eq!(errors, Vec::<String>::new());
    assert_eq!(
        bodies,
        ["(params a$0: Int b$1: Int = a$0) -> Int {\
          (let c$2 (call add/1 a$0 (call multiply/1 b$1 2))); \
          (or (and (call equals/1 (call negate/1 c$2) 1) \
          (not (call lessThan/1 a$0 b$1))) \
          (not (call equals/1 a$0 b$1)))}"]
    );
}

#[test]
fn calls_fields_brackets_and_partial_application() {
    let text = r#"fn g(xs: List[Int], p: Point) -> Int {
  let n = xs.size
  let m = xs.map { x -> x + 1 }
  let k = Int.parse("4")
  let q = Point(x: 1, y: 2)
  let r = Point(..p, x: _ + 1)
  let first = xs[0]
  let e = List[Int]()
  let twice = multiply(_, 2)
  let later = add(_, xs.size)
  m.map(_ * n)
}"#;
    let (bodies, errors) = lower(text);
    assert_eq!(errors, Vec::<String>::new());
    assert_eq!(
        bodies,
        ["(params xs$0: List[Int] p$1: Point) -> Int {\
          (let n$2 (field xs$0 size/1)); \
          (let m$4 (. xs$0 map/1 (fn [x$3] {(call add/1 x$3 1)}))); \
          (let k$5 (typed Int parse/1 \"4\")); \
          (let q$6 (call Point:type {x: 1, y: 2})); \
          (let r$8 (call Point:type {..p$1, x: (fn [_$7] (call add/1 _$7 1))})); \
          (let first$9 (index xs$0 0)); \
          (let e$10 (call (type-args List:type Int))); \
          (let twice$12 (fn [_$11] (call multiply/1 _$11 2))); \
          (let later$15 {(let _$14 (field xs$0 size/1)); (fn [_$13] (call add/1 _$13 _$14))}); \
          (. m$4 map/1 (fn [_$16] (call multiply/1 _$16 n$2)))}"]
    );
}

#[test]
fn patterns_get_explicit_forms() {
    let text = r#"fn h(v: Int) -> Int {
  case v {
    0 -> 1
    1..9 -> 2
    -1 | -9..-2 -> 4
    n: Int where n > 10 -> n
    Point(x:, y: 0) | Point(x, y: 1) -> x
    [first, ..rest, last] -> first
    Done -> 3
    pass
  }
}
let (left, right) = (left: 1, right: 2)
"#;
    let (bodies, errors) = lower(text);
    assert_eq!(errors, Vec::<String>::new());
    assert_eq!(
        bodies,
        [
            "(params v$0: Int) -> Int {(case v$0 [0 -> 1] [1..9 -> 2] [(-1 | -9..-2) -> 4] \
             [n$1 @ Int where (call greaterThan/1 n$1 10) -> n$1] \
             [(Point(x: x$2, y: 0) | Point(x$2, y: 1)) -> x$2] \
             [[first$3, ..rest$4, last$5] -> first$3] [Done -> 3] [_ -> pass])}",
            "(pattern (left$0, right$1)) (record {left: 1, right: 2})",
        ]
    );
}

#[test]
fn statements_and_literals() {
    let text = r#"fn s(pairs: List[Int]) {
  var total = 0
  for (k, v) in pairs { total = total + v }
  let name: Str = parse("x") else { return }
  let (a, Int) = pairs
  fn twice(n: Int) -> Int { twice(n) }
  let text = "sum {total} of {name}"
  let grid = [1, 2; 3, 4]
  let dict = ["a": 1]
  let unit = ()
  let later = lazy total + 1
  let f = { (x, y): Point, z -> x }
  ~ !! parse("1")
  atomic { emit ok total }
  on Done { d -> 0 }
  ???
}
test "t" { let x = b"\x01" }
"#;
    let (bodies, errors) = lower(text);
    assert_eq!(errors, Vec::<String>::new());
    assert_eq!(
        bodies,
        [
            "(params pairs$0: List[Int]) {(var total$1 0); \
             (for (k$2, v$3) pairs$0 {(set total$1 (call add/1 total$1 v$3))}); \
             (let name$4: Str (call parse/1 \"x\") else {(return)}); \
             (let (a$5, Int) pairs$0); \
             (local-fn twice$6 (params n$7: Int) -> Int {(call twice$6 n$7)}); \
             (let text$8 (str \"sum \" total$1 \" of \" name$4)); \
             (let grid$9 (grid 1 2 ; 3 4)); (let dict$10 (map \"a\": 1)); \
             (let unit$11 (record {})); (let later$12 (lazy (call add/1 total$1 1))); \
             (let f$16 (fn [(x$13, y$14): Point, z$15] {x$13})); \
             (call discard/1 (call expect/1 (call parse/1 \"1\"))); \
             (atomic {(emit Ok total$1)}); (on Done (fn [d$17] {0})); ???}",
            "{(let x$0 b[1])}",
        ]
    );
}

#[test]
fn what_lowering_reports() {
    let text = r#"fn e(p: Point) {
  let a = missing + 1
  let b: Nope = 1
  a = 2
  var c = 0
  let f = { -> c = 1 }
  let g = { -> c + 1 }
  let r = (1, x: 2)
  let n = 99999999999999999999999999999999999999999
  let s = "a\qb"
  case p {
    Point(x:) | Point(y:) -> 0
    Unknown -> 1
  }
  @@ p
  undefinedVar = 3
  let t = List[(Int) -> Int]
  let u = p[(Int) -> Int]
}
type Moved(x: Int, ..Point, ..Point)"#;
    let (_, errors) = lower(text);
    assert_eq!(
        errors,
        [
            "line 2: unresolved missing",
            "line 3: unknown type Nope",
            "line 4: a is not a var",
            "line 6: c written in a closure",
            "line 8: unnamed field",
            "line 9: `99999999999999999999999999999999999999999` is too large",
            "line 10: unknown escape `\\q`",
            "line 12: x not in every alternative",
            "line 12: y not in every alternative",
            "line 13: unknown type Unknown",
            "line 15: unknown prefix @@",
            "line 16: unresolved undefinedVar",
            "line 18: expected a value",
            "line 20: misplaced spread",
            "line 20: misplaced spread",
        ]
    );
}

#[test]
fn operators_need_their_functions() {
    let db = RootDatabase::new();
    let module = ModuleId::new(
        &db,
        "alone".to_string(),
        SourceFile::new(&db, "fn f(a: Int) { a + 1 }".to_string()),
    );
    let program = Program::new(&db, vec![module]);
    let owner = owners(&db, module)[0];
    let errors: Vec<String> = lower_body(&db, program, owner)
        .errors
        .iter()
        .map(|e| format!("{e:?}"))
        .collect();
    // Without a prelude, `Int` is unknown too.
    assert_eq!(
        errors,
        [
            r#"UnknownType { name: "Int", range: 8..11 }"#,
            r#"NoOperator { function: "add", range: 15..20 }"#,
        ]
    );
}

/// A query that reads a body and counts its runs.
static RUNS: AtomicUsize = AtomicUsize::new(0);

#[crag_db::tracked]
fn body_size<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> usize {
    RUNS.fetch_add(1, Ordering::SeqCst);
    hir_body(db, program, owner).exprs.len()
}

#[test]
fn bodies_stay_equal_when_only_their_place_changes() {
    let mut db = RootDatabase::new();
    let text = "fn a() { 1 }\nfn b(x: Int) { x + 2 }\n";
    let (program, module) = setup(&db, text);
    // An owner borrows the database, so it is looked up again after edits;
    // it is the same function `b` every time.
    let runs = |db: &RootDatabase| {
        body_size(db, program, owners(db, module)[1]);
        RUNS.load(Ordering::SeqCst)
    };
    let start = runs(&db);
    let root = |db: &RootDatabase| {
        let lowered = lower_body(db, program, owners(db, module)[1]);
        lowered.source_map.exprs[lowered.body.root.unwrap().index()].clone()
    };
    let before = root(&db);
    let edit = |db: &mut RootDatabase, text: String| {
        let file = *module.file(db);
        file.set_text(db).to(text);
    };
    edit(
        &mut db,
        format!("// moved\n\n{}", text.replace("{ 1 }", "{ 1 + 1 }")),
    );
    assert_eq!(runs(&db), start, "only positions and another body changed");
    assert_eq!(root(&db).start, before.start + 14, "the source map follows");
    edit(&mut db, text.replace("x + 2", "x + 3"));
    assert_eq!(runs(&db), start + 1, "the body changed");
}

const FRAGMENTS: &[&str] = &[
    "\"", "{", "}", "(", ")", "[", "]", "_", "\n", ".", "..", "else", "x", " ", "+", "->", ",",
    "1", "=", "let", "case", "if", "{ x -> }", "?.", "!!", ":", "|", "var", "fn", "pass",
    "\"{a}\"",
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
fn broken_code_lowers_without_panicking() {
    let base = r#"fn s(pairs: List[Int], p: Point) -> Int {
  var total = 0
  for (k, v) in pairs { total = total + v }
  let name: Str = parse("x") else { return 0 }
  case p {
    Point(x:, y: 0) | Point(x, y: 1) -> x
    n: Int where n > 10 -> n
    pass
  }
  let r = Point(..p, x: _ + 1)
  pairs.map { x -> x * 2 }.size
}
test "t" { ~ !! parse("1") }
"#;
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
        let (program, module) = setup(&db, &text);
        for owner in owners(&db, module) {
            let lowered = lower_body(&db, program, owner);
            let (body, map) = (&lowered.body, &lowered.source_map);
            assert_eq!(body.exprs.len(), map.exprs.len(), "{text:?}");
            assert_eq!(body.pats.len(), map.pats.len(), "{text:?}");
            assert_eq!(body.types.len(), map.types.len(), "{text:?}");
            assert_eq!(body.bindings.len(), map.bindings.len(), "{text:?}");
            pretty(&db, body);
        }
    }
}

#[test]
fn functions_and_function_types_are_marked_pure() {
    let (bodies, errors) = lower(
        "fn f(g: ((Int) -> Int is Pure), h: (Int) -> Int) -> Int is Pure { 1 }\n\
         fn k(x: (Int is Pure)) -> Int is Solid { 1 }",
    );
    assert_eq!(
        errors,
        [
            "line 2: not a function marker",
            "line 2: not a function marker"
        ]
    );
    assert_eq!(
        bodies[0],
        "(params g$0: ((Int) -> Int is Pure) h$1: ((Int) -> Int)) -> Int is Pure {1}"
    );
}
