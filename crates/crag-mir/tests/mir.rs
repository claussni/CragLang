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

use crag_db::RootDatabase;
use crag_hir::{ItemKind, ModuleId, Owner, Program, SourceFile, owners};
use crag_mir::{InstanceKey, Tier, mir};

const PRELUDE: &str = r#"pub type Int
pub type Int8
pub type Float
pub type Fixed[S]
pub type Str
pub type CodePoint
pub type List[T]
pub type True
pub type False
pub type Bool = True | False
pub type Empty[T]
pub type Option[T] = T | Empty[T]
pub type Range[T](first: T, last: T)
pub fn add(a: Int, b: Int) -> Int
pub fn add(a: Float, b: Float) -> Float
pub fn subtract(a: Int, b: Int) -> Int
pub fn multiply(a: Int, b: Int) -> Int
pub fn multiply(a: Float, b: Float) -> Float
pub fn divide(a: Int, b: Int) -> Int
pub fn divide(a: Float, b: Float) -> Float
pub fn negate(a: Int8) -> Int8
pub fn equals(a: Int, b: Int) -> Bool
pub fn equals(a: Str, b: Str) -> Bool
pub fn lessThan(a: Int, b: Int) -> Bool
pub fn size(s: Str) -> Int
"#;

/// The type errors of the module, then the MIR of every function, test
/// and value of the module after a line with its name.
fn mir_of(text: &str) -> String {
    let db = RootDatabase::new();
    let core = ModuleId::new(
        &db,
        "std.core".to_string(),
        SourceFile::new(&db, PRELUDE.to_string()),
    );
    let module = ModuleId::new(
        &db,
        "app".to_string(),
        SourceFile::new(&db, text.to_string()),
    );
    let program = Program::new(&db, vec![core, module]);
    let mut out = String::new();
    for (_, error) in crag_types::module_type_errors(&db, program, module) {
        out += &format!("error: {}\n", error.kind.message(&db));
    }
    for owner in owners(&db, module) {
        let name = match owner {
            Owner::Item(item) if *item.kind(&db) == ItemKind::Type => continue,
            Owner::Item(item) => item.name(&db).text(&db).clone(),
            Owner::Test(test) => format!("test {}", test.label(&db)),
        };
        for error in &crag_hir::lower_body(&db, program, owner).errors {
            out += &format!("error: {error:?}\n");
        }
        let key = InstanceKey::new(&db, owner, Vec::new());
        if let Some(body) = mir(&db, program, key, Tier::Baseline) {
            out += &format!("{name}\n{}", body.pretty(&db));
            for (_, what) in &body.unsupported {
                out += &format!("unsupported: {what}\n");
            }
        }
    }
    out
}

fn check(text: &str, expected: &str) {
    let found = mir_of(text);
    if found != expected {
        panic!("MIR differs; found:\n{found}");
    }
}

/// Integer operations test for overflow before they run, division for a
/// zero divisor first; a run of `Float` operations shares one test, after
/// it. A negated literal is a constant.
#[test]
fn arithmetic_checks_are_explicit() {
    check(
        r#"fn inc(n: Int) -> Int {
  n + 1
}

fn area(r: Float) -> Float {
  3.14159 * r * r
}

fn half(n: Int, d: Int) -> Int {
  n / d
}

fn least() -> Int8 {
  -128
}
"#,
        r#"inc
param _0: Int (n)
let _1: Int
let _2: False | True
bb0:
  _2 = overflows Int.add(_0, 1)
  branch _2 bb1 bb2
bb1:
  trap overflow
bb2:
  _1 = Int.add(_0, 1)
  return _1
area
param _0: Float (r)
let _1: Float
let _2: Float
let _3: False | True
bb0:
  _1 = Float.mul(3.14159, _0)
  _2 = Float.mul(_1, _0)
  _3 = overflowed(_1, _2)
  branch _3 bb1 bb2
bb1:
  trap overflow
bb2:
  return _2
half
param _0: Int (n)
param _1: Int (d)
let _2: Int
let _3: False | True
let _4: False | True
bb0:
  _3 = Int.eq(_1, 0)
  branch _3 bb1 bb2
bb1:
  trap divide by zero
bb2:
  _4 = overflows Int.div(_0, _1)
  branch _4 bb3 bb4
bb3:
  trap overflow
bb4:
  _2 = Int.div(_0, _1)
  return _2
least
bb0:
  return -128
"#,
    );
}

#[test]
fn calls_in_tail_position_are_tail_calls() {
    check(
        r#"fn count(n: Int) -> Int {
  if n == 0 { 0 } else { count(n - 1) }
}

fn call() -> Int {
  count(3) + 1
}
"#,
        r#"count
param _0: Int (n)
let _1: False | True
let _2: Int
let _3: False | True
bb0:
  _1 = Int.eq(_0, 0)
  branch _1 bb1 bb2
bb1:
  return 0
bb2:
  _3 = overflows Int.sub(_0, 1)
  branch _3 bb3 bb4
bb3:
  trap overflow
bb4:
  _2 = Int.sub(_0, 1)
  tail call count(_2)
call
let _0: Int
let _1: Int
let _2: False | True
bb0:
  _0 = call count(3) -> bb1
bb1:
  _2 = overflows Int.add(_0, 1)
  branch _2 bb2 bb3
bb2:
  trap overflow
bb3:
  _1 = Int.add(_0, 1)
  return _1
"#,
    );
}

/// A value is retained for every use but the last, released after a last
/// use that only reads it, and released where it dies unused: an unused
/// parameter, and on the edges into blocks that no longer need it, split
/// when the block has other predecessors.
#[test]
fn reference_counts_follow_liveness() {
    check(
        r#"type Pair(a: Str, b: Str)

fn twice(s: Str) -> Pair {
  Pair(a: s, b: s)
}

fn ignore(s: Str) -> Int {
  1
}

fn first(p: Pair) -> Str {
  p.a
}

fn both(a: Str, c: Bool, d: Bool) -> Int {
  if c and d { size(a) } else { 0 }
}
"#,
        r#"twice
param _0: Str (s)
let _1: Pair
bb0:
  retain _0
  _1 = Pair(a: _0, b: _0)
  return _1
ignore
param _0: Str (s)
bb0:
  release _0
  return 1
first
param _0: Pair (p)
let _1: Str
bb0:
  _1 = _0.a
  retain _1
  release _0
  return _1
both
param _0: Str (a)
param _1: False | True (c)
param _2: False | True (d)
bb0:
  branch _1 bb3 bb4
bb1:
  tail call size(_0)
bb2:
  return 0
bb3:
  branch _2 bb1 bb5
bb4:
  release _0
  jump bb2
bb5:
  release _0
  jump bb2
"#,
    );
}

/// A union is switched on its runtime type, a finer type first; literals
/// become comparisons, list patterns tests of the length.
#[test]
fn case_becomes_a_decision_tree() {
    check(
        r#"type Point(x: Int, y: Int)
type Point3(..Point, z: Int)

fn describe(v: Int | Str) -> Int {
  case v {
    0 -> 1
    1..9 -> 2
    Int -> 3
    "a" -> 4
    _ -> 5
  }
}

fn depth(p: Point) -> Int {
  case p {
    Point3(z:) -> z
    Point(x: 0, y:) -> y
    Point(x:) -> x
  }
}

fn last(xs: List[Str]) -> Str {
  case xs {
    [] -> "empty"
    [a] -> a
    [_, ..rest, b] -> b
  }
}
"#,
        r#"describe
param _0: Int | Str (v)
let _1: Int
let _2: False | True
let _3: False | True
let _4: False | True
let _5: Str
let _6: False | True
bb0:
  switch _0 [Int: bb1] else bb2
bb1:
  _1 = (_0 as Int)
  release _0
  _2 = Int.eq(_1, 0)
  branch _2 bb4 bb3
bb2:
  _5 = (_0 as Str)
  retain _5
  release _0
  _6 = Str.eq(_5, "a")
  release _5
  branch _6 bb8 bb9
bb3:
  _3 = Int.ge(_1, 1)
  branch _3 bb5 bb7
bb4:
  return 1
bb5:
  _4 = Int.le(_1, 9)
  branch _4 bb6 bb7
bb6:
  return 2
bb7:
  return 3
bb8:
  return 4
bb9:
  return 5
depth
param _0: Point (p)
let _1: Int (z)
let _2: Int
let _3: False | True
let _4: Int (y)
let _5: Int (x)
bb0:
  switch _0 [Point3: bb1] else bb2
bb1:
  _1 = (_0 as Point3).z
  release _0
  jump bb3
bb2:
  _2 = (_0 as Point).x
  _3 = Int.eq(_2, 0)
  branch _3 bb4 bb5
bb3:
  return _1
bb4:
  _4 = (_0 as Point).y
  release _0
  jump bb6
bb5:
  _5 = (_0 as Point).x
  release _0
  jump bb7
bb6:
  return _4
bb7:
  return _5
last
param _0: List[Str] (xs)
let _1: Int
let _2: False | True
let _3: False | True
let _4: Str (a)
let _5: List[Str] (rest)
let _6: Str (b)
bb0:
  _1 = len _0
  _2 = Int.eq(_1, 0)
  branch _2 bb2 bb1
bb1:
  _3 = Int.eq(_1, 1)
  branch _3 bb3 bb4
bb2:
  release _0
  return "empty"
bb3:
  _4 = _0[0]
  retain _4
  release _0
  jump bb5
bb4:
  _5 = slice _0[1..-1]
  release _5
  _6 = _0[-1]
  retain _6
  release _0
  jump bb6
bb5:
  return _4
bb6:
  return _6
"#,
    );
}

/// A `let` destructures with the tree of its one pattern; a typed `let …
/// else` tests the type first. A failed guard goes on to the next arm
/// that can match.
#[test]
fn lets_bind_and_test() {
    check(
        r#"type Point(x: Int, y: Int)

fn swap(p: Point) -> Point {
  let Point(x:, y:) = p
  Point(x: y, y: x)
}

fn known(o: Option[Point]) -> Int {
  let q: Point = o else { return 0 }
  q.y
}

fn second(xs: List[Int]) -> Int {
  case xs {
    [_, b, ..] where b == 0 -> b
    [a, ..] -> a
    [] -> 0
  }
}
"#,
        r#"swap
param _0: Point (p)
let _1: Int (x)
let _2: Int (y)
let _3: Point
bb0:
  _1 = _0.x
  _2 = _0.y
  release _0
  jump bb1
bb1:
  _3 = Point(x: _2, y: _1)
  return _3
known
param _0: Empty[Point] | Point (o)
let _1: Point
let _2: Point (q)
let _3: Int
bb0:
  switch _0 [Point: bb1] else bb2
bb1:
  _1 = convert _0
  _2 = _1
  jump bb3
bb2:
  release _0
  return 0
bb3:
  _3 = _2.y
  release _2
  return _3
second
param _0: List[Int] (xs)
let _1: Int
let _2: False | True
let _3: False | True
let _4: Int (a)
let _5: Int (b)
let _6: False | True
bb0:
  _1 = len _0
  _2 = Int.eq(_1, 0)
  branch _2 bb2 bb1
bb1:
  _3 = Int.eq(_1, 1)
  branch _3 bb3 bb4
bb2:
  release _0
  return 0
bb3:
  _4 = _0[0]
  release _0
  jump bb5
bb4:
  _5 = _0[1]
  _6 = Int.eq(_5, 0)
  branch _6 bb6 bb7
bb5:
  return _4
bb6:
  release _0
  return _5
bb7:
  _4 = _0[0]
  release _0
  jump bb5
"#,
    );
}

#[test]
fn loops_poll_on_their_back_edges() {
    check(
        r#"fn sum(xs: List[Int]) -> Int {
  var total = 0
  for x in xs {
    total = total + x
  }
  total
}

fn last(r: Range[Int]) -> Int {
  var n = 0
  for i in r {
    n = i
  }
  n
}
"#,
        r#"sum
param _0: List[Int] (xs)
let _1: Int (total)
let _2: Int
let _3: Int
let _4: False | True
let _5: Int
let _6: Int (x)
let _7: Int
let _8: Int
let _9: False | True
bb0:
  _1 = 0
  _2 = len _0
  _3 = 0
  jump bb1
bb1:
  _4 = Int.lt(_3, _2)
  branch _4 bb2 bb3
bb2:
  _5 = _0[_3]
  _6 = _5
  _9 = overflows Int.add(_1, _6)
  branch _9 bb4 bb5
bb3:
  release _0
  return _1
bb4:
  release _0
  trap overflow
bb5:
  _7 = Int.add(_1, _6)
  _1 = _7
  _8 = Int.add(_3, 1)
  _3 = _8
  poll
  jump bb1
last
param _0: Range[Int] (r)
let _1: Int (n)
let _2: Int
let _3: Int
let _4: False | True
let _5: Int (i)
let _6: False | True
let _7: Int
bb0:
  _1 = 0
  _2 = _0.first
  _3 = _0.last
  release _0
  _4 = Int.le(_2, _3)
  branch _4 bb1 bb2
bb1:
  _5 = _2
  _1 = _5
  _6 = Int.eq(_2, _3)
  branch _6 bb2 bb3
bb2:
  return _1
bb3:
  _7 = Int.add(_2, 1)
  _2 = _7
  poll
  jump bb1
"#,
    );
}

/// A body with type errors traps where it starts; a construct the builder
/// does not lower yet traps where it is reached, and is listed.
#[test]
fn what_cannot_run_traps() {
    check(
        r#"fn closure(n: Int) -> Int {
  let f = { x: Int -> x }
  n
}

fn wrong() -> Int {
  "no"
}

fn hole() -> Int {
  ???
}
"#,
        r#"error: expected Int, found Str
closure
param _0: Int (n)
bb0:
  trap unsupported
unsupported: closures
wrong
bb0:
  trap error
hole
bb0:
  trap hole
"#,
    );
}
