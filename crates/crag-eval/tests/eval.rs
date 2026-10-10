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

//! Module-level values evaluated at compile time: their bytes, their
//! errors, and what is no constant.

use crag_abi::TrapKind;
use crag_db::{Db, RootDatabase, Setter, catch_cancelled};
use crag_eval::{ConstValue, EvalError, EvalSite, LIMITS, const_eval, eval_errors, evaluate};
use crag_hir::{ItemId, ModuleId, Program, SourceFile, item_tree};
use crag_runtime::Meter;

const PRELUDE: &str = r#"pub type Int
pub type Float
pub type True
pub type False
pub type Bool = True | False
pub type Empty[T]
pub type Option[T] = T | Empty[T]
pub type Range[T](first: T, last: T)
pub type List[T]
pub type Map[K, V]
pub type Set[T]
pub fn add(a: Int, b: Int) -> Int
pub fn subtract(a: Int, b: Int) -> Int
pub fn multiply(a: Int, b: Int) -> Int
pub fn divide(a: Int, b: Int) -> Int
pub fn equals(a: Int, b: Int) -> Bool
pub fn lessThan(a: Int, b: Int) -> Bool
"#;

struct Project {
    db: RootDatabase,
    program: Program,
    module: ModuleId,
    file: SourceFile,
}

impl Project {
    fn new(text: &str) -> Project {
        let db = RootDatabase::new();
        let core = ModuleId::new(
            &db,
            "std.core".to_string(),
            SourceFile::new(&db, PRELUDE.to_string()),
        );
        let file = SourceFile::new(&db, text.to_string());
        let module = ModuleId::new(&db, "app".to_string(), file);
        let program = Program::new(&db, vec![core, module]);
        let errors = crag_types::module_type_errors(&db, program, module);
        assert!(
            errors.is_empty(),
            "{:?}",
            errors
                .iter()
                .map(|(_, e)| e.kind.message(&db))
                .collect::<Vec<_>>()
        );
        Project {
            db,
            program,
            module,
            file,
        }
    }

    fn item(&self, name: &str) -> ItemId<'_> {
        item_of(&self.db, self.module, name)
    }

    /// The value's evaluation, checking that it leaves the heap empty.
    fn eval(&self, name: &str) -> Result<ConstValue, EvalError> {
        self.eval_with(name, LIMITS)
    }

    fn eval_with(&self, name: &str, meter: Meter) -> Result<ConstValue, EvalError> {
        let site = EvalSite::Value(self.item(name));
        let (result, left) = evaluate(&self.db, self.program, site, meter);
        assert_eq!(left, 0, "boxes left after evaluating {name}");
        result
    }

    fn bytes(&self, name: &str) -> Vec<u8> {
        self.eval(name).unwrap().bytes
    }
}

fn item_of<'db>(db: &'db dyn Db, module: ModuleId, name: &str) -> ItemId<'db> {
    item_tree(db, module)
        .items
        .iter()
        .map(|i| i.id)
        .find(|i| i.name(db).text(db) == name)
        .unwrap_or_else(|| panic!("no item {name}"))
}

fn words(words: &[u64]) -> Vec<u8> {
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

#[test]
fn constants_are_computed_and_encoded() {
    let p = Project::new(
        r#"type Point(x: Int, y: Int)
type Point3(..Point, z: Int)

fn double(n: Int) -> Int { n * 2 }

let base = 20
let answer = double(base) + 2
let origin = Point(x: 1, y: 2)
let deep: Point = Point3(x: 1, y: 2, z: 3)
let numbers = [3, 1, 2]
let ages = [2: 20, 1: 10]
let same = [1: 10, 2: 20]
let picked: Option[Int] = 5
let none: Option[Int] = Empty
let looped = sum(10)

fn sum(n: Int) -> Int {
  var t = 0
  for i in 1..n {
    t = t + i
  }
  t
}
"#,
    );
    let answer = p.eval("answer").unwrap();
    assert_eq!(answer.bytes, words(&[42]));
    assert_eq!(answer.hash, *blake3::hash(&answer.bytes).as_bytes());
    assert_eq!(p.bytes("looped"), words(&[55]));
    // A record: the shape of its box's type, then its fields.
    let origin = p.bytes("origin");
    assert_eq!(origin[4..], words(&[1, 2]));
    // A subtype's box has a shape of its own and keeps its fields.
    let deep = p.bytes("deep");
    assert_ne!(deep[..4], origin[..4]);
    assert_eq!(deep[4..], words(&[1, 2, 3]));
    assert_eq!(p.bytes("numbers"), words(&[3, 3, 1, 2]));
    // A map's entries come in the order of their keys, however written.
    assert_eq!(p.bytes("ages"), words(&[2, 1, 10, 2, 20]));
    assert_eq!(p.bytes("ages"), p.bytes("same"));
    // A union: the member, then its words.
    let picked = p.bytes("picked");
    let none = p.bytes("none");
    assert_eq!(picked[4..], words(&[5]));
    assert_eq!(none.len(), 4);
    assert_ne!(picked[..4], none[..4]);
    // The query keeps the result.
    let site = EvalSite::Value(p.item("answer"));
    assert_eq!(const_eval(&p.db, p.program, site), &Ok(answer));
}

#[test]
fn a_failing_evaluation_is_a_compile_error() {
    let text = r#"fn zero() -> Int { 0 }

fn ratio(a: Int, b: Int) -> Int { a / b }

fn spin(n: Int) -> Int {
  var t = 0
  for i in 1..n {
    t = t + 1
  }
  t
}

type Point(x: Int, y: Int)

fn hold(n: Int, p: Point) -> Int {
  if n == 3000 { 0 } else { hold(n + 1, Point(x: n, y: 0)) + p.x }
}

let good = 1
let bad: Int = ratio(1, zero())
let forever = spin(1000000000000)
let hungry = hold(0, Point(x: 0, y: 0))

fn depth(n: Int) -> Int {
  if n == 0 { 0 } else { depth(n - 1) + 1 }
}

let tall = depth(5000)
"#;
    let p = Project::new(text);
    let Err(EvalError::Trap {
        kind,
        position,
        stack,
    }) = p.eval("bad")
    else {
        panic!("bad did not trap");
    };
    assert_eq!(kind, TrapKind::DivideByZero);
    assert_eq!(
        position,
        Some((p.module, text.find("a / b").unwrap() as u32))
    );
    assert_eq!(stack, ["ratio", "bad"]);
    let kind = |name, meter| match p.eval_with(name, meter) {
        Err(EvalError::Trap { kind, .. }) => kind,
        other => panic!("{name}: {other:?}"),
    };
    // Smaller limits than the compiler's, so the test is quick. With the
    // compiler's, `hungry` fits.
    let steps = Meter {
        steps: 1_000_000,
        ..LIMITS
    };
    let memory = Meter {
        memory: 64 << 10,
        ..LIMITS
    };
    assert_eq!(kind("forever", steps), TrapKind::OutOfSteps);
    assert_eq!(kind("hungry", memory), TrapKind::OutOfMemory);
    // The stack is memory too: five thousand frames do not fit 64 KiB.
    assert_eq!(kind("tall", memory), TrapKind::OutOfMemory);
    // The errors of the module, in its order.
    let errors: Vec<_> = eval_errors(&p.db, p.program, p.module)
        .into_iter()
        .map(|(item, _)| item.name(&p.db).text(&p.db).clone())
        .collect();
    assert_eq!(errors, ["bad", "forever"]);
    assert_eq!(p.bytes("hungry"), words(&[(0..2999).sum()]));
    assert_eq!(p.bytes("tall"), words(&[5000]));
}

#[test]
fn what_cannot_be_a_constant_is_computed_when_the_program_runs() {
    let p = Project::new(
        r#"import cLib("m").{ now() -> Int }

fn inc(n: Int) -> Int { n + 1 }
fn clock() -> Int { now() }

let stamp = clock()
let adder = { n: Int -> n + 1 }
let named: (Int) -> Int = inc
let pair = (f: inc, n: 1)
"#,
    );
    for name in ["adder", "named", "pair"] {
        assert_eq!(
            p.eval(name),
            Err(EvalError::NotConstant("it holds a function value".into())),
            "{name}"
        );
    }
    // Compile-time code does no I/O.
    assert_eq!(
        p.eval("stamp"),
        Err(EvalError::NotConstant("it has effects".into()))
    );
    assert!(eval_errors(&p.db, p.program, p.module).is_empty());
}

#[test]
fn an_edit_cancels_a_long_evaluation() {
    let text = r#"fn spin(n: Int) -> Int {
  var t = 0
  for i in 1..n {
    t = t + 1
  }
  t
}

let forever = spin(1000000000000)
"#;
    let mut p = Project::new(text);
    let snapshot = p.db.snapshot();
    let (program, module) = (p.program, p.module);
    let started = std::time::Instant::now();
    let reader = std::thread::spawn(move || {
        let db = snapshot.db();
        let site = EvalSite::Value(item_of(db, module, "forever"));
        catch_cancelled(|| const_eval(db, program, site).clone())
    });
    std::thread::sleep(std::time::Duration::from_millis(20));
    // Waits until the evaluation has stopped and dropped its snapshot.
    p.file
        .set_text(&mut p.db)
        .to(text.replace("forever", "later"));
    assert_eq!(reader.join().unwrap(), Err(crag_db::Cancelled));
    eprintln!("cancelled after {:?}", started.elapsed());
}
