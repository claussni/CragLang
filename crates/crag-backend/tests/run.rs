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

//! Compiles Crag modules and runs their functions.
//!
//! The functions run on the test's own thread, entered through the entry
//! stub with a task context whose stack limit is zero, so no stack check
//! fails, and whose heap is the module's. The runtime functions later
//! components provide are stubs here that count what they are asked to do,
//! and `rt_alloc` is one too, because the runtime's switches to a worker's
//! stack.

use std::cell::Cell;
use std::collections::HashMap;

use crag_abi::{HEADER_SIZE, HEAP_OFFSET, RuntimeFn};
use crag_backend::{code, type_index};
use crag_codegen::{CodeObject, CodegenSettings, FuncId, OptLevel, compile_entry_stub, target_for};
use crag_db::RootDatabase;
use crag_hir::{ItemKind, ModuleId, Owner, Program, SourceFile, owners};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_mir::{InstanceKey, Tier};
use crag_runtime::{Heap, alloc_box};
use crag_types::{Ty, TyKind, prelude_item};

const PRELUDE: &str = r#"pub type Int
pub type Int8
pub type UInt8
pub type Float
pub type Fixed[S]
pub type CodePoint
pub type True
pub type False
pub type Bool = True | False
pub type Empty[T]
pub type Option[T] = T | Empty[T]
pub type Range[T](first: T, last: T)
pub fn add(a: Int, b: Int) -> Int
pub fn add(a: UInt8, b: UInt8) -> UInt8
pub fn add(a: Float, b: Float) -> Float
pub fn add(a: Fixed[2], b: Fixed[2]) -> Fixed[2]
pub fn subtract(a: Int, b: Int) -> Int
pub fn multiply(a: Int, b: Int) -> Int
pub fn multiply(a: Float, b: Float) -> Float
pub fn divide(a: Int, b: Int) -> Int
pub fn remainder(a: Int, b: Int) -> Int
pub fn addWrapping(a: Int8, b: Int8) -> Int8
pub fn negate(a: Int) -> Int
pub fn equals(a: Int, b: Int) -> Bool
pub fn lessThan(a: Int, b: Int) -> Bool
pub fn lessThan(a: Float, b: Float) -> Bool
"#;

thread_local! {
    /// Calls of `rt_alloc`: boxes the inline path did not allocate.
    static SLOW_ALLOCS: Cell<usize> = const { Cell::new(0) };
    static RELEASED: Cell<usize> = const { Cell::new(0) };
}

/// The heap in a task context.
///
/// # Safety
///
/// `ctx` is a context `Module::call` made.
unsafe fn heap_of<'a>(ctx: *mut u64) -> &'a mut Heap {
    // SAFETY: as the caller promises.
    unsafe { &mut *(*ctx.byte_offset(HEAP_OFFSET as isize) as *mut Heap) }
}

extern "C" fn rt_alloc(ctx: *mut u64, size: u64, index: u64) -> *mut u8 {
    SLOW_ALLOCS.set(SLOW_ALLOCS.get() + 1);
    assert!(size >= u64::from(HEADER_SIZE) && size.is_multiple_of(8));
    // SAFETY: generated code passes the context it received.
    alloc_box(unsafe { heap_of(ctx) }, size as usize, index)
}

extern "C" fn rt_retain(_ctx: *mut u64, ptr: *mut u64) {
    // SAFETY: generated code passes boxes it allocated.
    unsafe { *ptr += 1 }
}

/// Frees a box with the last reference. The tests' boxes hold no boxes, so
/// there are no fields to release.
extern "C" fn rt_release(ctx: *mut u64, ptr: *mut u64) {
    // SAFETY: as for `rt_retain` and `rt_alloc`.
    unsafe {
        assert!(*ptr > 0, "released a dead box");
        *ptr -= 1;
        if *ptr == 0 {
            RELEASED.set(RELEASED.get() + 1);
            heap_of(ctx).free(ptr.cast());
        }
    }
}

extern "C" fn rt_trap(_ctx: *mut u64, kind: u64) {
    eprintln!("trap {kind}");
    std::process::abort();
}

type Stub = unsafe extern "C" fn(*mut u64, *const u8, *const u64, *mut u64);

/// A compiled module.
struct Module {
    db: RootDatabase,
    program: Program,
    functions: HashMap<String, (usize, u32, u32)>,
    unsupported: Vec<String>,
    arena: CodeArena,
    symbols: SymbolTable,
    settings: CodegenSettings,
    heap: Box<Heap>,
}

impl Module {
    fn new(text: &str) -> Module {
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
        let errors = crag_types::module_type_errors(&db, program, module);
        assert!(
            errors.is_empty(),
            "{:?}",
            errors
                .iter()
                .map(|(_, e)| e.kind.message(&db))
                .collect::<Vec<_>>()
        );
        let mut objects: Vec<(FuncId, CodeObject)> = Vec::new();
        let mut names = Vec::new();
        let mut unsupported = Vec::new();
        for owner in owners(&db, module) {
            let Owner::Item(item) = owner else { continue };
            if *item.kind(&db) != ItemKind::Function {
                continue;
            }
            let key = InstanceKey::new(&db, owner, Vec::new());
            let compiled = code(&db, program, key, Tier::Baseline)
                .as_ref()
                .expect("a function with a body")
                .as_ref()
                .expect("Cranelift accepts it");
            let name = item.name(&db).text(&db).clone();
            for what in &compiled.unsupported {
                unsupported.push(format!("{name}: {what}"));
            }
            names.push((name, compiled.params, compiled.returns));
            objects.push((compiled.func, compiled.object.clone()));
        }
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            let addr = match func {
                RuntimeFn::Alloc => rt_alloc as *const () as usize,
                RuntimeFn::Retain => rt_retain as *const () as usize,
                RuntimeFn::Release => rt_release as *const () as usize,
                RuntimeFn::Trap => rt_trap as *const () as usize,
                f => crag_runtime::runtime_fn_addr(f).expect("the runtime has it"),
            };
            symbols.define_runtime(func, addr);
        }
        let mut arena = CodeArena::new(1 << 20).unwrap();
        let group: Vec<(FuncId, &CodeObject)> = objects.iter().map(|(f, o)| (*f, o)).collect();
        let entries = load_group(&mut arena, &mut symbols, &group).unwrap();
        let functions = names
            .into_iter()
            .zip(entries)
            .map(|((name, params, returns), entry)| (name, (entry.addr(), params, returns)))
            .collect();
        let settings = CodegenSettings {
            target: target_for("x86_64-unknown-linux-gnu").unwrap(),
            opt: OptLevel::None,
        };
        Module {
            db,
            program,
            functions,
            unsupported,
            arena,
            symbols,
            settings,
            heap: Box::new(Heap::new()),
        }
    }

    /// Calls a function with argument words and returns its result words.
    fn call(&mut self, name: &str, args: &[u64]) -> Vec<u64> {
        let (addr, params, returns) = self.functions[name];
        assert_eq!(args.len(), params as usize, "arguments of {name}");
        let stub = compile_entry_stub(params, returns, &self.settings).unwrap();
        let stub = load(&mut self.arena, &self.symbols, &stub).unwrap();
        // The stack limit, the side stack's pointer and end, then the heap.
        let mut ctx = [0u64; 8];
        ctx[HEAP_OFFSET as usize / 8] = &raw mut *self.heap as u64;
        let mut results = [0u64; 2];
        // SAFETY: the stub was compiled for this function's words, and the
        // context's zero limit lets every stack check pass on this thread.
        // Generated code and the stubs use the heap only during the call.
        unsafe {
            let stub: Stub = std::mem::transmute(stub.as_ptr());
            stub(
                ctx.as_mut_ptr(),
                addr as *const u8,
                args.as_ptr(),
                results.as_mut_ptr(),
            );
        }
        results[..returns as usize].to_vec()
    }

    fn int(&mut self, name: &str, args: &[i64]) -> i64 {
        let args: Vec<u64> = args.iter().map(|&a| a as u64).collect();
        match self.call(name, &args).as_slice() {
            [one] => *one as i64,
            words => panic!("{name} returned {words:?}"),
        }
    }

    /// The type index of a prelude tag, as a `Bool` or a union carries it.
    fn tag(&self, name: &str) -> u64 {
        let item = prelude_item(&self.db, self.program, name).unwrap();
        type_index(Ty::new(&self.db, TyKind::Named(item, Vec::new()))) as u64
    }
}

#[test]
fn arithmetic_runs() {
    let mut m = Module::new(
        r#"fn inc(n: Int) -> Int {
  n + 1
}

fn mix(a: Int, b: Int) -> Int {
  (a * b - a) / b + a % b
}

fn wrap(a: Int8, b: Int8) -> Int8 {
  a +% b
}

fn bytes(a: UInt8, b: UInt8) -> UInt8 {
  a + b
}

fn neg(n: Int) -> Int {
  -n
}

fn area(r: Float) -> Float {
  3.0 * r * r
}

fn cents(a: Fixed[2], b: Fixed[2]) -> Fixed[2] {
  a + b + 0.05
}
"#,
    );
    assert_eq!(m.int("inc", &[41]), 42);
    let mix = |a: i64, b: i64| (a * b - a) / b + a % b;
    assert_eq!(m.int("mix", &[7, 2]), mix(7, 2));
    assert_eq!(m.int("mix", &[-7, 2]), mix(-7, 2));
    assert_eq!(m.int("wrap", &[100, 100]), -56);
    assert_eq!(m.int("bytes", &[200, 55]), 255);
    assert_eq!(m.int("neg", &[5]), -5);
    let area = m.call("area", &[2.0f64.to_bits()]);
    assert_eq!(f64::from_bits(area[0]), 12.0);
    assert_eq!(m.int("cents", &[150, 225]), 380);
    assert_eq!(m.unsupported, Vec::<String>::new());
}

#[test]
fn control_flow_runs() {
    let mut m = Module::new(
        r#"fn count(n: Int, acc: Int) -> Int {
  if n == 0 { acc } else { count(n - 1, acc + 1) }
}

fn between(n: Int) -> Bool {
  0 < n and n < 10
}

fn sum(r: Range[Int]) -> Int {
  var total = 0
  for i in r {
    total = total + i
  }
  total
}

fn upTo(n: Int) -> Int {
  sum(1..n)
}

fn sign(x: Float) -> Int {
  if x < 0.0 { -1 } else { if 0.0 < x { 1 } else { 0 } }
}
"#,
    );
    // Deep enough to overflow the thread's stack without tail calls.
    assert_eq!(m.int("count", &[10_000_000, 0]), 10_000_000);
    let (t, f) = (m.tag("True"), m.tag("False"));
    assert_eq!(m.call("between", &[5]), [t]);
    assert_eq!(m.call("between", &[10]), [f]);
    assert_eq!(m.call("between", &[0]), [f]);
    assert_eq!(m.int("upTo", &[100]), 5050);
    assert_eq!(m.int("upTo", &[0]), 0);
    assert_eq!(m.int("sign", &[(-2.5f64).to_bits() as i64]), -1);
    assert_eq!(m.int("sign", &[0.0f64.to_bits() as i64]), 0);
    assert_eq!(m.int("sign", &[3.0f64.to_bits() as i64]), 1);
}

#[test]
fn case_runs() {
    let mut m = Module::new(
        r#"fn classify(v: Int8) -> Int {
  case v {
    -128..-1 -> 0
    0 -> 1
    1 | 2 -> 2
    _ -> 3
  }
}

fn orZero(o: Option[Int]) -> Int {
  case o {
    Empty -> 0
    n: Int -> n
  }
}

fn both(n: Int) -> Int {
  orZero(n) + orZero(Empty)
}
"#,
    );
    let results: Vec<i64> = [-128, -1, 0, 1, 2, 3, 127]
        .iter()
        .map(|&v| m.int("classify", &[v]))
        .collect();
    assert_eq!(results, [0, 0, 1, 2, 2, 3, 3]);
    assert_eq!(m.int("both", &[7]), 7);
}

#[test]
fn records_are_counted() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Point3(..Point, z: Int)

fn make(x: Int) -> Point {
  Point(x: x, y: 2)
}

fn sum(p: Point) -> Int {
  p.x + p.y
}

fn depth(p: Point) -> Int {
  case p {
    Point3(z:) -> z
    Point(x:) -> x
  }
}

fn run(x: Int) -> Int {
  let p = make(x)
  let q = Point3(x: 1, y: 2, z: 30)
  sum(p) + sum(p) + depth(p) + depth(q)
}
"#,
    );
    RELEASED.set(0);
    assert_eq!(m.int("run", &[5]), 7 + 7 + 5 + 30);
    // Both boxes were freed, each exactly once.
    assert_eq!(RELEASED.get(), 2);
}

#[test]
fn boxes_come_from_the_free_list() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)

fn total(n: Int) -> Int {
  var sum = 0
  for i in 1..n {
    let p = Point(x: i, y: 1)
    sum = sum + p.x + p.y
  }
  sum
}
"#,
    );
    SLOW_ALLOCS.set(0);
    RELEASED.set(0);
    assert_eq!(m.int("total", &[10_000]), 10_000 * 10_001 / 2 + 10_000);
    // Each point is freed before the next is made, and the next takes its
    // block from the free list inline. Only the first box, the range, finds
    // the heap's page for its class empty.
    assert_eq!((SLOW_ALLOCS.get(), RELEASED.get()), (1, 10_001));
    assert_eq!(m.heap.pages_in_use(), 1);
}

#[test]
fn what_cannot_compile_is_listed() {
    let mut m = Module::new(
        r#"fn label(n: Int) -> Int {
  let text = "many"
  n
}

fn plain(n: Int) -> Int {
  n * 2
}
"#,
    );
    assert_eq!(m.unsupported, ["label: strings and bytes"]);
    assert_eq!(m.int("plain", &[21]), 42);
}
