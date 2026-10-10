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
//! `Module::call` runs a function on the test's own thread, entered through
//! the entry stub with a task context whose stack limit is zero, so no stack
//! check fails, and whose heap is the module's. The runtime's functions switch to
//! a worker's stack, which this context has none of, so stubs here do what
//! they do on the test's own stack: `rt_alloc` and `rt_release` count their
//! calls, and the list and map functions call the runtime's Rust halves.
//! `rt_trap` aborts. `Module::run` runs a function on a fiber instead, with
//! a second copy of the code that calls the runtime itself, so a trap ends
//! the fiber. `Module::metered` compiles the code in the metered tier,
//! whose fibers `Module::run_metered` runs under a meter.

use std::cell::Cell;
use std::collections::HashMap;

use crag_abi::{
    HEADER_SIZE, HEAP_OFFSET, Number, RuntimeFn, SIDE_END_OFFSET, SIDE_PTR_OFFSET, Shapes,
    TrapKind, inline_text,
};
use crag_backend::{code, shapes, type_index};
use crag_codegen::{
    CodeObject, CodegenSettings, OptLevel, SlotKey, compile_entry_stub, target_for,
};
use crag_db::RootDatabase;
use crag_hir::{ItemKind, ModuleId, Owner, Program, SourceFile, lower_body, owners};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_mir::{InstanceKey, Tier, collect_instances};
use crag_runtime::text::TextWords;
use crag_runtime::{
    CodeMap, Fiber, FiberConfig, FiberState, Heap, Meter, PrintLimits, StopReason, Trap, Types,
    Worker, alloc_box, decode_value, encode_value, list, map, print_value, release_box,
    release_value, request_stop, text,
};
use crag_types::{Ty, TyKind, prelude_item, signature};

const PRELUDE: &str = r#"pub type Int
pub type Int8
pub type UInt8
pub type Float
pub type Fixed[S]
pub type CodePoint
pub type Str
pub type Bytes
pub type True
pub type False
pub type Bool = True | False
pub type Empty[T]
pub type Option[T] = T | Empty[T]
pub distinct type Error
pub type Range[T](first: T, last: T)
pub type List[T]
pub type Map[K, V]
pub type Set[T]
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
pub fn negate(a: Float) -> Float
pub fn equals(a: Int, b: Int) -> Bool
pub fn lessThan(a: Int, b: Int) -> Bool
pub fn lessThan(a: Float, b: Float) -> Bool
pub fn equals(a: Str, b: Str) -> Bool
pub fn equals(a: Bytes, b: Bytes) -> Bool
"#;

thread_local! {
    /// Calls of `rt_alloc`: boxes the inline path did not allocate.
    static SLOW_ALLOCS: Cell<usize> = const { Cell::new(0) };
    /// Calls of `rt_release`: boxes whose count generated code took to
    /// zero, not counting the fields freed with them.
    static RELEASED: Cell<usize> = const { Cell::new(0) };
    /// Calls of `rt_text_equals`: strings compared byte by byte.
    static TEXT_COMPARES: Cell<usize> = const { Cell::new(0) };
    /// The descriptors of the module running on this thread.
    static TYPES: Cell<*const Types> = const { Cell::new(std::ptr::null()) };
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

/// Frees a box whose count generated code took to zero, with the fields
/// it releases in turn.
extern "C" fn rt_release(ctx: *mut u64, ptr: *mut u8) {
    RELEASED.set(RELEASED.get() + 1);
    // SAFETY: generated code passes the context it received and a box it
    // allocated, of a type the module describes.
    unsafe { release_box(heap_of(ctx), &*TYPES.get(), ptr) }
}

/// The descriptors of the running module.
///
/// # Safety
///
/// Called during `Module::call`.
unsafe fn types<'a>() -> &'a Types {
    // SAFETY: as the caller promises.
    unsafe { &*TYPES.get() }
}

// The list and map functions. Generated code passes the context it received
// and collections of the module's types.

extern "C" fn rt_list_push(ctx: *mut u64, list: *mut u8, w0: u64, w1: u64) -> *mut u8 {
    // SAFETY: see above.
    unsafe { list::push(heap_of(ctx), types(), list, &[w0, w1]) }
}

extern "C" fn rt_list_elem(_ctx: *mut u64, list: *mut u8, index: u64) -> *mut u64 {
    // SAFETY: see above.
    unsafe { list::get(types(), list, index as usize) }
}

extern "C" fn rt_list_slice(ctx: *mut u64, list: *mut u8, front: u64, back: u64) -> *mut u8 {
    // SAFETY: see above.
    unsafe { list::slice(heap_of(ctx), types(), list, front as usize, back as usize) }
}

extern "C" fn rt_map_insert(
    ctx: *mut u64,
    map: *mut u8,
    k0: u64,
    k1: u64,
    v0: u64,
    v1: u64,
) -> *mut u8 {
    // SAFETY: see above.
    unsafe { map::insert(heap_of(ctx), types(), map, &[k0, k1], &[v0, v1]) }
}

extern "C" fn rt_map_get(_ctx: *mut u64, map: *mut u8, k0: u64, k1: u64) -> *mut u64 {
    // SAFETY: see above.
    unsafe { map::get(types(), map, &[k0, k1]) }
}

extern "C" fn rt_text_concat(ctx: *mut u64, a0: u64, a1: u64, b0: u64, b1: u64) -> TextWords {
    // SAFETY: see above; the values are borrowed live ones.
    unsafe {
        let (a, b) = ([a0, a1], [b0, b1]);
        let parts = [text::bytes_of(&a), text::bytes_of(&b)];
        let [w0, w1] = text::make_text(heap_of(ctx), &parts);
        TextWords(w0, w1)
    }
}

extern "C" fn rt_text_equals(_ctx: *mut u64, a0: u64, a1: u64, b0: u64, b1: u64) -> u64 {
    TEXT_COMPARES.set(TEXT_COMPARES.get() + 1);
    // SAFETY: see above.
    unsafe { u64::from(text::bytes_of(&[a0, a1]) == text::bytes_of(&[b0, b1])) }
}

extern "C" fn rt_text_show(ctx: *mut u64, word: u64, number: u64) -> TextWords {
    let shown = text::show_number(Number::from_code(number).unwrap(), word);
    // SAFETY: see above.
    let [w0, w1] = text::make_text(unsafe { heap_of(ctx) }, &[shown.as_bytes()]);
    TextWords(w0, w1)
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
    types: Types,
    /// The code loaded again with the runtime's own functions, and the
    /// worker that runs it on fibers.
    fibers: (CodeArena, SymbolTable, HashMap<String, usize>),
    worker: Worker,
}

impl Module {
    fn new(text: &str) -> Module {
        Module::compiled(text, Tier::Baseline)
    }

    fn metered(text: &str) -> Module {
        Module::compiled(text, Tier::Metered)
    }

    fn compiled(text: &str, tier: Tier) -> Module {
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
        let syntax = &crag_hir::parse(&db, *module.file(&db)).errors;
        assert!(syntax.is_empty(), "{syntax:?}");
        let lowering: Vec<_> = owners(&db, module)
            .into_iter()
            .flat_map(|owner| lower_body(&db, program, owner).errors.clone())
            .collect();
        assert!(lowering.is_empty(), "{lowering:?}");
        let errors = crag_types::module_type_errors(&db, program, module);
        assert!(
            errors.is_empty(),
            "{:?}",
            errors
                .iter()
                .map(|(_, e)| e.kind.message(&db))
                .collect::<Vec<_>>()
        );
        let mut objects: Vec<(SlotKey, CodeObject)> = Vec::new();
        let mut names = Vec::new();
        let mut unsupported = Vec::new();
        let mut types = Vec::new();
        // The module's functions that are not generic, then the instances
        // and closure code they reach.
        let mut roots = Vec::new();
        for owner in owners(&db, module) {
            let Owner::Item(item) = owner else { continue };
            if *item.kind(&db) == ItemKind::Function
                && signature(&db, program, item).type_params == 0
            {
                roots.push(InstanceKey::body(&db, owner));
            }
        }
        for key in collect_instances(&db, program, &roots, tier) {
            let compiled = code(&db, program, key, tier)
                .as_ref()
                .expect("a function with a body")
                .as_ref()
                .expect("Cranelift accepts it");
            let name = match key.owner(&db) {
                Owner::Item(owner) => owner.name(&db).text(&db).clone(),
                Owner::Test(_) => "test".into(),
            };
            let body = crag_mir::mir(&db, program, key, Tier::Baseline);
            let built = body
                .iter()
                .flat_map(|b| b.unsupported.iter().map(|(_, w)| w));
            for what in built.chain(&compiled.unsupported) {
                unsupported.push(format!("{name}: {what}"));
            }
            // Each root by its name, with the index of its object.
            if roots.contains(&key) {
                names.push((name, objects.len(), compiled.params, compiled.returns));
            }
            types.extend(compiled.types.iter().cloned());
            objects.push((compiled.slot, compiled.object.clone()));
        }
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            let addr = match func {
                RuntimeFn::Alloc => rt_alloc as *const () as usize,
                RuntimeFn::Release => rt_release as *const () as usize,
                RuntimeFn::Trap => rt_trap as *const () as usize,
                RuntimeFn::ListPush => rt_list_push as *const () as usize,
                RuntimeFn::ListElem => rt_list_elem as *const () as usize,
                RuntimeFn::ListSlice => rt_list_slice as *const () as usize,
                RuntimeFn::MapInsert => rt_map_insert as *const () as usize,
                RuntimeFn::MapGet => rt_map_get as *const () as usize,
                RuntimeFn::TextConcat => rt_text_concat as *const () as usize,
                RuntimeFn::TextEquals => rt_text_equals as *const () as usize,
                RuntimeFn::TextShow => rt_text_show as *const () as usize,
                f => crag_runtime::runtime_fn_addr(f),
            };
            symbols.define_runtime(func, addr);
        }
        let mut arena = CodeArena::new(1 << 20).unwrap();
        let group: Vec<(SlotKey, &CodeObject)> = objects.iter().map(|(f, o)| (*f, o)).collect();
        let entries = load_group(&mut arena, &mut symbols, &group).unwrap();
        let mut fiber_arena = CodeArena::new(1 << 20).unwrap();
        let mut fiber_symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            fiber_symbols.define_runtime(func, crag_runtime::runtime_fn_addr(func));
        }
        let fiber_entries = load_group(&mut fiber_arena, &mut fiber_symbols, &group).unwrap();
        let mut code_map = CodeMap::new();
        for ((func, object), entry) in group.iter().zip(&fiber_entries) {
            code_map.add(func.func, entry.addr(), object);
        }
        let fiber_functions = names
            .iter()
            .map(|(name, i, ..)| (name.clone(), fiber_entries[*i].addr()))
            .collect();
        let mut worker = Worker::new();
        worker.set_types(std::sync::Arc::new(Types::new(types.iter().cloned())));
        worker.set_code_map(std::sync::Arc::new(code_map));
        let functions = names
            .into_iter()
            .map(|(name, i, params, returns)| (name, (entries[i].addr(), params, returns)))
            .collect();
        let settings = CodegenSettings {
            target: target_for("x86_64-unknown-linux-gnu").unwrap(),
            opt: OptLevel::None,
            metered: false,
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
            types: Types::new(types),
            fibers: (fiber_arena, fiber_symbols, fiber_functions),
            worker,
        }
    }

    /// Calls a function with argument words and returns its result words.
    fn call(&mut self, name: &str, args: &[u64]) -> Vec<u64> {
        let (addr, params, returns) = self.functions[name];
        assert_eq!(args.len(), params as usize, "arguments of {name}");
        let stub = compile_entry_stub(params, returns, &self.settings).unwrap();
        let stub = load(&mut self.arena, &self.symbols, &stub).unwrap();
        // The stack limit, the side stack's pointer and end, then the heap.
        let mut side = vec![0u64; 1 << 12];
        let mut ctx = [0u64; 8];
        ctx[SIDE_PTR_OFFSET as usize / 8] = side.as_mut_ptr() as u64;
        ctx[SIDE_END_OFFSET as usize / 8] = side.as_mut_ptr_range().end as u64;
        ctx[HEAP_OFFSET as usize / 8] = &raw mut *self.heap as u64;
        let mut results = [0u64; 2];
        TYPES.set(&self.types);
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

    /// Runs a function on a fiber with the runtime's own functions: its
    /// result words, or the trap that ended it.
    fn run(&mut self, name: &str, args: &[i64]) -> Result<Vec<u64>, Trap> {
        self.run_with(name, args, None, false).0
    }

    /// Runs a function as `run` does, under a meter: also the steps left.
    fn run_metered(
        &mut self,
        name: &str,
        args: &[i64],
        meter: Meter,
    ) -> (Result<Vec<u64>, Trap>, u64) {
        let (result, left) = self.run_with(name, args, Some(meter), false);
        (result, left.unwrap())
    }

    /// Runs a function as `run_metered` does, paused at every check and
    /// resumed: the meter goes on where it stopped.
    fn run_paused(&mut self, name: &str, args: &[i64], meter: Meter) -> Result<Vec<u64>, Trap> {
        self.run_with(name, args, Some(meter), true).0
    }

    fn run_with(
        &mut self,
        name: &str,
        args: &[i64],
        meter: Option<Meter>,
        pause: bool,
    ) -> (Result<Vec<u64>, Trap>, Option<u64>) {
        let (_, params, returns) = self.functions[name];
        assert_eq!(args.len(), params as usize, "arguments of {name}");
        let (arena, symbols, functions) = &mut self.fibers;
        let stub = compile_entry_stub(params, returns, &self.settings).unwrap();
        let stub = load(arena, symbols, &stub).unwrap();
        let args: Vec<u64> = args.iter().map(|&a| a as u64).collect();
        // SAFETY: the stub was compiled for this function's words, and both
        // stay loaded while the module exists, which the fiber does not
        // outlive.
        let mut fiber = unsafe {
            Fiber::new(stub.addr(), functions[name], &args, FiberConfig::default()).unwrap()
        };
        if let Some(meter) = meter {
            fiber.set_meter(meter);
        }
        let mut state = FiberState::Paused;
        while state == FiberState::Paused {
            if pause {
                request_stop(&fiber, StopReason::Pause);
            }
            state = self.worker.resume(&mut fiber);
        }
        let result = match state {
            FiberState::Finished => Ok(fiber.results().unwrap()[..returns as usize].to_vec()),
            FiberState::Trapped => Err(fiber.trap().unwrap().clone()),
            state => panic!("{name} stopped {state:?}"),
        };
        (result, fiber.steps_left())
    }

    fn int(&mut self, name: &str, args: &[i64]) -> i64 {
        let args: Vec<u64> = args.iter().map(|&a| a as u64).collect();
        match self.call(name, &args).as_slice() {
            [one] => *one as i64,
            words => panic!("{name} returned {words:?}"),
        }
    }

    /// Calls a function without parameters and prints its result through
    /// the shape of its type, then releases it.
    fn shown(&mut self, name: &str) -> String {
        let limits = PrintLimits {
            items: 5,
            ..PrintLimits::default()
        };
        self.shown_with(name, limits)
    }

    /// The shapes of the result of a function of the module.
    fn result_shapes(&self, name: &str) -> (Shapes, u32) {
        let (db, program) = (&self.db, self.program);
        let module = program.modules(db)[1];
        let owner = owners(db, module)
            .into_iter()
            .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == name))
            .unwrap();
        let ty = crag_mir::mir(db, program, InstanceKey::body(db, owner), Tier::Baseline)
            .as_ref()
            .unwrap()
            .result;
        shapes(db, program, ty)
    }

    fn shown_with(&mut self, name: &str, limits: PrintLimits) -> String {
        let words = self.call(name, &[]);
        let (shapes, root) = self.result_shapes(name);
        TYPES.set(&self.types);
        // SAFETY: the words are the function's result, of type `ty`, which
        // the call left to the test.
        unsafe {
            let text = print_value(&words, &shapes, root, &self.types, limits);
            release_value(&mut self.heap, &self.types, &words, &shapes, root);
            text
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
fn narrowed_bindings_run() {
    let mut m = Module::new(
        r#"type Nil
type Cons(head: Int, tail: Cons | Nil)
type LookupError(code: Int)
type Missing(..LookupError)

fn early(o: Option[Int]) -> Int {
  if o is Empty { return -1 }
  o + 1
}

fn options(n: Int) -> Int {
  early(n) * 10 + early(Empty)
}

fn build(n: Int, acc: Cons | Nil) -> Cons | Nil {
  if n == 0 { acc } else { build(n - 1, Cons(head: n, tail: acc)) }
}

fn sum(list: Cons | Nil, acc: Int) -> Int {
  if list is Nil { return acc }
  sum(list.tail, acc + list.head)
}

fn length(list: Cons | Nil) -> Int {
  case list {
    Nil -> 0
    _ -> 1 + length(list.tail)
  }
}

fn total(n: Int) -> Int {
  let list = build(n, Nil)
  sum(list, 0) * 1000 + length(list)
}

fn kind(r: Int | LookupError) -> Int {
  if r is Missing { return r.code * 10 }
  case r {
    n: Int -> n
    _ -> r.code
  }
}

fn kinds(n: Int) -> Int {
  kind(Missing(code: n)) + kind(LookupError(code: 1)) * 100 + kind(n) * 1000
}

fn widened(n: Int) -> Int {
  let w: Missing | Int = Missing(code: n)
  kind(w)
}

fn unwrap(o: Option[Int]) -> Int {
  let n: Int = o else { return 0 }
  n * 2
}

fn unwraps(n: Int) -> Int {
  unwrap(n) + unwrap(Empty)
}

fn vars(n: Int) -> Int {
  var v: Int | Nil = n
  if v is Nil { return 0 }
  let a = v + 1
  v = Nil
  if v is Int { return 100 }
  a
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("options", &[4]), 50 - 1);
    assert_eq!(m.int("total", &[100]), 5050 * 1000 + 100);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("kinds", &[7]), 70 + 100 + 7000);
    assert_eq!(m.int("widened", &[3]), 30);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("unwraps", &[21]), 42);
    assert_eq!(m.int("vars", &[5]), 6);
}

#[test]
fn errors_pass_to_the_caller() {
    let mut m = Module::new(
        r#"type NotFound(..Error)
type Expired(..Error, after: Int)
type Session(user: Int)

fn session(id: Int) -> Session {
  if id == 0 { return NotFound() }
  if id < 0 { Expired(after: 0 - id) } else { Session(user: id * 2) }
}

fn user(id: Int) -> Int {
  case session(id) {
    s: Session -> s.user
    e: Expired -> e.after * 100
    pass
  }
}

fn count(n: Int) -> Int {
  if n == 0 { return NotFound() }
  down(n)
}

fn down(n: Int) -> Int {
  if n == 1 { return Expired(after: 7) }
  count(n - 1)
}

fn outcome(id: Int) -> Int {
  case user(id) {
    n: Int -> n
    NotFound -> -1
  }
}

fn counted(n: Int) -> Int {
  case count(n) {
    k: Int -> k
    NotFound -> -1
    e: Expired -> e.after
  }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("outcome", &[21]), 42);
    assert_eq!(m.int("outcome", &[-3]), 300);
    assert_eq!(m.int("outcome", &[0]), -1);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("counted", &[0]), -1);
    assert_eq!(m.int("counted", &[6]), 7);
    assert_eq!(m.heap.live_blocks(), 0);
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
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn fields_are_released_with_their_box() {
    let mut m = Module::new(
        r#"type Nil
type Cons(head: Int, tail: Cons | Nil)
type Point(x: Int, y: Int)
type Line(from: Point, to: Point)

fn build(n: Int, acc: Cons | Nil) -> Cons | Nil {
  if n == 0 { acc } else { build(n - 1, Cons(head: n, tail: acc)) }
}

fn sum(list: Cons | Nil, acc: Int) -> Int {
  case list {
    Nil -> acc
    c: Cons -> sum(c.tail, acc + c.head)
  }
}

fn twice(n: Int) -> Int {
  let list = build(n, Nil)
  sum(list, 0) + sum(list, 0)
}

fn dropped(n: Int) -> Int {
  let list = build(n, Nil)
  n
}

fn second(n: Int) -> Int {
  let list = build(n, Nil)
  case list {
    Nil -> 0
    c: Cons -> sum(c.tail, 0)
  }
}

fn shared(x: Int) -> Int {
  let p = Point(x: x, y: 1)
  let line = Line(from: p, to: p)
  line.from.x + line.to.y + p.x
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    let n = 100_000;
    RELEASED.set(0);
    assert_eq!(m.int("twice", &[n]), n * (n + 1));
    // The second walk owns the list and frees each cell as it passes it.
    assert_eq!(RELEASED.get(), n as usize);
    assert_eq!(m.heap.live_blocks(), 0);
    // A list nothing reads goes with its first cell, in one call of the
    // runtime.
    RELEASED.set(0);
    assert_eq!(m.int("dropped", &[n]), n);
    assert_eq!(RELEASED.get(), 1);
    assert_eq!(m.heap.live_blocks(), 0);
    // The rest of the list is held by its first cell and by the local read
    // out of it, so it outlives the first cell when that is released first.
    assert_eq!(m.int("second", &[n]), n * (n + 1) / 2 - 1);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("shared", &[5]), 11);
    assert_eq!(m.heap.live_blocks(), 0);
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
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn what_cannot_compile_is_listed() {
    let mut m = Module::new(
        r#"fn label(n: Int) -> Int {
  let text: Option[Str] = "many"
  n
}

fn plain(n: Int) -> Int {
  n * 2
}

type Pair(a: Int, b: Int)

let Pair(a:, b:) = Pair(a: 1, b: 2)

fn first() -> Int {
  a
}
"#,
    );
    assert_eq!(
        m.unsupported,
        [
            "label: values of this type",
            "first: module-level `let`s with patterns"
        ]
    );
    assert_eq!(m.int("plain", &[21]), 42);
}

#[test]
fn strings_run() {
    let mut m = Module::new(
        r#"type Person(name: Str, age: Int)

fn greet(name: Str) -> Str { "Hello, {name}!" }
fn join(a: Str, b: Str) -> Str { "{a}{b}" }
fn hello() -> Str { greet("Ada") }
fn welcome() -> Str { greet("Ada Lovelace, Countess") }
fn report() -> Str { "{40 + 2} {0.5} {'q'} {-7}" }
fn plain() -> Str { "a literal that is long enough for a buffer" }
fn nothing() -> Str { "" }
fn braces() -> Str { "{{x}}\n\"q\"" }

fn kind(s: Str) -> Int {
  case s {
    "one" -> 1
    "a long literal compared by its bytes" -> 2
    _ -> 0
  }
}

fn kinds() -> List[Int] {
  [
    kind("one"),
    kind("a long literal compared by its bytes"),
    kind(join("on", "e")),
    kind("two"),
    kind(join("a long literal compared ", "by its bytes")),
  ]
}

fn same() -> List[Bool] {
  [
    join("a", "b") == "ab",
    join("a long one, ", "made at run time") == "a long one, made at run time",
    join("a long one, ", "made at run time") == "a long one, made at run time!",
    "short" == "a long string that is not short",
  ]
}

fn people() -> List[Person] {
  [Person(name: "Ada", age: 36), Person(name: "Alan Mathison Turing", age: 41)]
}
fn ages() -> Map[Str, Int] { ["ada": 36, "alan mathison turing": 41] }
fn lookup() -> Option[Int] { ages()[join("alan mathison ", "turing")] }
fn data() -> Bytes { b"\x00\xff and enough bytes for a buffer" }
fn names() -> Set[Str] { ["b", "a", "a long name in a set of names", "b"] }

let motto = "a module-level value that holds a long string"
fn mottoOf() -> Str { motto }

fn copies() -> List[Str] {
  let s = join("a string in a buffer, ", "copied by interpolation")
  ["{s}", s]
}
"#,
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    let expected = [
        ("hello", r#""Hello, Ada!""#),
        ("welcome", r#""Hello, Ada Lovelace, Countess!""#),
        ("report", r#""42 0.5 q -7""#),
        ("plain", r#""a literal that is long enough for a buffer""#),
        ("nothing", r#""""#),
        ("braces", r#""{{x}}\n\"q\"""#),
        ("kinds", "[1, 2, 1, 0, 2]"),
        ("same", "[True, True, False, False]"),
        (
            "people",
            r#"[Person(name: "Ada", age: 36), Person(name: "Alan Mathison Turing", age: 41)]"#,
        ),
        ("ages", r#"["ada": 36, "alan mathison turing": 41]"#),
        ("lookup", "41"),
        ("data", r#"b"\x00\xff and enough bytes for a buffer""#),
        ("names", r#"["a", "a long name in a set of names", "b"]"#),
        (
            "mottoOf",
            r#""a module-level value that holds a long string""#,
        ),
        (
            "mottoOf",
            r#""a module-level value that holds a long string""#,
        ),
        // One part, which the result shares with a reference of its own.
        (
            "copies",
            r#"["a string in a buffer, copied by interpolation", "a string in a buffer, copied by interpolation"]"#,
        ),
    ];
    TEXT_COMPARES.set(0);
    for (name, shown) in expected {
        assert_eq!(m.shown(name), shown, "{name}");
        // The cell holds a static string, which takes no block.
        assert_eq!(m.heap.live_blocks(), 0, "{name}");
    }
    // Only strings in buffers of the same length that differ in their
    // words are compared by the runtime: a buffer made at run time and a
    // literal's, or the literals of two functions.
    assert_eq!(TEXT_COMPARES.get(), 3);
    // Short strings are inline, long ones point at their buffer.
    let words = m.call("hello", &[]);
    assert_eq!(words, inline_text(b"Hello, Ada!"));
}

#[test]
fn strings_run_on_fibers_and_unwind() {
    let mut m = Module::new(
        r#"fn greet(name: Str) -> Str { "Hello, {name}, who is {40 + 2}!" }
fn kind(s: Str) -> Int {
  case s {
    "Hello, someone with a long name, who is 42!" -> 2
    _ -> 0
  }
}
fn ratio(a: Int, b: Int) -> Int { a / b }
fn holds(n: Int) -> Int {
  let long = greet("someone with a long name")
  let short = "x"
  let k = ratio(10, n)
  kind(long) + k + kind(short)
}
"#,
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    assert_eq!(m.run("holds", &[5]), Ok(vec![4]));
    assert_eq!(m.worker.heap().live_blocks(), 0);
    // The frame of `holds` keeps both strings across the call that traps;
    // the unwinder releases the buffer and skips the inline one.
    let trap = m.run("holds", &[0]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::DivideByZero);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn collections_run() {
    // A literal long enough to need a tree of several leaves.
    let long: Vec<String> = (1..=100).map(|i| i.to_string()).collect();
    let long = long.join(", ");
    let mut m = Module::new(&format!(
        r#"type Point(x: Int, y: Int)

fn total(xs: List[Int]) -> Int {{
  var sum = 0
  for x in xs {{
    sum = sum + x
  }}
  sum
}}

fn literal(i: Int) -> Int {{
  let xs = [1, 2, 3, 4, 5]
  total(xs) * 100 + xs[i]
}}

fn long() -> List[Int] {{
  [{long}]
}}

fn walk(xs: List[Int], acc: Int) -> Int {{
  case xs {{
    [] -> acc
    [x, ..rest] -> walk(rest, acc + x)
  }}
}}

fn ends(xs: List[Int]) -> Int {{
  case xs {{
    [] -> 0
    [x] -> x
    [a, .., b] -> a * 1000 + b
  }}
}}

fn walked(n: Int) -> Int {{
  let xs = long()
  walk(xs, 0) + ends(xs) + ends([n]) + ends([])
}}

fn points(n: Int) -> Int {{
  let ps = [Point(x: n, y: 2), Point(x: 3, y: 4)]
  var sum = 0
  for p in ps {{
    sum = sum + p.x * p.y
  }}
  case ps {{
    [first, ..] -> sum + first.x
    [] -> 0
  }}
}}

fn options(n: Int) -> Int {{
  let xs: List[Option[Int]] = [n, Empty, 5]
  var sum = 0
  for x in xs {{
    case x {{
      Empty -> {{ sum = sum + 1000 }}
      v: Int -> {{ sum = sum + v }}
    }}
  }}
  sum
}}

fn lookup(k: Int) -> Int {{
  let ages = [1: 10, 2: 20, 3: Point(x: 30, y: 0).x]
  case ages[k] {{
    Empty -> -1
    v: Int -> v
  }}
}}

fn nested(k: Int) -> Int {{
  let places = [1: Point(x: 7, y: 8), 2: Point(x: 9, y: 10)]
  case places[k] {{
    Empty -> -1
    p: Point -> p.x + p.y
  }}
}}

fn grid(i: Int) -> Int {{
  let rows = [[1, 2], [3], [i, 5, 6]]
  rows[0][1] + rows[1][0] + rows[2][0] * 10
}}

fn sets(n: Int) -> Int {{
  let s: Set[Int] = [1, 2, 2, n]
  n
}}
"#
    ));
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("literal", &[0]), 1501);
    assert_eq!(m.int("literal", &[4]), 1505);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("walked", &[7]), 5050 + 1100 + 7);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("points", &[5]), 10 + 12 + 5);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("options", &[3]), 1008);
    assert_eq!(m.heap.live_blocks(), 0);
    let found: Vec<i64> = (0..5).map(|k| m.int("lookup", &[k])).collect();
    assert_eq!(found, [-1, 10, 20, 30, -1]);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("nested", &[2]), 19);
    assert_eq!(m.int("nested", &[3]), -1);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("grid", &[4]), 45);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("sets", &[9]), 9);
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn traps_end_the_fiber_and_release_what_it_holds() {
    let text = r#"type Point(x: Int, y: Int)

fn inc(n: Int) -> Int {
  n + 1
}

fn deep(n: Int, p: Point) -> Int {
  if n == 0 {
    p.x / (p.y - p.y)
  } else {
    let q = Point(x: n, y: 1)
    deep(n - 1, p) + q.x
  }
}

fn start(n: Int) -> Int {
  deep(n, Point(x: 1, y: 2))
}

fn pick(i: Int) -> Int {
  let points = [Point(x: 1, y: 2), Point(x: 3, y: 4)]
  let p = points[i]
  p.x + p.y
}
"#;
    let mut m = Module::new(text);
    assert_eq!(m.unsupported, Vec::<String>::new());
    let at = |what: &str| Some(text.find(what).unwrap() as u32);
    assert_eq!(m.run("inc", &[41]), Ok(vec![42]));
    let trap = m.run("inc", &[i64::MAX]).unwrap_err();
    assert_eq!(
        (trap.kind, trap.position),
        (TrapKind::Overflow, at("n + 1"))
    );
    assert_eq!(trap.stack.len(), 1);
    // Every frame holds a point across its call when the last one traps.
    let trap = m.run("start", &[1000]).unwrap_err();
    assert_eq!(
        (trap.kind, trap.position),
        (TrapKind::DivideByZero, at("p.x / (p.y - p.y)"))
    );
    // `deep` 1001 times; `start` tail-called the first, so its frame is
    // gone.
    assert_eq!(trap.stack.len(), 1001);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    assert_eq!(m.run("pick", &[1]), Ok(vec![7]));
    let trap = m.run("pick", &[2]).unwrap_err();
    assert_eq!(
        (trap.kind, trap.position),
        (TrapKind::Index, at("points[i]"))
    );
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn metered_code_runs_out_of_steps_and_memory() {
    let text = r#"type Point(x: Int, y: Int)

fn spin(n: Int) -> Int {
  var t = 0
  for i in 1..n {
    t = t + i
  }
  t
}

fn hold(n: Int, p: Point) -> Int {
  if n == 0 { p.x } else { hold(n - 1, Point(x: p.x + 1, y: p.y)) + p.y }
}

fn start(n: Int) -> Int {
  hold(n, Point(x: 0, y: 1))
}

fn churn(n: Int) -> Int {
  var t = 0
  for i in 1..n {
    let p = Point(x: i, y: i)
    t = t + p.x - p.y
  }
  t
}

type End
type Node(value: Int, next: Node | End)

fn chain(k: Int) -> Int {
  var n: Node | End = End
  for i in 1..k {
    n = Node(value: i, next: n)
  }
  case n {
    Node(value:) -> value
    End -> 0
  }
}

fn waves(k: Int) -> Int {
  var t = 0
  for i in 1..k {
    t = t + chain(5000)
  }
  t
}

fn depth(n: Int) -> Int {
  if n == 0 { 0 } else { depth(n - 1) + 1 }
}
"#;
    let mut m = Module::metered(text);
    assert_eq!(m.unsupported, Vec::<String>::new());
    let ample = |steps| Meter {
        steps,
        memory: usize::MAX,
    };
    // Ten steps: the entry, and the back-edge after each turn of the loop
    // but the last.
    assert_eq!(m.run_metered("spin", &[10], ample(100)), (Ok(vec![55]), 90));
    assert_eq!(m.run_metered("spin", &[10], ample(10)), (Ok(vec![55]), 0));
    let (trap, left) = m.run_metered("spin", &[10], ample(9));
    let trap = trap.unwrap_err();
    assert_eq!(
        (trap.kind, trap.position, left),
        (TrapKind::OutOfSteps, None, 0)
    );
    assert_eq!(trap.stack.len(), 1);
    // A long computation is stopped, and what its frames hold released.
    let (trap, _) = m.run_metered("start", &[1_000_000], ample(1000));
    assert_eq!(trap.unwrap_err().kind, TrapKind::OutOfSteps);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    assert_eq!(
        m.run_metered("start", &[1000], ample(10_000)).0,
        Ok(vec![2000])
    );

    // A chain holds its nodes of 40 bytes, made in a loop, so only the
    // heap grows. The loop's range is a box of 32 bytes, whose refill
    // carves 4 KiB; a refill of nodes carves 102 of them, 4080 bytes, and
    // seven fit what is left of 32 KiB: the 715th node goes beyond it. The
    // trap comes at the next step, the loop's back-edge, which a chain of
    // 715 never reaches.
    let budget = |memory| Meter {
        steps: u64::MAX,
        memory,
    };
    let fresh = |k| {
        let mut m = Module::metered(text);
        let result = m.run_metered("chain", &[k], budget(32 << 10)).0;
        assert_eq!(m.worker.heap().live_blocks(), 0);
        result
    };
    assert_eq!(fresh(714), Ok(vec![714]));
    assert_eq!(fresh(715), Ok(vec![715]));
    let trap = fresh(716).unwrap_err();
    assert_eq!((trap.kind, trap.stack.len()), (TrapKind::OutOfMemory, 1));
    // A point made and dropped each turn reuses its block.
    let mut m = Module::metered(text);
    assert_eq!(
        m.run_metered("churn", &[100_000], budget(32 << 10)).0,
        Ok(vec![0])
    );
    // Each wave holds 5000 nodes, more than three pages, and gives them
    // back when it is done: what pages that empty give back is charged
    // again.
    assert_eq!(
        m.run_metered("waves", &[10], budget(256 << 10)).0,
        Ok(vec![50_000])
    );
    // The stack is memory too: the frames of a deep recursion do not fit.
    let trap = m.run_metered("depth", &[100_000], budget(64 << 10)).0;
    assert_eq!(trap.unwrap_err().kind, TrapKind::OutOfMemory);
    assert_eq!(
        m.run_metered("depth", &[100], budget(64 << 10)).0,
        Ok(vec![100])
    );
    // A fiber stopped and resumed keeps what is left of its budget, so the
    // trap comes however often it is resumed.
    let mut m = Module::metered(text);
    let trap = m
        .run_paused("chain", &[100_000], budget(32 << 10))
        .unwrap_err();
    assert_eq!(trap.kind, TrapKind::OutOfMemory);
    assert_eq!(
        m.run_paused("spin", &[100_000], ample(1000))
            .unwrap_err()
            .kind,
        TrapKind::OutOfSteps
    );
}

#[test]
fn values_decode_to_what_they_encode() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Point3(..Point, z: Int)
type Nil
type Cons(head: Int, tail: Cons | Nil)

fn deep() -> Point { Point3(x: 1, y: 2, z: 3) }
fn chain() -> Cons { Cons(head: 1, tail: Cons(head: 2, tail: Nil)) }
fn points() -> List[Point] { [Point(x: 1, y: 2), Point3(x: 3, y: 4, z: 5)] }
fn ages() -> Map[Int, List[Int]] { [2: [20], 1: [10, 11], 3: []] }
fn set() -> Set[Int] { [3, 1, 2] }
fn maybe() -> Option[Point] { Point(x: 5, y: 6) }
fn none() -> Option[Point] { Empty }
fn tags() -> List[Bool] { [True, False, True] }
fn mixed() -> (a: Fixed[2], b: List[Option[Int]], c: Float) { (a: 1.25, b: [1, Empty], c: 0.5) }
fn empty() -> List[Int] { [] }
fn nothing() -> Map[Int, Int] { [:] }
type Pair(u: Int, v: Int)
fn both() -> (p: Point, w: Pair) { (p: Point(x: 1, y: 2), w: Pair(u: 1, v: 2)) }
fn words() -> Map[Str, List[Str]] {
  ["k": ["a", "a string long enough for a buffer"], "a key long enough for a buffer": []]
}
fn texts() -> (name: Str, data: Bytes, none: Str) {
  (name: "Grüße aus Crag, lang genug", data: b"\x00\xff", none: "")
}
"#,
    );
    let names = [
        "deep", "chain", "points", "ages", "set", "maybe", "none", "tags", "mixed", "empty",
        "nothing", "both", "words", "texts",
    ];
    let limits = PrintLimits::default();
    for name in names {
        let words = m.call(name, &[]);
        let (shapes, root) = m.result_shapes(name);
        let types = &m.types;
        TYPES.set(types);
        // SAFETY: the words are the function's result, of the shape, and
        // the decoded value is built for the module's types.
        unsafe {
            let bytes = encode_value(&words, &shapes, root, types).unwrap();
            let decoded = decode_value(&bytes, &shapes, root, &mut m.heap, types).unwrap();
            assert_eq!(
                encode_value(&decoded, &shapes, root, types).unwrap(),
                bytes,
                "{name}"
            );
            assert_eq!(
                print_value(&decoded, &shapes, root, types, limits),
                print_value(&words, &shapes, root, types, limits),
                "{name}"
            );
            release_value(&mut m.heap, types, &words, &shapes, root);
            release_value(&mut m.heap, types, &decoded, &shapes, root);
        }
        assert_eq!(m.heap.live_blocks(), 0, "{name}");
    }

    // Bytes that do not fit the shape are refused, and nothing is left.
    let words = m.call("points", &[]);
    let (shapes, root) = m.result_shapes("points");
    let types = &m.types;
    // SAFETY: as above.
    let bytes = unsafe { encode_value(&words, &shapes, root, types).unwrap() };
    unsafe { release_value(&mut m.heap, types, &words, &shapes, root) };
    let mut broken = vec![
        bytes[..bytes.len() - 1].to_vec(),
        [&bytes[..], &[0]].concat(),
        // A length beyond the bytes.
        [&[9, 0, 0, 0, 0, 0, 0, 0][..], &bytes[8..]].concat(),
    ];
    // The first point's box of a shape that is no record.
    let mut not_record = bytes.clone();
    not_record[8..12].copy_from_slice(&(root).to_le_bytes());
    broken.push(not_record);
    let mut no_shape = bytes.clone();
    no_shape[8..12].copy_from_slice(&999u32.to_le_bytes());
    broken.push(no_shape);
    for (i, b) in broken.iter().enumerate() {
        // SAFETY: as above.
        let result = unsafe { decode_value(b, &shapes, root, &mut m.heap, types) };
        assert!(result.is_err(), "broken {i}");
    }
    // A box of a record type that is no subtype of the field's, though laid
    // out alike: `Pair` for the `Point` of `both`, and the other way.
    let words = m.call("both", &[]);
    let (shapes, root) = m.result_shapes("both");
    // SAFETY: as above.
    let bytes = unsafe { encode_value(&words, &shapes, root, &m.types).unwrap() };
    unsafe { release_value(&mut m.heap, &m.types, &words, &shapes, root) };
    let shape_at = |at: usize| u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap());
    // The outer record, then `p`'s shape and two words, then `w`'s shape.
    let (point, wide) = (shape_at(4), shape_at(4 + 4 + 16));
    let mut swapped = bytes.clone();
    swapped[4..8].copy_from_slice(&wide.to_le_bytes());
    swapped[4 + 4 + 16..4 + 4 + 16 + 4].copy_from_slice(&point.to_le_bytes());
    // SAFETY: as above.
    let result = unsafe { decode_value(&swapped, &shapes, root, &mut m.heap, &m.types) };
    assert!(result.is_err());
    let (shapes, root) = m.result_shapes("maybe");
    // SAFETY: as above.
    let member = unsafe { decode_value(&[7, 0, 0, 0], &shapes, root, &mut m.heap, &m.types) };
    assert!(member.is_err());
    // A string decodes only from UTF-8, and bytes from anything.
    let words = m.call("texts", &[]);
    let (shapes, root) = m.result_shapes("texts");
    // SAFETY: as above.
    let bytes = unsafe { encode_value(&words, &shapes, root, &m.types).unwrap() };
    unsafe { release_value(&mut m.heap, &m.types, &words, &shapes, root) };
    // The record's shape, then its fields by name: the bytes, the name
    // and the empty string, each its length and then its bytes.
    let name = "Grüße aus Crag, lang genug".len();
    assert_eq!(bytes.len(), 4 + 8 + 2 + 8 + name + 8);
    assert_eq!(bytes[4..12], 2u64.to_le_bytes());
    assert_eq!(bytes[14..22], (name as u64).to_le_bytes());
    let mut not_utf8 = bytes.clone();
    not_utf8[22] = 0xff;
    // SAFETY: as above.
    let result = unsafe { decode_value(&not_utf8, &shapes, root, &mut m.heap, &m.types) };
    assert!(result.is_err());
    let mut other_bytes = bytes.clone();
    other_bytes[12] = 0xfe;
    // SAFETY: as above.
    unsafe {
        let decoded = decode_value(&other_bytes, &shapes, root, &mut m.heap, &m.types).unwrap();
        let shown = print_value(&decoded, &shapes, root, &m.types, limits);
        assert_eq!(
            shown,
            r#"(data: b"\xfe\xff", name: "Grüße aus Crag, lang genug", none: "")"#
        );
        release_value(&mut m.heap, &m.types, &decoded, &shapes, root);
    }
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn module_values_are_computed_once_and_kept() {
    let text = r#"type Point(x: Int, y: Int)

let base = 40
let origin = Point(x: base, y: 2)
let answer: Int = base + two()
let bad: Int = 1 / zero()
let made = make()

fn make() -> Point { Point(x: 1, y: 1) }
fn two() -> Int { 2 }
fn zero() -> Int { 0 }

fn read() -> Int { answer + origin.y }
fn point() -> Point { origin }
fn madePoint() -> Point { made }
fn broken() -> Int { bad }
"#;
    let mut m = Module::new(text);
    assert_eq!(m.unsupported, Vec::<String>::new());
    RELEASED.set(0);
    assert_eq!(m.int("read", &[]), 44);
    // The cell keeps the point, and every read gives the same one with a
    // reference of its own.
    assert_eq!(m.heap.live_blocks(), 1);
    let (p, q) = (m.call("point", &[]), m.call("point", &[]));
    assert_eq!(p, q);
    // SAFETY: the point is alive, held by its cell and both results.
    let count = unsafe { (p[0] as *const u64).read() };
    assert_eq!(count, 3);
    assert_eq!(RELEASED.get(), 0);
    assert_eq!(m.heap.live_blocks(), 1);
    // A value that is a call keeps what the call gives: it is no tail call.
    assert_eq!(m.call("madePoint", &[]), m.call("madePoint", &[]));
    assert_eq!(m.heap.live_blocks(), 2);

    // A trap while a value is computed leaves its cell empty, so the next
    // read computes it again.
    for _ in 0..2 {
        let trap = m.run("broken", &[]).unwrap_err();
        let at = text.find("1 / zero()").unwrap() as u32;
        assert_eq!(
            (trap.kind, trap.position),
            (TrapKind::DivideByZero, Some(at))
        );
        // `broken` and the code of `bad`.
        assert_eq!(trap.stack.len(), 2);
    }
    assert_eq!(m.run("read", &[]), Ok(vec![44]));
    assert_eq!(m.worker.heap().live_blocks(), 1);
}

#[test]
fn values_print_by_the_shapes_of_their_types() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Point3(..Point, z: Int)
type Pair(second: Int, first: Int)
type Nil
type Cons(head: Int, tail: Cons | Nil)

fn point() -> Point { Point(x: 1, y: -2) }
fn deeper() -> Point { Point3(x: 1, y: 2, z: 3) }
fn pair() -> Pair { Pair(second: 2, first: 1) }
fn anon() -> (b: Bool, a: Float) { (b: 1 < 2, a: 0.5) }
fn chain() -> Cons | Nil { Cons(head: 1, tail: Cons(head: 2, tail: Nil)) }
fn options() -> List[Option[Int]] { [3, Empty, 5] }
fn points() -> List[Point] { [Point(x: 1, y: 2), Point3(x: 3, y: 4, z: 5)] }
fn many() -> List[Int] { [1, 2, 3, 4, 5, 6, 7] }
fn ages() -> Map[Int, Point] { [2: Point(x: 20, y: 0), 1: Point(x: 10, y: 0)] }
fn none() -> Map[Int, Int] { [:] }
fn set() -> Set[Int] { [3, 1, 2, 1] }
fn cents() -> Fixed[2] { 12.05 }
fn small() -> UInt8 { 255 }
fn letter() -> CodePoint { 'q' }
fn nothing() -> Option[Int] { Empty }
fn adder() -> (Int) -> Int {
  let p = point()
  { n -> n + p.x }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    let shown = |m: &mut Module, name: &str| m.shown(name);
    assert_eq!(shown(&mut m, "point"), "Point(x: 1, y: -2)");
    // A box shows its own type, a subtype's fields included.
    assert_eq!(shown(&mut m, "deeper"), "Point3(x: 1, y: 2, z: 3)");
    // Fields in the order they are declared, not laid out.
    assert_eq!(shown(&mut m, "pair"), "Pair(second: 2, first: 1)");
    assert_eq!(shown(&mut m, "anon"), "(a: 0.5, b: True)");
    assert_eq!(
        shown(&mut m, "chain"),
        "Cons(head: 1, tail: Cons(head: 2, tail: Nil))"
    );
    assert_eq!(shown(&mut m, "options"), "[3, Empty, 5]");
    assert_eq!(
        shown(&mut m, "points"),
        "[Point(x: 1, y: 2), Point3(x: 3, y: 4, z: 5)]"
    );
    assert_eq!(shown(&mut m, "many"), "[1, 2, 3, 4, 5, … 2 more]");
    // Entries by their keys.
    assert_eq!(
        shown(&mut m, "ages"),
        "[1: Point(x: 10, y: 0), 2: Point(x: 20, y: 0)]"
    );
    assert_eq!(shown(&mut m, "none"), "[:]");
    assert_eq!(shown(&mut m, "set"), "[1, 2, 3]");
    assert_eq!(shown(&mut m, "cents"), "12.05");
    assert_eq!(shown(&mut m, "small"), "255");
    assert_eq!(shown(&mut m, "letter"), "'q'");
    assert_eq!(shown(&mut m, "nothing"), "Empty");
    assert_eq!(shown(&mut m, "adder"), "<function>");
    // Deep and long values are cut short.
    let limits = PrintLimits {
        depth: 1,
        ..PrintLimits::default()
    };
    assert_eq!(
        m.shown_with("chain", limits),
        "Cons(head: 1, tail: Cons(head: …, tail: …))"
    );
    let limits = PrintLimits {
        chars: 10,
        ..PrintLimits::default()
    };
    assert_eq!(m.shown_with("many", limits), "[1, 2, 3, …]");
    // Every value was released after it was shown.
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn lifted_calls_run() {
    let mut m = Module::new(
        r#"type Circle(r: Int)
type Rect(w: Int, h: Int)

fn area(c: Circle) -> Int { 3 * c.r * c.r }
fn area(r: Rect) -> Int { r.w * r.h }

fn shape(n: Int) -> Circle | Rect {
  if 0 < n { Circle(r: n) } else { Rect(w: 2, h: 0 - n) }
}

fn areas(n: Int) -> Int {
  area(shape(n)) + shape(0 - n).area() * 1000
}

fn pair(a: Circle, b: Circle) -> Int { 1 }
fn pair(a: Circle, b: Rect) -> Int { 2 }
fn pair(a: Rect, b: Circle | Rect) -> Int { 3 }

fn pairs(n: Int) -> Int {
  pair(shape(n), shape(n)) + pair(shape(n), shape(0 - n)) * 10 + pair(shape(0 - n), shape(n)) * 100
}

fn flip(x: Int | Float) -> Int | Float { -x }

fn flips(n: Int) -> Int {
  case flip(n) {
    i: Int -> i
    _ -> 0
  }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("areas", &[2]), 12 + 4 * 1000);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("pairs", &[2]), 1 + 2 * 10 + 3 * 100);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("flips", &[5]), -5);
}

#[test]
fn unit_records_are_values() {
    // A record type without fields has one value, written by its name
    // like a tag's (§3.3).
    let mut m = Module::new(
        r#"type Overdrawn(..Error)
type Done()

fn withdraw(balance: Int, amount: Int) -> Int | Overdrawn {
  if balance < amount { return Overdrawn }
  balance - amount
}

fn left(balance: Int, amount: Int) -> Int {
  case withdraw(balance, amount) {
    Overdrawn -> -1
    n: Int -> n
  }
}

fn finish(n: Int) -> Int {
  let d: Done | Int = if n < 0 { Done } else { n }
  case d {
    Done -> 0
    k: Int -> k
  }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("left", &[10, 3]), 7);
    assert_eq!(m.int("left", &[1, 3]), -1);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("finish", &[-4]), 0);
    assert_eq!(m.int("finish", &[4]), 4);
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn closures_run() {
    // A closure is its code and an environment of what it captures: on
    // the side stack when it does not outlive its frame, on the heap when
    // it escapes or is made in a loop (§11.5.9).
    let mut m = Module::new(
        r#"type Cell(n: Int)

fn apply(f: (Int) -> Int, x: Int) -> Int {
  f(x)
}

fn shifted(k: Int, x: Int) -> Int {
  let c = Cell(n: k)
  apply({ n -> n + c.n }, x)
}

fn reused(k: Int, x: Int) -> Int {
  let c = Cell(n: k)
  apply({ n -> Cell(n: n).n + c.n }, x)
}

fn adder(k: Int) -> (Int) -> Int {
  let c = Cell(n: k)
  { n -> n + c.n }
}

fn added(k: Int, x: Int) -> Int {
  let f = adder(k)
  f(x) + f(x)
}

fn sumTo(n: Int, step: Int) -> Int {
  fn go(m: Int) -> Int {
    if m < 1 { 0 } else { m + go(m - step) }
  }
  go(n)
}

fn neg(n: Int) -> Int {
  0 - n
}

fn negated(x: Int) -> Int {
  apply(neg, x)
}

fn both(f: (Int, Int) -> Int, x: Int) -> Int {
  f(x, x)
}

fn doubled(x: Int) -> Int {
  both(add, x)
}

fn nested(a: Int, x: Int) -> Int {
  let c = Cell(n: a)
  apply({ n -> apply({ m -> m + c.n }, n) * 2 }, x)
}

fn composed(x: Int) -> Int {
  let fs = [adder(1), adder(10)]
  var total = x
  for f in fs {
    total = f(total)
  }
  total
}

fn looped(n: Int) -> Int {
  var total = 0
  for i in 1..n {
    let c = Cell(n: i)
    total = apply({ m -> m + c.n }, total)
  }
  total
}

fn minus(a: Int, b: Int) -> Int {
  a - b
}

fn partial(x: Int) -> Int {
  apply(minus(_, 1), x)
}

fn forward(k: Int, x: Int) -> Int {
  let f = adder(k)
  f(x)
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("shifted", &[5, 3]), 8);
    assert_eq!(m.heap.live_blocks(), 0);
    // The captured cell lives while the closure does, so the cell made
    // inside it is another.
    assert_eq!(m.int("reused", &[5, 3]), 8);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("added", &[5, 3]), 16);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("sumTo", &[10, 3]), 22);
    assert_eq!(m.int("negated", &[4]), -4);
    assert_eq!(m.int("doubled", &[21]), 42);
    assert_eq!(m.int("nested", &[3, 4]), 14);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("composed", &[0]), 11);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("looped", &[4]), 10);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("partial", &[8]), 7);
    assert_eq!(m.int("forward", &[2, 3]), 5);
    assert_eq!(m.heap.live_blocks(), 0);
    // A trap in a closure releases the environments the frames hold.
    let trap = m.run("added", &[1, i64::MAX]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    let trap = m.run("shifted", &[1, i64::MAX]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn tail_calls_take_closures_along() {
    // A tail call pops the caller's side stack, so a closure it passes or
    // calls is on the heap; one it does not take along stays behind and
    // is popped (§11.5.11). None of these loops grows a stack.
    let mut m = Module::new(
        r#"type Cell(n: Int)

fn apply(f: (Int) -> Int, x: Int) -> Int {
  f(x)
}

fn over(f: (Int) -> Int, x: Int) -> Int {
  let r = apply({ m -> m + 0 * x }, x)
  f(r)
}

fn passed(k: Int, x: Int) -> Int {
  let c = Cell(n: k)
  over({ n -> n + c.n }, x)
}

fn wrapped(k: Int, x: Int) -> Int {
  let c = Cell(n: k)
  let f: (Int) -> Int = { n -> n + c.n }
  over({ n -> f(n) * 2 }, x)
}

fn rounds(k: Int, n: Int, acc: Int) -> Int {
  let c = Cell(n: k)
  if n == 0 { acc } else { relay({ m -> m + c.n }, k, n - 1, acc) }
}

fn relay(f: (Int) -> Int, k: Int, n: Int, acc: Int) -> Int {
  rounds(k, n, f(acc))
}

fn countdown(n: Int, k: Int) -> Int {
  fn go(m: Int) -> Int {
    let r = apply({ x -> x + 0 * m }, m)
    if r == 0 { k } else { go(r - 1) }
  }
  go(n)
}

fn kept(k: Int, n: Int) -> Int {
  let c = Cell(n: k)
  let r = apply({ m -> m + c.n }, 0)
  if n == 0 { r } else { kept(k, n - 1) }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    // The callee's own side-stack closure lies where the caller's was.
    assert_eq!(m.int("passed", &[5, 3]), 8);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("wrapped", &[3, 4]), 14);
    assert_eq!(m.heap.live_blocks(), 0);
    // Deep enough to overflow the thread's stack without tail calls.
    assert_eq!(m.int("rounds", &[2, 1_000_000, 0]), 2_000_000);
    assert_eq!(m.heap.live_blocks(), 0);
    // `go` calls itself with the environment it was called with, after
    // its own closure has gone on the side stack.
    assert_eq!(m.int("countdown", &[1_000_000, 7]), 7);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("kept", &[4, 1_000_000]), 4);
    assert_eq!(m.heap.live_blocks(), 0);
    // A trap in the callee releases the environment it was passed.
    let trap = m.run("passed", &[1, i64::MAX]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    let trap = m.run("rounds", &[i64::MAX, 3, 1]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn generic_functions_run_per_instance() {
    // A generic function is compiled once per type arguments and slot
    // fillings it is called with (§11.5.10).
    let mut m = Module::new(
        r#"type Shape(pos: Int)
type Circle(..Shape, r: Int)
type Point(x: Int, y: Int)
type Pair[A, B](first: A, second: B)

form Sizable[U] {
  size(u: U) -> Int
}

fn size(p: Point) -> Int {
  p.x * p.y
}

fn size(n: Int) -> Int {
  n
}

fn identity[T](x: T) -> T {
  x
}

fn biggest[T: Sizable](a: T, b: T) -> T {
  if size(a) < size(b) { b } else { a }
}

fn twice[A: Sizable](a: A) -> Int {
  size(biggest(a, a)) * 2
}

fn pos[S: Shape](s: S) -> Int {
  s.pos
}

fn apply[A, B](a: A, f: (A) -> B) -> B {
  f(a)
}

fn swap[A, B](p: Pair[A, B]) -> Pair[B, A] {
  Pair[B, A](first: p.second, second: p.first)
}

fn orZero[T: Sizable](o: Option[T]) -> Int {
  case o {
    Empty -> 0
    v: T -> size(v)
  }
}

fn nest[T](x: T, n: Int) -> Int {
  if n == 0 { 0 } else { nest(Pair[T, T](first: x, second: x), n - 1) + 1 }
}

fn same(x: Int) -> Int {
  identity(x) + identity(Point(x: x, y: 1)).x
}

fn larger(x: Int) -> Int {
  biggest(Point(x: x, y: 2), Point(x: 3, y: 3)).y
}

fn doubled(x: Int) -> Int {
  twice(Point(x: x, y: 1)) + twice(x)
}

fn circle(x: Int) -> Int {
  pos(Circle(pos: x, r: 1))
}

fn tripled(x: Int) -> Int {
  apply(x, { n -> n * 3 })
}

fn swapped(x: Int) -> Int {
  let p = swap(Pair[Int, Point](first: x, second: Point(x: 1, y: 2)))
  p.first.y + p.second
}

fn optional(x: Int) -> Int {
  let o: Option[Point] = if 0 < x { Point(x: x, y: 2) } else { Empty }
  orZero[Point](o)
}

fn nested(n: Int) -> Int {
  nest(1, n)
}

fn kept[T](x: T) -> T {
  let f = { y: T -> y }
  f(x)
}

fn closed(x: Int) -> Int {
  kept(x) + kept(Point(x: x, y: 1)).y
}
"#,
    );
    // Each call of `nest` adds a level of `Pair`, so its instances stop
    // at a depth, where the call traps.
    assert_eq!(
        m.unsupported,
        ["nest: instances whose type arguments nest this deeply"]
    );
    assert_eq!(m.int("same", &[4]), 8);
    assert_eq!(m.int("larger", &[2]), 3);
    assert_eq!(m.int("larger", &[5]), 2);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("doubled", &[5]), 20);
    assert_eq!(m.int("circle", &[7]), 7);
    assert_eq!(m.int("tripled", &[7]), 21);
    assert_eq!(m.int("swapped", &[5]), 7);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("optional", &[3]), 6);
    assert_eq!(m.int("optional", &[-3]), 0);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("closed", &[4]), 5);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("nested", &[3]), 3);
    assert_eq!(m.heap.live_blocks(), 0);
    let trap = m.run("nested", &[40]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Unsupported);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}
