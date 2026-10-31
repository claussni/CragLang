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
    Frame, FuncId, HEADER_SIZE, HEAP_OFFSET, Number, RuntimeFn, SIDE_END_OFFSET, SIDE_PTR_OFFSET,
    Shapes, TrapKind, inline_text,
};
use crag_backend::{code, flat_layouts, flat_params, func_id, scalar_replace, shapes, type_index};
use crag_codegen::{
    CodeObject, CodegenSettings, OptLevel, SlotKey, compile_entry_stub, target_for,
};
use crag_db::RootDatabase;
use crag_hir::{ItemKind, ModuleId, Owner, Program, Resource, SourceFile, lower_body, owners};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_mir::{InstanceKey, Tier, collect_instances};
use crag_runtime::text::TextWords;
use crag_runtime::{
    CodeMap, Disposal, Fiber, FiberConfig, FiberState, Heap, Meter, PrintLimits, StopReason, Trap,
    Types, Worker, alloc_box, decode_value, encode_value, list, map, next_disposal, print_value,
    release_box, release_value, request_stop, text,
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
pub type Oks[X]
pub type Errs[X]
pub type Ref[T]
pub fn use[T](r: Ref[T]) -> T
pub fn use[T, U](r: Ref[T], f: (T) -> U) -> U
pub fn update[T, R](r: Ref[T], f: (T) -> R) -> () | Errs[R]
pub fn swap[T](r: Ref[T], new: T) -> T
pub fn empty[T](r: Ref[Option[T]]) -> Option[T]
pub type Ext[T]
pub fn value[T](l: Lazy[T]) -> T
pub type Lazy[T]
pub fn use[T](r: Ext[T]) -> T
pub fn update[T, R](r: Ext[T], f: (T) -> R) -> () | Errs[R]
pub fn swap[T](r: Ext[T], new: T) -> T
pub distinct type Error
pub distinct type LifecycleHandler
pub distinct type Dispose[T](..LifecycleHandler) where HandlerForm[(T) -> ()]
pub distinct type Embed[T](..LifecycleHandler)
  where HandlerForm[((Bytes) -> T | EmbedError) | ((Str) -> T | EmbedError), is Pure]
pub type EmbedError(..Error, message: Str, line: Int = 0, column: Int = 0)
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
    unsafe {
        let words = list::passed(list::element(types(), list), w0, w1);
        list::push(heap_of(ctx), types(), list, &words)
    }
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
    unsafe {
        let value = list::passed(map::value_layout(types(), map), v0, v1);
        map::insert(heap_of(ctx), types(), map, &[k0, k1], &value)
    }
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

extern "C" fn rt_disposal(ctx: *mut u64) -> Disposal {
    // SAFETY: see above.
    unsafe { next_disposal(heap_of(ctx), types()) }
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
        Module::compiled(text, Tier::compiled())
    }

    /// A module whose `embed`s may name the resources.
    fn with_resources(text: &str, resources: &[(&str, &[u8])]) -> Module {
        Module::compiled_with(text, Tier::compiled(), resources)
    }

    fn metered(text: &str) -> Module {
        Module::compiled(text, Tier::Metered)
    }

    fn compiled(text: &str, tier: Tier) -> Module {
        Module::compiled_with(text, tier, &[])
    }

    /// A module, in the optimizing tier, that may import the module `lib`
    /// with the library's text.
    fn with_library(text: &str, library: &str) -> Module {
        Module::build(text, Tier::Optimizing, &[], Some(library))
    }

    fn compiled_with(text: &str, tier: Tier, resources: &[(&str, &[u8])]) -> Module {
        Module::build(text, tier, resources, None)
    }

    fn build(text: &str, tier: Tier, resources: &[(&str, &[u8])], library: Option<&str>) -> Module {
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
        let resources = resources
            .iter()
            .map(|(source, bytes)| {
                let content = Ok(std::sync::Arc::from(*bytes));
                (module, source.to_string(), Resource::new(&db, content))
            })
            .collect();
        let mut modules = vec![core, module];
        if let Some(library) = library {
            let file = SourceFile::new(&db, library.to_string());
            modules.push(ModuleId::new(&db, "lib".to_string(), file));
        }
        let program = Program::new(&db, modules, resources);
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
                // Without a scheduler a deferred release frees at once.
                RuntimeFn::Release | RuntimeFn::ReleaseDeferred => rt_release as *const () as usize,
                RuntimeFn::Trap => rt_trap as *const () as usize,
                RuntimeFn::ListPush => rt_list_push as *const () as usize,
                RuntimeFn::ListElem => rt_list_elem as *const () as usize,
                RuntimeFn::ListSlice => rt_list_slice as *const () as usize,
                RuntimeFn::MapInsert => rt_map_insert as *const () as usize,
                RuntimeFn::MapGet => rt_map_get as *const () as usize,
                RuntimeFn::TextConcat => rt_text_concat as *const () as usize,
                RuntimeFn::TextEquals => rt_text_equals as *const () as usize,
                RuntimeFn::TextShow => rt_text_show as *const () as usize,
                RuntimeFn::Disposal => rt_disposal as *const () as usize,
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

    /// The bytes of the result a function of the module gives by value.
    fn flat_result(&self, name: &str) -> Option<u32> {
        let (db, program) = (&self.db, self.program);
        let module = program.modules(db)[1];
        let owner = owners(db, module)
            .into_iter()
            .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == name))
            .unwrap();
        crag_backend::flat_result(db, program, InstanceKey::body(db, owner))
            .as_ref()
            .map(|(size, _)| *size)
    }

    /// Which parameters of a function of the module pass by value.
    fn flat(&self, name: &str) -> Vec<bool> {
        let (db, program) = (&self.db, self.program);
        let module = program.modules(db)[1];
        let owner = owners(db, module)
            .into_iter()
            .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == name))
            .unwrap();
        flat_params(db, program, InstanceKey::body(db, owner)).clone()
    }

    /// Which parameters of a function of the module are borrowed.
    /// The function a function of the module, or of its library, is
    /// loaded as.
    fn func(&self, name: &str) -> FuncId {
        let (db, program) = (&self.db, self.program);
        let owner = program.modules(db)[1..]
            .iter()
            .flat_map(|&module| owners(db, module))
            .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == name))
            .unwrap();
        func_id(InstanceKey::body(db, owner))
    }

    fn borrowed(&self, name: &str) -> Vec<bool> {
        let (db, program) = (&self.db, self.program);
        let module = program.modules(db)[1];
        let owner = owners(db, module)
            .into_iter()
            .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == name))
            .unwrap();
        crag_mir::borrows(db, program, InstanceKey::body(db, owner)).clone()
    }

    /// The named locals of a function of the module that scalar
    /// replacement keeps split.
    fn split(&self, name: &str) -> Vec<String> {
        let (db, program) = (&self.db, self.program);
        let module = program.modules(db)[1];
        let owner = owners(db, module)
            .into_iter()
            .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == name))
            .unwrap();
        let key = InstanceKey::body(db, owner);
        let mut body = crag_mir::mir(db, program, key, Tier::Baseline)
            .clone()
            .unwrap();
        scalar_replace(db, program, key, &mut body);
        body.locals
            .iter()
            .filter(|l| l.split)
            .filter_map(|l| Some(l.binding?.1.text(db).clone()))
            .collect()
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
fn flat_locals_stay_in_registers() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Line(from: Point, to: Point)
type Named(items: List[Int], at: Point)
type Node(value: Int, next: Node | Nil)
type Nil

fn lines(a: Int, b: Int) -> Int {
  let p = Point(x: a, y: b)
  let q = Point(x: b, y: a)
  let l = Line(from: p, to: q)
  let r = l.to
  l.from.x * 1000 + r.x * 100 + p.y * 10 + q.y
}

fn label() -> List[Int] {
  let n = Named(items: [1, 2], at: Point(x: 1, y: 2))
  let m = n
  m.items
}

fn node(a: Int) -> Int {
  let tail = Node(value: a, next: Nil)
  let head = Node(value: 1, next: tail)
  case head.next {
    Nil -> 0
    n: Node -> n.value + head.value
  }
}

fn escapes(a: Int) -> Point {
  let p = Point(x: a, y: a)
  let kept = Point(x: p.x, y: 1)
  kept
}
"#,
    );
    let split = |name| match flat_layouts() {
        true => m.split(name),
        false => Vec::new(),
    };
    let on = |names: &[&str]| match flat_layouts() {
        true => names.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
        false => Vec::new(),
    };
    assert_eq!(split("lines"), on(&["p", "q", "l", "r"]));
    assert_eq!(split("label"), on(&["n", "m"]));
    // `tail` is boxed where it goes into a field that holds a box, and
    // `n` loaded from it.
    assert_eq!(split("node"), on(&["tail", "head", "n"]));
    // A returned record is boxed where it is returned.
    assert_eq!(split("escapes"), on(&["p", "kept"]));
    RELEASED.set(0);
    assert_eq!(m.int("lines", &[3, 4]), 3443);
    assert_eq!(m.int("node", &[5]), 6);
    assert_eq!(m.shown("label"), "[1, 2]");
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn flat_locals_are_boxed_where_they_escape() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Line(from: Point, to: Point)
type Named(items: List[Int], at: Point)

fn line(a: Int) -> Line {
  let p = Point(x: a, y: 1)
  let l = Line(from: p, to: Point(x: 2, y: a))
  l
}

fn ends(a: Int) -> Int {
  let l = line(a)
  let from = l.from
  let to = l.to
  from.x * 100 + to.y * 10 + from.y
}

fn listed(a: Int) -> List[Point] {
  let p = Point(x: a, y: a)
  [p, p]
}

fn first(a: Int) -> Int {
  let ps = listed(a)
  let p = ps[0]
  p.x + p.y
}

fn passed(a: Int) -> Int {
  let l = line(a)
  let from = l.from
  ends(from.x)
}

fn named(a: Int) -> List[Int] {
  let n = Named(items: [a, a], at: Point(x: 1, y: 2))
  let m = Named(items: n.items, at: n.at)
  m.items
}

fn zeroLine() -> Line {
  line(0)
}

fn zeroNamed() -> List[Int] {
  named(0)
}
"#,
    );
    let split = |name| match flat_layouts() {
        true => m.split(name),
        false => Vec::new(),
    };
    let on = |names: &[&str]| match flat_layouts() {
        true => names.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
        false => Vec::new(),
    };
    // Boxed where it is returned, the points within it too.
    assert_eq!(split("line"), on(&["p", "l"]));
    // Given by value, through a buffer on the side stack.
    assert_eq!(split("ends"), on(&["l", "from", "to"]));
    assert_eq!(split("passed"), on(&["l", "from"]));
    // Used twice where it must be in a box: one box, shared.
    assert_eq!(split("listed"), on(&[]));
    // An element is loaded from its list.
    assert_eq!(split("first"), on(&["p"]));
    assert_eq!(split("named"), on(&["n", "m"]));
    assert_eq!(m.int("ends", &[7]), 7 * 100 + 7 * 10 + 1);
    assert_eq!(m.int("first", &[4]), 8);
    assert_eq!(m.int("passed", &[3]), 3 * 100 + 3 * 10 + 1);
    assert_eq!(
        m.shown("zeroLine"),
        "Line(from: Point(x: 0, y: 1), to: Point(x: 2, y: 0))"
    );
    assert_eq!(m.shown("zeroNamed"), "[0, 0]");
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn flat_records_pass_by_value() {
    let mut m = Module::new(
        r#"type Grass
type Rock
type Terrain = Grass | Rock
type Tile(kind: Terrain, cost: UInt8, seen: Bool)
type Point(x: Int, y: Int)
type Spot(at: Point | Empty[Point], n: Int)
type Wide(a: Int, b: Int, c: Int, d: Int, e: Int)

fn tile(t: Tile, n: Int) -> Int {
  let k = case t.kind {
    Grass -> 1
    Rock -> 2
  }
  if t.seen { k * 10 + n } else { k }
}

fn spot(s: Spot) -> Int { s.n }
fn wide(w: Wide) -> Int { w.e }

fn run(n: Int) -> Int {
  tile(Tile(kind: Rock, cost: 7, seen: True), n) * 100 + tile(Tile(kind: Grass, cost: 0, seen: False), n)
}
"#,
    );
    let on = |flags: &[bool]| match flat_layouts() {
        true => flags.to_vec(),
        false => Vec::new(),
    };
    assert_eq!(m.flat("tile"), on(&[true, false]));
    // A union field with a record member is stored in its place, but a
    // record too large to be flat keeps its box.
    assert_eq!(m.flat("spot"), on(&[true]));
    assert_eq!(m.flat("wide"), on(&[false]));
    assert_eq!(m.int("run", &[3]), 2301);
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn union_fields_split_with_their_records() {
    let mut m = Module::new(
        r#"type Named(name: Str | Empty[Str], n: Int)

fn label(s: Str | Empty[Str]) -> Int {
  case s {
    Empty[Str] -> 0
    t: Str -> if t == "hello" { 1 } else { 2 }
  }
}

fn named(r: Named) -> Int { label(r.name) * 10 + r.n }

fn run(n: Int) -> Int {
  let long = Named(name: "a name longer than fifteen bytes", n: n)
  named(Named(name: "hello", n: n)) * 10000 + named(long) * 100 + named(Named(name: Empty[Str], n: n))
}
"#,
    );
    let on = |flags: &[bool]| match flat_layouts() {
        true => flags.to_vec(),
        false => Vec::new(),
    };
    // The union is its member's type index and the string's two words,
    // with no member box.
    assert_eq!(m.flat("named"), on(&[true]));
    assert_eq!(m.int("run", &[3]), 130_000 + 2_300 + 3);
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn flat_fields_are_stored_in_their_box() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Line(from: Point, to: Point, dashed: Bool, label: Str)
type Glyph(code: CodePoint, size: Int, bold: Bool, italic: Bool, at: Point)
type Row(glyph: Glyph, next: Option[Point])

fn line(a: Int) -> Line {
  Line(from: Point(x: a, y: a + 1), to: Point(x: a * 10, y: 0 - a), dashed: True, label: "a label long enough for a buffer")
}
fn length(l: Line) -> Int { l.to.x - l.from.x + l.from.y }
fn row(a: Int) -> Row {
  let next: Option[Point] = if a == 1 { Empty } else { Point(x: a, y: a) }
  Row(glyph: Glyph(code: 'A', size: a, bold: True, italic: False, at: Point(x: 4, y: 20)), next: next)
}
fn size(r: Row) -> Int {
  let n = case r.next {
    Empty -> 0
    p: Point -> p.x
  }
  if r.glyph.bold and not r.glyph.italic { r.glyph.size + r.glyph.at.y + n } else { 0 }
}
fn ends(l: Line) -> List[Point] { [l.from, l.to] }
fn spread(a: Int) -> Int {
  let ps = ends(line(a))
  ps[0].x + ps[1].x
}
fn three() -> Line { line(3) }
fn two() -> Row { row(2) }

fn run(a: Int) -> Int { length(line(a)) * 1000 + size(row(a)) }
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("run", &[3]), 31 * 1000 + 26);
    assert_eq!(m.int("run", &[1]), 11 * 1000 + 21);
    assert_eq!(m.int("spread", &[4]), 44);
    assert_eq!(m.heap.live_blocks(), 0);
    // The points are in the line's box, which is all that is made: the
    // label is a literal, in static data.
    let words = m.call("three", &[]);
    let boxes = if flat_layouts() { 1 } else { 3 };
    assert_eq!(m.heap.live_blocks(), boxes);
    let (shapes, root) = m.result_shapes("three");
    // SAFETY: the words are the function's result, of the shape.
    unsafe { release_value(&mut m.heap, &m.types, &words, &shapes, root) };
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(
        m.shown("three"),
        "Line(from: Point(x: 3, y: 4), to: Point(x: 30, y: -3), dashed: True, \
         label: \"a label long enough for a buffer\")"
    );
    assert_eq!(
        m.shown("two"),
        "Row(glyph: Glyph(code: 'A', size: 2, bold: True, italic: False, at: Point(x: 4, \
         y: 20)), next: Point(x: 2, y: 2))"
    );
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn flat_elements_are_stored_in_their_collections() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Glyph(code: CodePoint, size: Int, bold: Bool, italic: Bool, at: Point)
  where 0 < size and size < 256
type Label(text: Str, at: Point)
type Stock(qty: Int, reserved: Int, onOrder: Bool)

fn glyph(n: Int) -> Glyph {
  Glyph(code: 'A', size: n, bold: 2 < n, italic: False, at: Point(x: n, y: 0))
}
fn glyphs(n: Int) -> List[Glyph] { [glyph(n), glyph(1), glyph(n + 1)] }
fn bold(n: Int) -> Int {
  let gs = glyphs(n)
  let g = gs[2]
  let k = case gs {
    [first, .., last] -> first.size * 100 + last.at.x
    _ -> 0
  }
  if g.bold { k + g.size * 10000 } else { k }
}

fn labels(n: Int) -> List[Label] {
  [Label(text: "{n} is a label long enough for a heap buffer", at: Point(x: n, y: n)), Label(text: "short", at: Point(x: 0, y: 7))]
}
fn labelled(n: Int) -> Int {
  let ls = labels(n)
  if ls[0].text == "{n} is a label long enough for a heap buffer" { ls[0].at.x + ls[1].at.y } else { -1 }
}

fn stock() -> Map[Int, Stock] {
  [1001: Stock(qty: 40, reserved: 5, onOrder: False), 1002: Stock(qty: 0, reserved: 0, onOrder: True)]
}
fn onHand(key: Int) -> Int {
  case stock()[key] {
    Empty -> -1
    s: Stock -> if s.onOrder { 1000 } else { s.qty - s.reserved }
  }
}

fn maybe(n: Int) -> List[Option[Point]] { [Point(x: n, y: 2), Empty] }
fn firstX(n: Int) -> Int {
  case maybe(n)[0] {
    Empty -> -1
    p: Point -> p.x
  }
}

fn points() -> List[Point] { [Point(x: 1, y: 2), Point(x: 3, y: 4), Point(x: 5, y: 6)] }
fn three() -> List[Glyph] { glyphs(3) }
fn named() -> List[Label] { labels(2) }
fn stocked() -> Map[Int, Stock] { stock() }
fn maybes() -> List[Option[Point]] { maybe(1) }
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("bold", &[5]), 60506);
    assert_eq!(m.int("labelled", &[3]), 10);
    assert_eq!(m.int("onHand", &[1001]), 35);
    assert_eq!(m.int("onHand", &[1002]), 1000);
    assert_eq!(m.int("onHand", &[7]), -1);
    assert_eq!(m.int("firstX", &[9]), 9);
    assert_eq!(m.heap.live_blocks(), 0);
    // The points take no box of their own: the list's box and its leaf.
    let words = m.call("points", &[]);
    let boxes = if flat_layouts() { 2 } else { 5 };
    assert_eq!(m.heap.live_blocks(), boxes);
    let (shapes, root) = m.result_shapes("points");
    // SAFETY: the words are the function's result, of the shape.
    unsafe { release_value(&mut m.heap, &m.types, &words, &shapes, root) };
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(
        m.shown("three"),
        "[Glyph(code: 'A', size: 3, bold: True, italic: False, at: Point(x: 3, y: 0)), \
         Glyph(code: 'A', size: 1, bold: False, italic: False, at: Point(x: 1, y: 0)), \
         Glyph(code: 'A', size: 4, bold: True, italic: False, at: Point(x: 4, y: 0))]"
    );
    assert_eq!(
        m.shown("stocked"),
        "[1001: Stock(qty: 40, reserved: 5, onOrder: False), 1002: Stock(qty: 0, reserved: 0, \
         onOrder: True)]"
    );
    assert_eq!(m.shown("maybes"), "[Point(x: 1, y: 2), Empty]");
    // The labels' strings are released with their list.
    assert_eq!(
        m.shown("named"),
        "[Label(text: \"2 is a label long enough for a heap buffer\", at: Point(x: 2, y: 2)), \
         Label(text: \"short\", at: Point(x: 0, y: 7))]"
    );
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn collections_pack_values_smaller_than_a_word() {
    // 300 tiles of two bytes: a leaf takes 256 of them, so the list is its
    // box, two leaves and the node above them. Boxed, a word each, a leaf
    // takes 64, and the two tiles are boxes of their own.
    let tiles = vec!["t"; 299].join(", ");
    let text = format!(
        r#"type Grass
type Rock
type Terrain = Grass | Rock
type Tile(kind: Terrain, cost: UInt8, seen: Bool)

fn tiles() -> List[Tile] {{
  let t = Tile(kind: Grass, cost: 1, seen: False)
  let r = Tile(kind: Rock, cost: 9, seen: True)
  [{tiles}, r]
}}
fn tileAt(i: Int) -> Int {{
  let x = tiles()[i]
  let k = case x.kind {{
    Grass -> 1
    Rock -> 2
  }}
  if x.seen {{ k * 10 }} else {{ k }}
}}
fn signs() -> List[Int8] {{ [-1, 5, -128] }}
fn sign(i: Int) -> Int8 {{ signs()[i] }}
fn flags() -> List[Bool] {{ [True, False, True] }}
fn small() -> Map[Int8, Bool] {{ [-1: True, 3: False] }}
fn smallAt(k: Int8) -> Int {{
  case small()[k] {{
    Empty -> 0
    True -> 1
    False -> 2
  }}
}}
"#
    );
    let mut m = Module::new(&text);
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.int("tileAt", &[0]), 1);
    assert_eq!(m.int("tileAt", &[299]), 20);
    assert_eq!(m.int("sign", &[0]), -1);
    assert_eq!(m.int("sign", &[2]), -128);
    assert_eq!(m.int("smallAt", &[-1]), 1);
    assert_eq!(m.int("smallAt", &[3]), 2);
    assert_eq!(m.int("smallAt", &[4]), 0);
    assert_eq!(m.heap.live_blocks(), 0);
    let words = m.call("tiles", &[]);
    let boxes = if flat_layouts() { 4 } else { 2 + 1 + 5 + 1 };
    assert_eq!(m.heap.live_blocks(), boxes);
    let (shapes, root) = m.result_shapes("tiles");
    // SAFETY: the words are the function's result, of the shape.
    unsafe { release_value(&mut m.heap, &m.types, &words, &shapes, root) };
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.shown("signs"), "[-1, 5, -128]");
    assert_eq!(m.shown("flags"), "[True, False, True]");
    assert_eq!(m.shown("small"), "[-1: True, 3: False]");
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn flat_records_are_returned_by_value() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Line(from: Point, to: Point)

fn point(a: Int) -> Point { Point(x: a, y: a + 1) }

fn line(a: Int) -> Line { Line(from: point(a), to: point(a * 10)) }

fn walk(l: Line, n: Int) -> Line {
  if n == 0 { l } else { walk(Line(from: l.to, to: l.from), n - 1) }
}

fn origin() -> Point { point(0) }

fn found(a: Int) -> Option[Point] { if a == 0 { Empty } else { point(a) } }

fn viaValue(a: Int) -> Point {
  let f: (Int) -> Point = { b -> Point(x: b, y: b) }
  f(a)
}

fn run(a: Int) -> Int {
  let p = point(a)
  let l = walk(line(a), 1001)
  let o = origin()
  let v = viaValue(a)
  let f = case found(a) {
    Empty -> 0
    q: Point -> q.x
  }
  p.y * 1000000 + l.from.x * 1000 + l.to.y * 10 + o.y + v.x + f
}

fn zeroLine() -> Line { walk(line(1), 2) }
"#,
    );
    let on = |r: Option<u32>| match flat_layouts() {
        true => r,
        false => None,
    };
    let size = |name: &str| m.flat_result(name);
    assert_eq!(size("point"), on(Some(16)));
    assert_eq!(size("line"), on(Some(32)));
    // A tag byte, then the point.
    assert_eq!(size("found"), on(Some(24)));
    // The host runs a function without parameters as a root.
    assert_eq!(size("origin"), None);
    assert_eq!(
        m.int("run", &[2]),
        3 * 1000000 + 20 * 1000 + 3 * 10 + 1 + 2 + 2
    );
    assert_eq!(
        m.shown("zeroLine"),
        "Line(from: Point(x: 1, y: 2), to: Point(x: 10, y: 11))"
    );
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn flat_unions_stay_in_registers() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)
type Spot(at: Option[Point], n: Int)
type Named(name: Str | Point, n: Int)
type End
type Node(value: Int, next: Node | End)

fn pick(a: Int) -> Int {
  let o: Option[Point] = if 0 < a { Point(x: a, y: 1) } else { Empty }
  case o {
    Empty -> -1
    p: Point -> p.x + p.y
  }
}

fn spot(a: Int) -> Int {
  let s = Spot(at: Point(x: a, y: 2), n: 5)
  let t = Spot(at: Empty, n: 6)
  let u = s
  case u.at {
    Empty -> t.n
    p: Point -> p.y * 10 + t.n
  }
}

fn named(a: Int) -> Int {
  let n = Named(name: "a string longer than the inline bytes", n: a)
  let m = Named(name: Point(x: a, y: a), n: 1)
  let k = case n.name {
    s: Str -> 100
    p: Point -> p.x
  }
  let j = case m.name {
    s: Str -> 100
    p: Point -> p.x
  }
  k + j + n.n
}

fn kept(a: Int) -> List[Option[Point]] {
  let o: Option[Point] = Point(x: a, y: a)
  [o, Empty]
}

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

fn listed() -> List[Option[Point]] { kept(3) }
"#,
    );
    let split = |name| match flat_layouts() {
        true => m.split(name),
        false => Vec::new(),
    };
    let on = |names: &[&str]| match flat_layouts() {
        true => names.iter().map(|n| n.to_string()).collect::<Vec<_>>(),
        false => Vec::new(),
    };
    assert_eq!(split("pick"), on(&["o", "p"]));
    assert_eq!(split("spot"), on(&["s", "t", "u", "p"]));
    assert_eq!(split("named"), on(&["n", "m", "p", "p"]));
    // Boxed where it goes into the list.
    assert_eq!(split("kept"), on(&["o"]));
    assert_eq!(m.int("pick", &[4]), 5);
    assert_eq!(m.int("pick", &[0]), -1);
    assert_eq!(m.int("spot", &[3]), 26);
    assert_eq!(m.int("named", &[7]), 100 + 7 + 7);
    assert_eq!(m.int("chain", &[1000]), 1000);
    assert_eq!(m.shown("listed"), "[Point(x: 3, y: 3), Empty]");
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
    // With flat layouts `build` returns the first cell by value, so it
    // has no box.
    let boxes = n as usize - usize::from(flat_layouts());
    assert_eq!(RELEASED.get(), boxes);
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
        r#"type Point(x: Int, y: Int, a: Int, b: Int, c: Int)

fn total(n: Int) -> Int {
  var sum = 0
  for i in 1..n {
    let p = Point(x: i, y: 1, a: 0, b: 0, c: 0)
    sum = sum + p.x + p.y
  }
  sum
}
"#,
    );
    SLOW_ALLOCS.set(0);
    RELEASED.set(0);
    assert_eq!(m.int("total", &[10_000]), 10_000 * 10_001 / 2 + 10_000);
    // Each point, too large to be flat, is freed before the next is made,
    // and the next takes its block from the free list inline. Only the
    // first point finds the heap's page for its class empty, and so does
    // the range when it is boxed, with flat layouts off.
    let range = usize::from(!flat_layouts());
    assert_eq!(
        (SLOW_ALLOCS.get(), RELEASED.get()),
        (1 + range, 10_000 + range)
    );
    assert_eq!(m.heap.pages_in_use(), 1 + range);
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn what_cannot_compile_is_listed() {
    let mut m = Module::new(
        r#"fn label(r: (n: Int, ..)) -> Int {
  r.n
}

fn plain(n: Int) -> Int {
  n * 2
}

"#,
    );
    assert_eq!(m.unsupported, ["label: types of parameters or results"]);
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
        ("names", r#"["b", "a", "a long name in a set of names"]"#),
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
    // literal's, or the literals of two functions. Inlined, `kind` shares
    // its literal's buffer with `kinds`.
    let compares = match Tier::compiled() {
        Tier::Optimizing => 2,
        _ => 3,
    };
    assert_eq!(TEXT_COMPARES.get(), compares);
    // Short strings are inline, long ones point at their buffer.
    let words = m.call("hello", &[]);
    assert_eq!(words, inline_text(b"Hello, Ada!"));
}

#[test]
fn unions_hold_members_of_two_words_in_boxes() {
    let mut m = Module::new(
        r#"type Named(name: Option[Str], age: Int)
type Cell(n: Int)

fn maybe(n: Int) -> Option[Str] {
  if n == 0 { Empty } else { "a long string, so in a buffer: {n}" }
}
fn short(n: Int) -> Option[Str] {
  if n == 0 { Empty } else { "hi" }
}
fn kind(o: Option[Str]) -> Int {
  case o {
    s: Str -> if s == "hi" { 1 } else { 2 }
    _ -> 0
  }
}
fn early(o: Option[Str]) -> Str {
  if o is Empty { return "none" }
  o
}
fn kinds() -> List[Int] {
  [kind(maybe(1)), kind(maybe(0)), kind(short(1)), kind(Empty), kind("hi")]
}
fn earlies() -> List[Str] { [early(maybe(2)), early(Empty), early(short(1))] }
fn options() -> List[Option[Str]] { [maybe(3), Empty, short(1)] }
fn mixed(n: Int) -> Str | Int | Bytes {
  case n {
    0 -> "a string long enough for a buffer"
    1 -> b"bytes long enough for a buffer too"
    _ -> n
  }
}
fn mixes() -> List[Str | Int | Bytes] { [mixed(0), mixed(1), mixed(2)] }
fn people() -> List[Named] {
  [Named(name: maybe(1), age: 3), Named(name: Empty, age: 4), Named(name: short(1), age: 5)]
}
fn names() -> Int {
  var out = 0
  for p in people() {
    out = out * 10 + kind(p.name)
  }
  out
}
fn table() -> Map[Int, Option[Str]] { [1: maybe(1), 2: Empty] }
fn words() -> Map[Str, Str] {
  ["a": "a value made at run time, {1} buffer", "b": "hi"]
}
fn found() -> List[Option[Str]] {
  let m = words()
  [m["a"], m["b"], m["c"]]
}
fn lookups() -> Int {
  let m = words()
  kind(m["a"]) * 100 + kind(m["b"]) * 10 + kind(m["c"]) + kind(m["a"]) * 1000
}
fn kept() -> (first: Option[Str], words: Map[Str, Str]) {
  let m = words()
  let first = m["a"]
  kind(m["a"])
  (first: first, words: m)
}
fn named(p: Named) -> Str {
  case p.name {
    s: Str -> s
    _ -> "none"
  }
}
fn nameds() -> List[Str] {
  [named(Named(name: maybe(4), age: 1)), named(Named(name: Empty, age: 2))]
}
fn adder(k: Int) -> Option[(Int) -> Int] {
  let c = Cell(n: k)
  if k == 0 { Empty } else { { n -> n + c.n } }
}
fn apply(f: Option[(Int) -> Int], x: Int) -> Int {
  if f is Empty { return x }
  f(x)
}
fn applied() -> List[Int] { [apply(adder(5), 1), apply(adder(0), 1)] }
fn functions() -> Map[Str, (Int) -> Int] {
  let c = Cell(n: 7)
  ["add": { n -> n + c.n }]
}
fn calls() -> Int {
  let fs = functions()
  apply(fs["add"], 1) * 10 + apply(fs["none"], 1)
}
"#,
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    let expected = [
        ("kinds", "[2, 0, 1, 0, 1]"),
        (
            "earlies",
            r#"["a long string, so in a buffer: 2", "none", "hi"]"#,
        ),
        (
            "options",
            r#"["a long string, so in a buffer: 3", Empty, "hi"]"#,
        ),
        (
            "mixes",
            r#"["a string long enough for a buffer", b"bytes long enough for a buffer too", 2]"#,
        ),
        (
            "people",
            r#"[Named(name: "a long string, so in a buffer: 1", age: 3), Named(name: Empty, age: 4), Named(name: "hi", age: 5)]"#,
        ),
        ("names", "201"),
        (
            "table",
            r#"[1: "a long string, so in a buffer: 1", 2: Empty]"#,
        ),
        (
            "found",
            r#"["a value made at run time, 1 buffer", "hi", Empty]"#,
        ),
        ("lookups", "2210"),
        (
            "kept",
            r#"(first: "a value made at run time, 1 buffer", words: ["a": "a value made at run time, 1 buffer", "b": "hi"])"#,
        ),
        ("nameds", r#"["a long string, so in a buffer: 4", "none"]"#),
        ("applied", "[6, 1]"),
        ("calls", "81"),
    ];
    for (name, shown) in expected {
        assert_eq!(m.shown(name), shown, "{name}");
        assert_eq!(m.heap.live_blocks(), 0, "{name}");
    }
}

#[test]
fn fields_left_out_take_their_defaults() {
    let mut m = Module::new(
        r#"type Options(size: Int, scale: Float = 1.5, label: Str = "a default long enough for a buffer")
type Wide(..Options, width: Int = 80)
type Computed(n: Int = add(1, 2), label: Str = name())
type Op(f: (Int) -> Int = { x -> add(x, 1) })
type Bag[T](items: List[T] = [])
type Wrapped(..Computed, m: Int = multiply(2, 3))
type Maybe(v: Option[Int] = multiply(2, 2))

fn name() -> Str { "made by a function, long enough for a buffer" }
fn plain() -> Options { Options(size: 1) }
fn given() -> Options { Options(size: 2, label: "x") }
fn wide() -> Wide { Wide(size: 3) }
fn computed() -> Computed { Computed() }
fn named() -> Computed { Computed(n: 4) }
fn wrapped() -> Wrapped { Wrapped(n: 5) }
fn applied() -> Int {
  let op = Op()
  let f = op.f
  f(2)
}
fn bag() -> Bag[Int] { Bag() }
fn maybe() -> Maybe { Maybe() }
"#,
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    let expected = [
        (
            "plain",
            r#"Options(size: 1, scale: 1.5, label: "a default long enough for a buffer")"#,
        ),
        ("given", r#"Options(size: 2, scale: 1.5, label: "x")"#),
        (
            "wide",
            r#"Wide(size: 3, scale: 1.5, label: "a default long enough for a buffer", width: 80)"#,
        ),
        (
            "computed",
            r#"Computed(n: 3, label: "made by a function, long enough for a buffer")"#,
        ),
        (
            "named",
            r#"Computed(n: 4, label: "made by a function, long enough for a buffer")"#,
        ),
        (
            "wrapped",
            r#"Wrapped(n: 5, label: "made by a function, long enough for a buffer", m: 6)"#,
        ),
        ("bag", "Bag(items: [])"),
        ("maybe", "Maybe(v: 4)"),
    ];
    for (name, shown) in expected {
        assert_eq!(m.shown(name), shown, "{name}");
        assert_eq!(m.heap.live_blocks(), 0, "{name}");
    }
    assert_eq!(m.int("applied", &[]), 3);
    assert_eq!(m.heap.live_blocks(), 0);
}

#[test]
fn parameters_left_out_take_their_defaults() {
    let mut m = Module::new(
        r#"fn scaled(x: Int, by: Int = add(x, 1)) -> Int { multiply(x, by) }
fn both(a: Int = 2, b: Int = multiply(a, 10)) -> Int { add(a, b) }
fn wrap[T](x: T, xs: List[T] = [x, x]) -> List[T] { xs }
fn label(s: Str, t: Str = s) -> Str { t }
fn adder(x: Int, f: (Int) -> Int = { y -> add(x, y) }) -> Int { f(10) }
fn sum(a: Int, b: Int, c: Int = add(a, b)) -> Int { multiply(c, 2) }

fn defaulted(x: Int) -> Int { scaled(x) }
fn given(x: Int) -> Int { scaled(x, by: 2) }
fn neither() -> Int { both() }
fn first() -> Int { both(a: 3) }
fn second() -> Int { both(b: 1) }
fn wrapped() -> List[Int] { wrap(5) }
fn texts() -> List[Str] { wrap("a string long enough for a buffer") }
fn same() -> Str { label("passed on to the default, long enough") }
fn adding(x: Int) -> Int { adder(x) }
fn summed() -> Int { sum(3, 4) }
"#,
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    assert_eq!(m.int("defaulted", &[3]), 12);
    assert_eq!(m.int("given", &[3]), 6);
    assert_eq!(m.int("neither", &[]), 22);
    assert_eq!(m.int("first", &[]), 33);
    assert_eq!(m.int("second", &[]), 3);
    assert_eq!(m.int("adding", &[5]), 15);
    assert_eq!(m.int("summed", &[]), 14);
    assert_eq!(m.heap.live_blocks(), 0);
    let expected = [
        ("wrapped", "[5, 5]"),
        (
            "texts",
            r#"["a string long enough for a buffer", "a string long enough for a buffer"]"#,
        ),
        ("same", r#""passed on to the default, long enough""#),
    ];
    for (name, shown) in expected {
        assert_eq!(m.shown(name), shown, "{name}");
        assert_eq!(m.heap.live_blocks(), 0, "{name}");
    }
}

#[test]
fn embeds_run_their_handlers_when_read() {
    // Here nothing computes the values at compile time, so their code runs
    // the handlers when they are first read.
    let mut m = Module::with_resources(
        r#"distinct type Level(n: Int)
  on Embed parse
distinct type Size(n: Int)
  on Embed measure

fn parse(text: Str) -> Level | EmbedError {
  case text {
    "high" -> Level(n: 3)
    _ -> EmbedError(message: "neither")
  }
}
fn measure(data: Bytes) -> Size { Size(n: 2) }

// The handler of a generic type is instantiated for each of its instances.
distinct type Pile[T](items: List[T], size: Int)
  on Embed pile
fn pile[T](data: Bytes) -> Pile[T] { Pile(items: [], size: 4) }

// Closures as handlers, code of the declaring type.
distinct type Word(text: Str)
  on Embed { text: Str -> Word(text: "{text}, from a closure long enough") }
distinct type Heap[T](items: List[T], n: Int)
  on Embed { data: Bytes -> Heap(items: [], n: 7) }

embed word: Word from "high.txt"
embed heap: Heap[Str] from "size.bin"
embed ints: Pile[Int] from "size.bin"
embed texts: Pile[Str] from "size.bin"
embed high: Level from "high.txt"
embed bad: Level from "bad.txt"
embed size: Size from "size.bin"
embed raw from "size.bin"

fn levels() -> Int { high.n * 10 + size.n }
fn piles() -> Int { ints.size + texts.size }
fn wordText() -> Str { word.text }
fn heapSize() -> Int { heap.n }
fn broken() -> Int { bad.n }
fn bytes() -> Bytes { raw }
"#,
        &[
            ("high.txt", b"high"),
            ("bad.txt", b"low"),
            ("size.bin", b"\x00\x01"),
        ],
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    assert_eq!(m.shown("levels"), "32");
    assert_eq!(m.shown("piles"), "8");
    assert_eq!(m.shown("wordText"), r#""high, from a closure long enough""#);
    assert_eq!(m.shown("heapSize"), "7");
    assert_eq!(m.shown("bytes"), r#"b"\x00\x01""#);
    // A handler's error is a compile error; code that gets one traps.
    let trap = m.run("broken", &[]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Error);
}

// A function borrows what it only reads (Plan §11.10.1): its caller
// keeps the value across the call and releases it once, also when a call
// both gives the value away and lends it, or the callee traps.
#[test]
fn borrowed_parameters_are_released_by_their_callers() {
    let mut m = Module::new(
        r#"fn total(xs: List[Int]) -> Int {
  var sum = 0
  for x in xs {
    sum = sum + x
  }
  sum
}

fn twice(n: Int) -> Int {
  let xs = [n, n + 1]
  total(xs) + total(xs)
}

fn keep(xs: List[Int], ys: List[Int]) -> List[Int] {
  if 0 < total(ys) { xs } else { [] }
}

fn same(n: Int) -> Int {
  let xs = [n, 2]
  total(keep(xs, xs))
}

fn walk(xs: List[Int], acc: Int) -> Int {
  case xs {
    [] -> acc
    [x, ..rest] -> walk(rest, acc + x)
  }
}

fn last(xs: List[Int], acc: Int) -> Int {
  total(xs) + acc
}

fn lend(n: Int) -> Int {
  let xs = [n, n, n]
  case xs {
    [_, ..rest] -> last(rest, 0)
    [] -> 0
  }
}

fn share(n: Int) -> Int {
  let xs = [n, 4]
  last(xs, 1)
}

fn divide(xs: List[Int], d: Int) -> Int {
  total(xs) / d
}

fn trapped(d: Int) -> Int {
  let xs = [10, 20]
  divide(xs, d) + total(xs)
}

fn greet(name: Str) -> Str { "Hello, {name}, from a string long enough" }

fn size(s: Str) -> Int {
  case s {
    "" -> 0
    _ -> 1
  }
}

fn greeted(n: Int) -> Int {
  let s = greet("someone with a long name {n}")
  size(s) + size(s)
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    assert_eq!(m.borrowed("total"), vec![true]);
    assert_eq!(m.borrowed("keep"), vec![false, true]);
    // A tail-recursive loop takes what it passes itself.
    assert_eq!(m.borrowed("walk"), Vec::<bool>::new());
    assert_eq!(m.borrowed("last"), vec![true, false]);
    assert_eq!(m.borrowed("size"), vec![true]);
    RELEASED.set(0);
    assert_eq!(m.int("twice", &[5]), 22);
    assert_eq!(RELEASED.get(), 1);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("same", &[5]), 7);
    assert_eq!(m.heap.live_blocks(), 0);
    // The tail call of `last` lends a slice it owns, so it is a call.
    assert_eq!(m.int("lend", &[3]), 6);
    assert_eq!(m.int("share", &[3]), 8);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("greeted", &[7]), 2);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.run("trapped", &[2]), Ok(vec![45]));
    assert_eq!(m.worker.heap().live_blocks(), 0);
    let trap = m.run("trapped", &[0]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::DivideByZero);
    assert_eq!(m.worker.heap().live_blocks(), 0);
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

    // A chain holds its nodes, made in a loop, so only the heap grows.
    // With flat layouts off a node takes 40 bytes; a refill of nodes
    // carves 102 of them, 4080 bytes, and seven fit 32 KiB beside the
    // loop's range, a box of 32 bytes whose refill carves 4 KiB. The node
    // after them goes beyond it; the trap comes at the next step, the
    // loop's back-edge, which a chain one longer never reaches. With flat
    // layouts a node takes 32 bytes, its `next` a pointer with null for
    // `End`, so a refill carves 128 and eight fit, and the chain's head is
    // in registers, boxed when the next node takes it: one more.
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
    let fit = if flat_layouts() { 8 * 128 + 1 } else { 7 * 102 };
    assert_eq!(fresh(fit), Ok(vec![fit as u64]));
    assert_eq!(fresh(fit + 1), Ok(vec![fit as u64 + 1]));
    let trap = fresh(fit + 2).unwrap_err();
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
type Pair3(..Pair, w: Int)
fn both() -> (p: Point, w: Pair) { (p: Point(x: 1, y: 2), w: Pair(u: 1, v: 2)) }
fn words() -> Map[Str, List[Str]] {
  ["k": ["a", "a string long enough for a buffer"], "a key long enough for a buffer": []]
}
fn texts() -> (name: Str, data: Bytes, none: Str) {
  (name: "Grüße aus Crag, lang genug", data: b"\x00\xff", none: "")
}
fn alone() -> Option[Str] { "a string made at run time: {2}" }
fn boxed() -> List[Option[Str] | Bytes] {
  ["a string long enough for a buffer", Empty, "short", b"\x01 bytes long enough for a buffer"]
}
// Stored flat in their collections.
type Flat(a: Int, b: Bool, c: Int)
fn flats() -> List[Flat] { [Flat(a: 1, b: True, c: 2), Flat(a: -3, b: False, c: 4)] }
fn spots() -> Map[Int, Option[Flat]] { [1: Flat(a: 5, b: True, c: 6), 2: Empty] }
fn labels() -> List[(text: Str, n: Int)] {
  [(text: "a string made at run time: {2}", n: 1), (text: "short", n: 2)]
}
fn narrow() -> List[Int8] { [-1, 7] }
fn keyed() -> Map[Int8, Flat] { [-3: Flat(a: 1, b: False, c: 2), 4: Flat(a: 3, b: True, c: 4)] }
// Plain types, written in their storage form.
type Tile(x: UInt8, y: Int8, lit: Bool)
fn flat() -> Flat { Flat(a: 1, b: True, c: -2) }
fn tile() -> Option[Tile] { Tile(x: 200, y: -3, lit: True) }
fn noTile() -> Option[Tile] { Empty }
fn placed() -> (name: Str, at: Tile, tiles: List[Tile]) {
  (name: "a", at: Tile(x: 1, y: 2, lit: False), tiles: [Tile(x: 3, y: 4, lit: True)])
}
"#,
    );
    let names = [
        "deep", "chain", "points", "ages", "set", "maybe", "none", "tags", "mixed", "empty",
        "nothing", "both", "words", "texts", "boxed", "alone", "flats", "spots", "labels",
        "narrow", "keyed", "flat", "tile", "noTile", "placed",
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

    // A Plain value is its storage form: `Flat` as `a`, `c` and a flag
    // byte, padded to 24 bytes, and `Option[Tile]` in the three bytes of a
    // `Tile`, `Empty` in the niche of `lit`'s flag byte. Bytes the value
    // they read does not give back are refused: a bit no field holds,
    // padding, or a payload beside the niche.
    let plain = |m: &mut Module, name: &str| {
        let words = m.call(name, &[]);
        let (shapes, root) = m.result_shapes(name);
        // SAFETY: as above.
        unsafe {
            let bytes = encode_value(&words, &shapes, root, &m.types).unwrap();
            release_value(&mut m.heap, &m.types, &words, &shapes, root);
            (bytes, shapes, root)
        }
    };
    let (flat, flat_shapes, flat_root) = plain(&mut m, "flat");
    let mut expected = [0u8; 24];
    expected[..8].copy_from_slice(&1i64.to_le_bytes());
    expected[8..16].copy_from_slice(&(-2i64).to_le_bytes());
    expected[16] = 1;
    assert_eq!(flat, expected);
    let (tile, tile_shapes, tile_root) = plain(&mut m, "tile");
    assert_eq!(tile, [200, 253, 1]);
    assert_eq!(plain(&mut m, "noTile").0, [0, 0, 2]);
    let broken = [
        (
            &flat_shapes,
            flat_root,
            [&flat[..16], &[3], &flat[17..]].concat(),
        ),
        (&flat_shapes, flat_root, [&flat[..23], &[1]].concat()),
        (&tile_shapes, tile_root, vec![200, 253, 5]),
        (&tile_shapes, tile_root, vec![1, 0, 2]),
        (&tile_shapes, tile_root, vec![200, 253]),
    ];
    for (i, (shapes, root, b)) in broken.iter().enumerate() {
        // SAFETY: as above.
        let result = unsafe { decode_value(b, shapes, *root, &mut m.heap, &m.types) };
        assert!(result.is_err(), "plain {i}");
    }
    assert_eq!(m.heap.live_blocks(), 0);

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
    // out alike: `Pair` for the `Point` of `both`, and the other way. Both
    // have subtypes, so neither is stored inline.
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
        "[2: Point(x: 20, y: 0), 1: Point(x: 10, y: 0)]"
    );
    assert_eq!(shown(&mut m, "none"), "[:]");
    assert_eq!(shown(&mut m, "set"), "[3, 1, 2]");
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

#[test]
fn dispose_handlers_run_when_values_are_dropped() {
    // A handler traps for a value whose `n` is zero, which shows that it
    // ran, with the value, where the value was dropped.
    let mut m = Module::new(
        r#"distinct type Guard(n: Int)
  on Dispose check
fn check(g: Guard) -> () {
  if g.n == 0 {
    ???
  }
}

// What holds a value with a handler disposes of it when it is freed.
type Holder(g: Guard, k: Int)
distinct type Sub(..Guard, m: Int)
distinct type Lid(n: Int)
  on Dispose { l: Lid -> if l.n == 0 { ??? } }
distinct type Cell[T](v: T, n: Int)
  on Dispose closeCell
fn closeCell[T](c: Cell[T]) -> () {
  if c.n == 0 {
    ???
  }
}

fn plain(n: Int) -> Int {
  let g = Guard(n: n)
  g.n + 1
}
fn held(n: Int) -> Int {
  let h = Holder(g: Guard(n: n), k: 3)
  h.k
}
fn listed(n: Int) -> Int {
  let gs = [Guard(n: 1), Guard(n: n)]
  5
}
fn optional(n: Int) -> Int {
  let o: Option[Guard] = Guard(n: n)
  6
}
fn sub(n: Int) -> Int {
  let s = Sub(n: n, m: 7)
  s.m
}
fn lid(n: Int) -> Int {
  let l = Lid(n: n)
  8
}
fn cell(n: Int) -> Int {
  let c: Cell[Str] = Cell(v: "a string long enough for a buffer", n: n)
  9
}
fn kept(n: Int) -> Guard { Guard(n: n) }
fn shownSub() -> Sub { Sub(n: 4, m: 5) }
// The value a key written twice had is dropped in the runtime.
fn mapped(n: Int) -> Map[Int, Guard] { [1: Guard(n: n), 1: Guard(n: 1)] }
"#,
    );
    assert!(m.unsupported.is_empty(), "{:?}", m.unsupported);
    let cases = [
        ("plain", 2),
        ("held", 3),
        ("listed", 5),
        ("optional", 6),
        ("sub", 7),
        ("lid", 8),
        ("cell", 9),
    ];
    for (name, result) in cases {
        assert_eq!(m.int(name, &[1]), result, "{name}");
        assert_eq!(m.heap.live_blocks(), 0, "{name}");
        assert_eq!(m.heap.disposals(), 0, "{name}");
        let trap = m.run(name, &[0]).unwrap_err();
        assert_eq!(trap.kind, TrapKind::Hole, "{name}");
    }
    // A value given away is not dropped.
    assert_eq!(m.run("kept", &[0]).map(|w| w.len()), Ok(1));
    assert_eq!(m.run("mapped", &[1]).map(|w| w.len()), Ok(1));
    // Printing skips the word of the dispose code. A value the runtime
    // releases outside generated code waits for the next code that drains
    // the queue.
    assert_eq!(m.shown("shownSub"), "Sub(n: 4, m: 5)");
    assert_eq!(m.heap.disposals(), 1);
    assert_eq!(m.int("plain", &[1]), 2);
    assert_eq!(m.heap.disposals(), 0);
    assert_eq!(m.heap.live_blocks(), 0);
    let trap = m.run("mapped", &[0]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Hole);
}

const REFS: &str = r#"type Point(x: Int, y: Int)

fn moved(n: Int) -> Int {
  ref p = Point(x: 1, y: 2)
  for k in 1..n {
    p.update { q -> Point(x: q.x + k, y: q.y) }
  }
  p.update { q -> q }
  let old = p.swap(Point(x: 0, y: 0))
  let q = p.use()
  old.x + q.y
}

fn kept(n: Int) -> Int {
  ref p: Option[Point] = Point(x: n, y: 0)
  case p.empty() {
    q: Point -> q.x
    _ -> 0
  }
}
"#;

#[test]
fn refs_count_what_they_update() {
    let mut m = Module::new(REFS);
    assert_eq!(m.unsupported, Vec::<String>::new());
    // The runtime's ref functions need a fiber's task context.
    assert_eq!(m.run("moved", &[10]).unwrap(), [1 + 55]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn refs_count_what_they_empty() {
    let mut m = Module::new(REFS);
    assert_eq!(m.run("kept", &[9]).unwrap(), [9]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn refs_hold_flat_values_in_their_cells() {
    let mut m = Module::new(
        r#"type Small(a: Int, lit: Bool)
type Named(text: Str)

fn smalls(n: Int) -> Int {
  ref s = Small(a: 1, lit: False)
  for k in 1..n {
    s.update { v -> Small(a: v.a + k, lit: if v.lit { False } else { True }) }
  }
  let v = s.use()
  if v.lit { v.a * 10 + 1 } else { v.a * 10 }
}

fn names(n: Int) -> Int {
  ref name = Named(text: "a name long enough for a heap buffer")
  name.update { v -> Named(text: "{v.text} and {n}") }
  let old = name.swap(Named(text: "short"))
  let now = name.use()
  if old.text == "a name long enough for a heap buffer and {n}" and now.text == "short" { n } else { -1 }
}

fn maybe(n: Int) -> Int {
  ref m: Option[Small] = Small(a: n, lit: True)
  let before = case m.use() {
    s: Small -> s.a
    _ -> 0
  }
  let old = m.swap(Empty)
  let after = case m.use() {
    s: Small -> s.a
    _ -> -1
  }
  let was = case old {
    s: Small -> s.a
    _ -> 0
  }
  before * 100 + was * 10 + after
}

fn maybeNamed(n: Int) -> Int {
  ref m: Option[Named] = Named(text: "another name long enough for the heap")
  let first = m.swap(Named(text: "another name long enough for the heap, {n}"))
  let old = m.swap(Empty)
  case old {
    s: Named -> if s.text == "another name long enough for the heap, {n}" { n } else { -1 }
    _ -> 0
  }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    // The runtime's ref functions need a fiber's task context.
    assert_eq!(m.run("smalls", &[5]).unwrap(), [161]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    assert_eq!(m.run("names", &[7]).unwrap(), [7]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    assert_eq!(m.run("maybe", &[4]).unwrap(), [4 * 100 + 4 * 10 - 1]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
    assert_eq!(m.run("maybeNamed", &[3]).unwrap(), [3]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn exts_count_what_they_hold() {
    let mut m = Module::new(
        r#"type Point(x: Int, y: Int)

fn held(n: Int) -> Int {
  ext p = Point(x: 1, y: 2)
  for k in 1..n {
    p.update { q -> Point(x: q.x + k, y: q.y) }
  }
  let old = p.swap(Point(x: 0, y: 0))
  old.x + p.use().y
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    // The ext's lock needs a fiber's task context.
    assert_eq!(m.run("held", &[10]).unwrap(), [1 + 55]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

#[test]
fn lazy_values_count_what_they_hold() {
    let mut m = Module::new(
        r#"fn twice(n: Int) -> Int {
  let s = "a string too long to be inline"
  let l = lazy "{s} {s}"
  let a = l.value
  let b = l.value
  if a == b { n } else { 0 }
}
"#,
    );
    assert_eq!(m.unsupported, Vec::<String>::new());
    // Lazy cells need a fiber's task context.
    assert_eq!(m.run("twice", &[5]).unwrap(), [5]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

/// In the optimizing tier, a small callee's code is copied in place of its
/// call, from its own module too. A trap in the copy is reported where the
/// callee's code is, with the callee as a frame of its own, marked as
/// inlined (Plan §11.10.1).
#[test]
fn traps_in_inlined_code_tell_their_callee() {
    let library = "pub fn inc(n: Int) -> Int {\n  n + 2\n}\n";
    let text = r#"import lib

fn double(n: Int) -> Int {
  n * 2
}

fn twice(n: Int) -> Int {
  inc(double(n)) + 2
}
"#;
    let mut m = Module::with_library(text, library);
    assert_eq!(m.unsupported, Vec::<String>::new());
    let (db, program) = (&m.db, m.program);
    let twice = owners(db, program.modules(db)[1])
        .into_iter()
        .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == "twice"))
        .unwrap();
    let body = crag_mir::mir(db, program, InstanceKey::body(db, twice), Tier::Optimizing);
    assert_eq!(body.as_ref().unwrap().inlined.len(), 2);
    assert_eq!(m.run("twice", &[20]), Ok(vec![44]));
    let (twice, double, inc) = (m.func("twice"), m.func("double"), m.func("inc"));
    let inlined = |func| Frame {
        func,
        inlined: true,
    };
    // In the function's own module.
    let trap = m.run("twice", &[i64::MAX]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(trap.position, Some(text.find("n * 2").unwrap() as u32));
    assert_eq!(trap.stack, vec![inlined(double), Frame::of(twice)]);
    // In the library's.
    let trap = m.run("twice", &[(i64::MAX - 1) / 2]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(trap.position, Some(library.find("n + 2").unwrap() as u32));
    assert_eq!(trap.stack, vec![inlined(inc), Frame::of(twice)]);
    // In the function's own code after them.
    let trap = m.run("twice", &[(i64::MAX - 3) / 2]).unwrap_err();
    assert_eq!(
        trap.position,
        Some(text.find("inc(double(n)) + 2").unwrap() as u32)
    );
    assert_eq!(trap.stack, vec![Frame::of(twice)]);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

/// In the optimizing tier, a record that dies gives its box to the record
/// built from it, when no one else holds it (Plan §11.10.1): no box is
/// freed and none allocated. A shared record stays as it was, and a trap
/// between the two frees the box kept.
#[test]
fn dying_records_give_their_boxes_to_new_ones() {
    let text = r#"type Nil
type Cons(head: Int, label: Str, tail: Cons | Nil)
type Leaf
type Node(left: Leaf | Node, label: Str, right: Leaf | Node)

fn build(n: Int, acc: Cons | Nil) -> Cons | Nil {
  if n == 0 { return acc }
  build(n - 1, Cons(head: n, label: "item {n}, with a label long enough for a buffer", tail: acc))
}

fn inc(xs: Cons | Nil) -> Cons | Nil {
  case xs {
    Nil -> Nil
    c: Cons -> Cons(head: c.head + 1, label: c.label, tail: inc(c.tail))
  }
}

fn sum(xs: Cons | Nil, acc: Int) -> Int {
  case xs {
    Nil -> acc
    c: Cons -> sum(c.tail, acc + c.head)
  }
}

fn bumped(n: Int) -> Int {
  sum(inc(build(n, Nil)), 0)
}

fn shared(n: Int) -> Int {
  let xs = build(n, Nil)
  let ys = inc(xs)
  sum(xs, 0) * 1000 + sum(ys, 0)
}

fn edge(n: Int) -> Int {
  sum(inc(Cons(head: 1, label: "a", tail: Cons(head: n, label: "b", tail: Nil))), 0)
}

fn tree(n: Int) -> Leaf | Node {
  if n == 0 { return Leaf }
  Node(left: tree(n - 1), label: "node {n}, with a label long enough for a buffer", right: Leaf)
}

fn rename(t: Leaf | Node) -> Leaf | Node {
  case t {
    Leaf -> Leaf
    n: Node -> Node(left: rename(n.left), label: "renamed", right: n.right)
  }
}

fn renamed(t: Leaf | Node) -> Int {
  case t {
    Leaf -> 0
    n: Node -> {
      let here = if n.label == "renamed" { 1 } else { 100 }
      here + renamed(n.left)
    }
  }
}

fn trees(n: Int) -> Int {
  renamed(rename(tree(n)))
}
"#;
    let mut base = Module::compiled(text, Tier::Baseline);
    let mut m = Module::compiled(text, Tier::Optimizing);
    assert_eq!(m.unsupported, Vec::<String>::new());
    RELEASED.set(0);
    assert_eq!(base.int("bumped", &[100]), 5150);
    let freed = RELEASED.get();
    RELEASED.set(0);
    assert_eq!(m.int("bumped", &[100]), 5150);
    // Each old node of the list became a new one.
    assert!(
        RELEASED.get() + 100 <= freed,
        "{} of {freed}",
        RELEASED.get()
    );
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("shared", &[10]), 55_065);
    assert_eq!(m.heap.live_blocks(), 0);
    assert_eq!(m.int("trees", &[20]), 20);
    assert_eq!(m.heap.live_blocks(), 0);
    // The overflow traps after the node is taken apart for the new one.
    assert_eq!(m.run("edge", &[5]), Ok(vec![8]));
    let trap = m.run("edge", &[i64::MAX]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}

/// In the optimizing tier, a call of a function value that is known to be
/// a small closure runs a copy of the closure's code, which reads what the
/// closure captured: the closure need not be made (Plan §11.10.1).
#[test]
fn known_closures_are_called_as_copies() {
    let text = r#"fn scaled(n: Int, k: Int) -> Int {
  let f = { x: Int -> x * k }
  f(n) + f(1)
}

fn apply(f: (Int) -> Int, n: Int) -> Int {
  f(n)
}

fn outer(n: Int, k: Int) -> Int {
  apply({ x: Int -> x + k }, n)
}

fn sum(n: Int) -> Int {
  fn go(i: Int, acc: Int) -> Int {
    if i == 0 { acc } else { go(i - 1, acc + i) }
  }
  go(n, 0)
}

fn total(xs: List[Int]) -> Int {
  var sum = 0
  for x in xs {
    sum = sum + x
  }
  sum
}

fn lists(n: Int) -> Int {
  let xs = [n, n, n]
  let f = { k: Int -> total(xs) + k }
  f(1) + f(2)
}

fn later(n: Int) -> Int {
  var c = n
  let f = { k: Int -> c + k }
  c = c + 1
  f(0)
}
"#;
    let mut m = Module::compiled(text, Tier::Optimizing);
    assert_eq!(m.unsupported, Vec::<String>::new());
    let (db, program) = (&m.db, m.program);
    let scaled = owners(db, program.modules(db)[1])
        .into_iter()
        .find(|o| matches!(o, Owner::Item(i) if i.name(db).text(db) == "scaled"))
        .unwrap();
    let body = crag_mir::mir(db, program, InstanceKey::body(db, scaled), Tier::Optimizing);
    let body = body.as_ref().unwrap();
    assert_eq!(body.inlined.len(), 2);
    // Only the guards' fallbacks make the closure.
    let made = body
        .blocks
        .iter()
        .filter(|b| b.inlined.is_none())
        .flat_map(|b| &b.statements)
        .filter(|s| {
            matches!(
                s,
                crag_mir::Statement::Assign(_, crag_mir::Rvalue::Closure { .. })
            )
        })
        .count();
    assert_eq!(made, 2);
    assert_eq!(m.int("scaled", &[5, 3]), 18);
    assert_eq!(m.int("outer", &[5, 3]), 8);
    assert_eq!(m.int("sum", &[10]), 55);
    assert_eq!(m.int("lists", &[2]), 15);
    assert_eq!(m.heap.live_blocks(), 0);
    // Refs need a fiber's task context.
    assert_eq!(m.run("later", &[4]), Ok(vec![5]));
    let trap = m.run("scaled", &[i64::MAX, 2]).unwrap_err();
    assert_eq!(trap.kind, TrapKind::Overflow);
    assert_eq!(m.worker.heap().live_blocks(), 0);
}
