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

//! Shared by the test files: builds LIR functions, compiles and loads them
//! and creates fibers that call them.
#![allow(dead_code)]

use std::sync::Arc;
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

use crag_abi::{CountedField, ElementLayout, FuncId, RuntimeFn, SlotKey, TypeDescriptor};
use crag_codegen::{
    Block, CodeObject, CodegenSettings, Inst, LirFunction, OptLevel, Term, VReg, compile,
    compile_entry_stub, target_for,
};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_runtime::{CodeMap, Fiber, FiberConfig, FiberState, Types, Worker};

/// The list type whose elements the values are laid out as: one word.
pub const INTS: u64 = 1;

/// A list type of boxes.
pub const BOXES: u64 = 2;

/// Loaded functions; `FuncId(i)` is the i-th.
pub struct Image {
    pub functions: Vec<usize>,
    /// The stack maps of the functions, for unwinding.
    pub code: CodeMap,
    arena: CodeArena,
    symbols: SymbolTable,
    pub settings: CodegenSettings,
    /// The entry stubs loaded so far, by the numbers of arguments and
    /// results.
    stubs: std::collections::HashMap<(usize, u32), usize>,
}

impl Image {
    pub fn new(functions: &[LirFunction]) -> Image {
        Image::compiled(functions, false)
    }

    /// The functions compiled in the metered tier.
    pub fn metered(functions: &[LirFunction]) -> Image {
        Image::compiled(functions, true)
    }

    fn compiled(functions: &[LirFunction], metered: bool) -> Image {
        let settings = CodegenSettings {
            target: target_for("x86_64-unknown-linux-gnu").unwrap(),
            opt: OptLevel::None,
            metered,
            profile: None,
        };
        let objects: Vec<CodeObject> = functions
            .iter()
            .map(|f| compile(f, &settings).unwrap())
            .collect();
        let mut arena = CodeArena::new(1 << 20).unwrap();
        let mut symbols = SymbolTable::new();
        for func in RuntimeFn::ALL {
            symbols.define_runtime(func, crag_runtime::runtime_fn_addr(func));
        }
        let group: Vec<_> = (0..)
            .map(|i| SlotKey {
                func: FuncId(i),
                signature: 0,
            })
            .zip(&objects)
            .collect();
        let entries = load_group(&mut arena, &mut symbols, &group).unwrap();
        let mut code = CodeMap::new();
        for ((func, object), entry) in group.iter().zip(&entries) {
            code.add(func.func, entry.addr(), object);
        }
        Image {
            code,
            functions: entries.iter().map(|e| e.addr()).collect(),
            arena,
            symbols,
            settings,
            stubs: std::collections::HashMap::new(),
        }
    }

    /// A fiber that will call function `func` with `args`, expecting one
    /// result.
    pub fn fiber(&mut self, func: usize, args: &[u64], config: FiberConfig) -> Box<Fiber> {
        self.fiber_returning(func, args, 1, config)
    }

    /// A fiber that will call function `func` with `args`, expecting
    /// `results` results.
    pub fn fiber_returning(
        &mut self,
        func: usize,
        args: &[u64],
        results: u32,
        config: FiberConfig,
    ) -> Box<Fiber> {
        let stub = self.stub(args.len(), results);
        // SAFETY: the stub was compiled for this argument count and number
        // of results, which the caller promises the function has, and the
        // image outlives the fiber in each test.
        unsafe { Fiber::new(stub, self.functions[func], args, config).unwrap() }
    }

    /// The loaded entry stub for `params` arguments and `results` results.
    fn stub(&mut self, params: usize, results: u32) -> usize {
        let key = (params, results);
        if let Some(&stub) = self.stubs.get(&key) {
            return stub;
        }
        let stub = compile_entry_stub(params as u32, results, &self.settings).unwrap();
        let stub = load(&mut self.arena, &self.symbols, &stub).unwrap().addr();
        self.stubs.insert(key, stub);
        stub
    }

    /// Gives the code map the entry stubs that tasks of scopes start in.
    pub fn with_task_entries(&mut self) {
        let stubs = [0, 1, 2].map(|results| self.stub(1, results));
        // SAFETY: the stubs stay loaded as long as the image.
        unsafe { self.code.set_task_entries(stubs) };
    }
}

pub fn r(i: u32) -> VReg {
    VReg(i)
}

pub fn konst(dst: VReg, value: i64) -> Inst {
    Inst::Const { dst, value }
}

pub fn runtime(func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) -> Inst {
    Inst::CallRuntime { func, args, dsts }
}

pub fn block(insts: Vec<Inst>, term: Term) -> Block {
    Block { insts, term }
}

pub fn lir(params: u32, returns: u32, vregs: u32, blocks: Vec<Block>) -> LirFunction {
    LirFunction {
        params,
        returns,
        vregs,
        tracked: vec![],
        blocks,
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// A function of `params` parameters that calls runtime function `func`
/// with them and returns its `results` results.
pub fn calling(func: RuntimeFn, params: u32, results: u32) -> LirFunction {
    let args = (0..params).map(r).collect();
    let dsts: Vec<_> = (params..params + results).map(r).collect();
    lir(
        params,
        results,
        params + results,
        vec![block(
            vec![runtime(func, args, dsts.clone())],
            Term::Return(dsts),
        )],
    )
}

/// The list types `INTS` and `BOXES`.
pub fn types() -> Arc<Types> {
    let list = |counted: Vec<CountedField>| TypeDescriptor::List {
        element: ElementLayout::of_words(1, counted.clone()),
        cell: ElementLayout::of_words(1, counted.clone()),
        ref_cell: ElementLayout::of_words(1, counted),
    };
    Arc::new(Types::new([
        (INTS as u32, list(vec![])),
        (BOXES as u32, list(vec![CountedField::Box(0)])),
    ]))
}

pub fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

/// `n` milliseconds in nanoseconds, as the runtime takes durations.
pub fn ms_nanos(n: u64) -> u64 {
    n * 1_000_000
}

/// Ends the test process if the test hangs, as a fiber that is never
/// woken would leave it; dropping it stands the watchdog down.
pub struct Watchdog(mpsc::Sender<()>);

/// Starts a watchdog that aborts the process, naming `what` hung, if it
/// is not dropped within 60 seconds.
pub fn watchdog(what: &str) -> Watchdog {
    let what = what.to_owned();
    let (done, waiting) = mpsc::channel::<()>();
    std::thread::spawn(move || {
        if waiting.recv_timeout(Duration::from_secs(60)) == Err(RecvTimeoutError::Timeout) {
            eprintln!("{what} hung for 60 seconds");
            std::process::abort();
        }
    });
    Watchdog(done)
}

/// Runs the fiber to completion on a fresh worker and returns its result.
pub fn finish(fiber: &mut Fiber) -> u64 {
    assert_eq!(Worker::new().resume(fiber), FiberState::Finished);
    fiber.results().unwrap()[0]
}
