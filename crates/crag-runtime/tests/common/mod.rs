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

//! Shared by the test files: compiles and loads LIR functions and creates
//! fibers that call them.
#![allow(dead_code)]

use crag_abi::{FuncId, RuntimeFn, SlotKey};
use crag_codegen::{
    CodeObject, CodegenSettings, LirFunction, OptLevel, VReg, compile, compile_entry_stub,
    target_for,
};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_runtime::{CodeMap, Fiber, FiberConfig, FiberState, Worker};

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

/// Runs the fiber to completion on a fresh worker and returns its result.
pub fn finish(fiber: &mut Fiber) -> u64 {
    assert_eq!(Worker::new().resume(fiber), FiberState::Finished);
    fiber.results().unwrap()[0]
}
