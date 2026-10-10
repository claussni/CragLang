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
}

impl Image {
    pub fn new(functions: &[LirFunction]) -> Image {
        let settings = CodegenSettings {
            target: target_for("x86_64-unknown-linux-gnu").unwrap(),
            opt: OptLevel::None,
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
        }
    }

    /// A fiber that will call function `func` with `args`, expecting one
    /// result.
    pub fn fiber(&mut self, func: usize, args: &[u64], config: FiberConfig) -> Box<Fiber> {
        let stub = compile_entry_stub(args.len() as u32, 1, &self.settings).unwrap();
        let stub = load(&mut self.arena, &self.symbols, &stub).unwrap();
        // SAFETY: the stub was compiled for this argument count and one
        // result, like every function in these tests, and the image outlives
        // the fiber in each test.
        unsafe { Fiber::new(stub.addr(), self.functions[func], args, config).unwrap() }
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
