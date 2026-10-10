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

//! `rt_trap` called from generated code deep in a fiber's stack: the boxes
//! the frames below hold are released, and the fiber ends with the trap.

mod common;

use std::sync::Arc;

use crag_abi::{FuncId, RuntimeFn, TrapKind, TypeDescriptor};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::{FiberConfig, FiberState, Trap, Types, Worker};

use common::{Image, r};

const BOX: i64 = 4;

/// `f(n)`: allocates a box holding `n`, calls `f(n - 1)` and adds the box's
/// field to the result, so every frame holds its box across the call, until
/// `n` is zero, which traps.
fn deep_fn() -> LirFunction {
    let konst = |dst, value| Inst::Const { dst: r(dst), value };
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 9,
        tracked: vec![r(4)],
        blocks: vec![
            Block {
                insts: vec![
                    konst(1, 0),
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: r(2),
                        a: r(0),
                        b: r(1),
                    },
                ],
                term: Term::Branch {
                    cond: r(2),
                    then: BlockId(1),
                    otherwise: BlockId(2),
                },
            },
            Block {
                insts: vec![],
                term: Term::Trap {
                    kind: TrapKind::Overflow,
                    position: Some(42),
                },
            },
            Block {
                insts: vec![
                    konst(3, 24),
                    konst(5, BOX),
                    Inst::CallRuntime {
                        func: RuntimeFn::Alloc,
                        args: vec![r(3), r(5)],
                        dsts: vec![r(4)],
                    },
                    Inst::Store {
                        src: r(0),
                        addr: r(4),
                        offset: 16,
                    },
                    konst(6, 1),
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(6),
                        a: r(0),
                        b: r(6),
                    },
                    Inst::Call {
                        func: FuncId(0).into(),
                        args: vec![r(6)],
                        dsts: vec![r(7)],
                    },
                    Inst::Load {
                        dst: r(8),
                        addr: r(4),
                        offset: 16,
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: r(7),
                        a: r(7),
                        b: r(8),
                    },
                ],
                term: Term::Return(vec![r(7)]),
            },
        ],
    }
}

fn check(config: FiberConfig) {
    let mut image = Image::new(&[deep_fn()]);
    let mut fiber = image.fiber(0, &[5000], config);
    let mut worker = Worker::new();
    let record = TypeDescriptor::Record {
        counted: Vec::new(),
    };
    worker.set_types(Arc::new(Types::new([(BOX as u32, record)])));
    worker.set_code_map(Arc::new(std::mem::take(&mut image.code)));
    assert_eq!(worker.resume(&mut fiber), FiberState::Trapped);
    let trap = Trap {
        kind: TrapKind::Overflow,
        position: Some(42),
        stack: vec![FuncId(0); 5001],
    };
    assert_eq!(fiber.trap(), Some(&trap));
    assert_eq!(fiber.results(), None);
    // Every frame's box was released on the way out.
    assert_eq!(worker.heap().live_blocks(), 0);
    // The worker runs the next fiber as usual.
    let mut next = image.fiber(0, &[0], config);
    assert_eq!(worker.resume(&mut next), FiberState::Trapped);
}

#[test]
fn a_trap_releases_what_the_frames_hold() {
    check(FiberConfig::default());
}

#[test]
fn a_trap_releases_what_the_frames_hold_while_the_stack_moves() {
    crag_runtime::stress::run_tortured(check);
}
