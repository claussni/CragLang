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

//! `rt_release` called from generated code on a fiber, freeing a long chain
//! of boxes, while the stack moves.

mod common;

use std::sync::Arc;

use crag_abi::{CountedField, RuntimeFn, TypeDescriptor};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::{FiberConfig, FiberState, Types, Worker};

use common::{Image, r};

/// The type index of a node: a box holding a union, the next node or
/// nothing.
const NODE: i64 = 3;

/// `chain(n)`: allocates a chain of `n` nodes, each holding the one made
/// before, then gives up its reference to the last, which frees them all.
/// Returns the last node's count before the release, which must be one.
fn chain_fn() -> LirFunction {
    let konst = |dst, value| Inst::Const { dst: r(dst), value };
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 12,
        tracked: vec![r(2), r(8)],
        blocks: vec![
            // The union held so far: no index, no payload.
            Block {
                insts: vec![
                    konst(1, 0),
                    konst(2, 0),
                    konst(3, 32),
                    konst(4, NODE),
                    konst(5, 1),
                    konst(7, 0),
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Eq,
                    dst: r(6),
                    a: r(0),
                    b: r(7),
                }],
                term: Term::Branch {
                    cond: r(6),
                    then: BlockId(3),
                    otherwise: BlockId(2),
                },
            },
            Block {
                insts: vec![
                    Inst::CallRuntime {
                        func: RuntimeFn::Alloc,
                        args: vec![r(3), r(4)],
                        dsts: vec![r(8)],
                    },
                    Inst::Store {
                        src: r(1),
                        addr: r(8),
                        offset: 16,
                    },
                    Inst::Store {
                        src: r(2),
                        addr: r(8),
                        offset: 24,
                    },
                    Inst::Move {
                        dst: r(1),
                        src: r(4),
                    },
                    Inst::Move {
                        dst: r(2),
                        src: r(8),
                    },
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(0),
                        a: r(0),
                        b: r(5),
                    },
                    Inst::Poll,
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![
                    konst(9, -1),
                    Inst::AtomicAdd {
                        dst: r(10),
                        addr: r(2),
                        offset: 0,
                        value: r(9),
                    },
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: r(11),
                        a: r(10),
                        b: r(5),
                    },
                ],
                term: Term::Branch {
                    cond: r(11),
                    then: BlockId(4),
                    otherwise: BlockId(5),
                },
            },
            Block {
                insts: vec![Inst::CallRuntime {
                    func: RuntimeFn::Release,
                    args: vec![r(2)],
                    dsts: Vec::new(),
                }],
                term: Term::Jump(BlockId(5)),
            },
            Block {
                insts: vec![],
                term: Term::Return(vec![r(10)]),
            },
        ],
    }
}

fn check(config: FiberConfig) {
    let mut image = Image::new(&[chain_fn()]);
    let mut fiber = image.fiber(0, &[100_000], config);
    let mut worker = Worker::new();
    worker.set_types(Arc::new(Types::new([(
        NODE as u32,
        TypeDescriptor {
            counted: vec![CountedField::Union {
                offset: 16,
                boxed: vec![NODE as u32],
            }],
        },
    )])));
    assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
    assert_eq!(fiber.results().unwrap()[0], 1);
    let heap = worker.heap();
    assert_eq!(heap.live_blocks(), 0);
    assert_eq!(heap.pages_in_use(), 1);
}

#[test]
fn generated_code_frees_a_chain() {
    check(FiberConfig::default());
}

#[test]
fn generated_code_frees_a_chain_while_the_stack_moves() {
    crag_runtime::stress::run_tortured(check);
}
