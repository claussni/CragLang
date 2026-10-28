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

//! `rt_tx_throw` called deep in a fiber's stack: the frames above the call
//! with a handler release what they hold, and that frame continues at the
//! handler with what it holds (Plan §11.7.14).

mod common;

use std::sync::Arc;

use crag_abi::{FuncId, HandlerKind, RuntimeFn, TypeDescriptor};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::{FiberConfig, FiberState, Types, Worker};

use common::{Image, r};

const BOX: i64 = 4;

fn konst(dst: u32, value: i64) -> Inst {
    Inst::Const { dst: r(dst), value }
}

fn alloc(dst: u32, size: u32, field: u32) -> Vec<Inst> {
    vec![
        konst(size, 24),
        konst(field + 100, BOX),
        Inst::CallRuntime {
            func: RuntimeFn::Alloc,
            args: vec![r(size), r(field + 100)],
            dsts: vec![r(dst)],
        },
        Inst::Store {
            src: r(field),
            addr: r(dst),
            offset: 16,
        },
    ]
}

/// `outer(n, d) = 42 + 1000`: holds a box of 1000 and calls `deep(k, d)`
/// with a handler, from `k = n` down: each call but the last throws, and
/// the handler tries again with `k - 1`.
fn outer() -> LirFunction {
    let (n, d) = (0, 1);
    let mut first = vec![konst(2, 1000)];
    first.extend(alloc(3, 4, 2));
    LirFunction {
        params: 2,
        returns: 1,
        vregs: 210,
        tracked: vec![r(3)],
        blocks: vec![
            Block {
                insts: first,
                term: Term::Jump(BlockId(1)),
            },
            // The attempt.
            Block {
                insts: vec![
                    Inst::TryCall {
                        func: FuncId(1).into(),
                        args: vec![r(n), r(d)],
                        dsts: vec![r(5)],
                        handlers: vec![(HandlerKind::Transaction, BlockId(2))],
                    },
                    Inst::Load {
                        dst: r(6),
                        addr: r(3),
                        offset: 16,
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: r(5),
                        a: r(5),
                        b: r(6),
                    },
                    Inst::CallRuntime {
                        func: RuntimeFn::Release,
                        args: vec![r(3)],
                        dsts: vec![],
                    },
                ],
                term: Term::Return(vec![r(5)]),
            },
            // The handler: the box is still there.
            Block {
                insts: vec![
                    konst(7, 1),
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(n),
                        a: r(n),
                        b: r(7),
                    },
                    Inst::Load {
                        dst: r(8),
                        addr: r(3),
                        offset: 16,
                    },
                    konst(9, 1000),
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: r(10),
                        a: r(8),
                        b: r(9),
                    },
                ],
                term: Term::Branch {
                    cond: r(10),
                    then: BlockId(1),
                    otherwise: BlockId(3),
                },
            },
            Block {
                insts: vec![],
                term: Term::Return(vec![r(9)]),
            },
        ],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// `deep(k, d)`: `d` frames that each hold a box, then a throw if `k` is
/// above zero, else 42.
fn deep() -> LirFunction {
    let (k, d) = (0, 1);
    let mut down = alloc(3, 4, d);
    down.extend([
        konst(5, 1),
        Inst::Bin {
            op: BinOp::Sub,
            dst: r(5),
            a: r(d),
            b: r(5),
        },
        Inst::Call {
            func: FuncId(1).into(),
            args: vec![r(k), r(5)],
            dsts: vec![r(6)],
        },
        Inst::CallRuntime {
            func: RuntimeFn::Release,
            args: vec![r(3)],
            dsts: vec![],
        },
    ]);
    LirFunction {
        params: 2,
        returns: 1,
        vregs: 210,
        tracked: vec![r(3)],
        blocks: vec![
            Block {
                insts: vec![
                    konst(2, 0),
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: r(7),
                        a: r(d),
                        b: r(2),
                    },
                ],
                term: Term::Branch {
                    cond: r(7),
                    then: BlockId(1),
                    otherwise: BlockId(4),
                },
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Gt,
                    dst: r(7),
                    a: r(k),
                    b: r(2),
                }],
                term: Term::Branch {
                    cond: r(7),
                    then: BlockId(2),
                    otherwise: BlockId(3),
                },
            },
            Block {
                insts: vec![Inst::CallRuntime {
                    func: RuntimeFn::TxThrow,
                    args: vec![],
                    dsts: vec![],
                }],
                term: Term::Return(vec![r(2)]),
            },
            Block {
                insts: vec![konst(8, 42)],
                term: Term::Return(vec![r(8)]),
            },
            Block {
                insts: down,
                term: Term::Return(vec![r(6)]),
            },
        ],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

fn check(n: u64, d: u64, config: FiberConfig) {
    let mut image = Image::new(&[outer(), deep()]);
    let mut fiber = image.fiber(0, &[n, d], config);
    let mut worker = Worker::new();
    let record = TypeDescriptor::Record {
        counted: Vec::new(),
        dispose: None,
    };
    worker.set_types(Arc::new(Types::new([(BOX as u32, record)])));
    worker.set_code_map(Arc::new(std::mem::take(&mut image.code)));
    assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
    assert_eq!(fiber.results().unwrap()[0], 1042);
    // The frames the throws left released their boxes, and the handler's
    // frame kept its own until it released it.
    assert_eq!(worker.heap().live_blocks(), 0);
}

#[test]
fn a_throw_continues_at_the_handler() {
    check(1, 0, FiberConfig::default());
    check(3, 5, FiberConfig::default());
}

#[test]
fn throws_through_many_frames() {
    check(4, 3000, FiberConfig::default());
}
