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

//! Side-stack pushes from generated code: addresses that stay valid while
//! the machine stack moves, chunks, and popping on return.

mod common;

use common::{Image, finish, r};
use crag_abi::FuncId;
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::FiberConfig;

/// `f(p) = p[0] + p[1]`: reads two words through a pointer it was given.
fn sum_pair_fn() -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 3,
        tracked: vec![],
        blocks: vec![Block {
            insts: vec![
                Inst::Load {
                    dst: r(1),
                    addr: r(0),
                    offset: 0,
                },
                Inst::Load {
                    dst: r(2),
                    addr: r(0),
                    offset: 8,
                },
                Inst::Bin {
                    op: BinOp::Add,
                    dst: r(1),
                    a: r(1),
                    b: r(2),
                },
            ],
            term: Term::Return(vec![r(1)]),
        }],
    }
}

/// `f(n) = sum_pair(&(n, 2 * n))`: puts a pair on the side stack and passes
/// its address to a callee, as a record passed by reference would be.
fn pass_pair_fn(sum_pair: u32) -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 4, // n, pair, 2 * n, result
        tracked: vec![],
        blocks: vec![Block {
            insts: vec![
                Inst::SidePush {
                    dst: r(1),
                    size: 16,
                    align: 8,
                },
                Inst::Store {
                    src: r(0),
                    addr: r(1),
                    offset: 0,
                },
                Inst::Bin {
                    op: BinOp::Add,
                    dst: r(2),
                    a: r(0),
                    b: r(0),
                },
                Inst::Store {
                    src: r(2),
                    addr: r(1),
                    offset: 8,
                },
                Inst::Call {
                    func: FuncId(sum_pair),
                    args: vec![r(1)],
                    dsts: vec![r(3)],
                },
            ],
            term: Term::Return(vec![r(3)]),
        }],
    }
}

/// `f(n) = if n == 0 { 0 } else { f(n - 1) + n }`, with `n` kept in a
/// side-stack slot across the recursive call and read back through its
/// address afterwards.
fn sum_through_slots_fn(self_id: u32) -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 7, // n, zero, flag, slot, one / n - 1, result, n read back
        tracked: vec![],
        blocks: vec![
            Block {
                insts: vec![
                    Inst::Const {
                        dst: r(1),
                        value: 0,
                    },
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
                term: Term::Return(vec![r(1)]),
            },
            Block {
                insts: vec![
                    Inst::SidePush {
                        dst: r(3),
                        size: 8,
                        align: 8,
                    },
                    Inst::Store {
                        src: r(0),
                        addr: r(3),
                        offset: 0,
                    },
                    Inst::Const {
                        dst: r(4),
                        value: 1,
                    },
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(4),
                        a: r(0),
                        b: r(4),
                    },
                    Inst::Call {
                        func: FuncId(self_id),
                        args: vec![r(4)],
                        dsts: vec![r(5)],
                    },
                    Inst::Load {
                        dst: r(6),
                        addr: r(3),
                        offset: 0,
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: r(5),
                        a: r(5),
                        b: r(6),
                    },
                ],
                term: Term::Return(vec![r(5)]),
            },
        ],
    }
}

/// `f(n) = callee(n) + callee(n - 1) + ... + callee(1)` as a loop.
fn call_in_loop_fn(callee: u32) -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 6, // n, acc, zero, one, flag, result
        tracked: vec![],
        blocks: vec![
            Block {
                insts: vec![
                    Inst::Const {
                        dst: r(1),
                        value: 0,
                    },
                    Inst::Const {
                        dst: r(2),
                        value: 0,
                    },
                    Inst::Const {
                        dst: r(3),
                        value: 1,
                    },
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Gt,
                    dst: r(4),
                    a: r(0),
                    b: r(2),
                }],
                term: Term::Branch {
                    cond: r(4),
                    then: BlockId(2),
                    otherwise: BlockId(3),
                },
            },
            Block {
                insts: vec![
                    Inst::Call {
                        func: FuncId(callee),
                        args: vec![r(0)],
                        dsts: vec![r(5)],
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: r(1),
                        a: r(1),
                        b: r(5),
                    },
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(0),
                        a: r(0),
                        b: r(3),
                    },
                    Inst::Poll,
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![],
                term: Term::Return(vec![r(1)]),
            },
        ],
    }
}

/// Pushes `size` bytes at `align`, writes and reads the last word, and
/// returns the address so the test can inspect it.
fn push_and_touch_fn(size: u32, align: u32) -> LirFunction {
    let last = size as i32 - 8;
    LirFunction {
        params: 0,
        returns: 1,
        vregs: 3, // address, value written, value read
        tracked: vec![],
        blocks: vec![Block {
            insts: vec![
                Inst::SidePush {
                    dst: r(0),
                    size,
                    align,
                },
                Inst::Const {
                    dst: r(1),
                    value: 77,
                },
                Inst::Store {
                    src: r(1),
                    addr: r(0),
                    offset: last,
                },
                Inst::Load {
                    dst: r(2),
                    addr: r(0),
                    offset: last,
                },
                // address + (read - written): the address if the word held.
                Inst::Bin {
                    op: BinOp::Sub,
                    dst: r(2),
                    a: r(2),
                    b: r(1),
                },
                Inst::Bin {
                    op: BinOp::Add,
                    dst: r(0),
                    a: r(0),
                    b: r(2),
                },
            ],
            term: Term::Return(vec![r(0)]),
        }],
    }
}

#[test]
fn an_address_on_the_side_stack_survives_stack_moves() {
    // Tortured, the call to `sum_pair` moves the machine stack while the
    // pair's address sits in the caller's frame.
    for config in [FiberConfig::normal(), FiberConfig::tortured()] {
        let mut image = Image::new(&[pass_pair_fn(1), sum_pair_fn()]);
        let mut fiber = image.fiber(0, &[14], config);
        assert_eq!(finish(&mut fiber), 42);
        assert_eq!(fiber.side_stack_chunks(), 1);
        assert!(fiber.side_stack_is_empty());
    }
}

#[test]
fn pushes_continue_in_new_chunks_and_keep_old_addresses() {
    let depth = 2000u64;
    for (config, at_least) in [(FiberConfig::normal(), 4), (FiberConfig::tortured(), 100)] {
        let mut image = Image::new(&[sum_through_slots_fn(0)]);
        let mut fiber = image.fiber(0, &[depth], config);
        // Every frame reads its slot after all deeper frames pushed theirs.
        assert_eq!(finish(&mut fiber), depth * (depth + 1) / 2);
        assert!(
            fiber.side_stack_chunks() >= at_least,
            "{} chunks",
            fiber.side_stack_chunks()
        );
        assert!(fiber.side_stack_is_empty());
    }
}

#[test]
fn returning_frees_what_a_function_pushed() {
    let mut image = Image::new(&[call_in_loop_fn(1), pass_pair_fn(2), sum_pair_fn()]);
    let n = 100_000u64;
    let mut fiber = image.fiber(0, &[n], FiberConfig::normal());
    assert_eq!(finish(&mut fiber), 3 * n * (n + 1) / 2);
    // A hundred thousand calls pushed sixteen bytes each into the same place.
    assert_eq!(fiber.side_stack_chunks(), 1);
}

#[test]
fn chunks_are_reused_after_the_stack_shrank_back() {
    // Two deep recursions in a row: the second walks through the chunks the
    // first left behind instead of allocating again.
    let mut image = Image::new(&[call_in_loop_fn(1), sum_through_slots_fn(1)]);
    let mut once = image.fiber(1, &[1000], FiberConfig::normal());
    finish(&mut once);
    let mut repeated = image.fiber(0, &[1000], FiberConfig::normal());
    finish(&mut repeated);
    assert_eq!(repeated.side_stack_chunks(), once.side_stack_chunks());
}

#[test]
fn a_large_aligned_push_gets_a_chunk_of_its_own() {
    let mut image = Image::new(&[push_and_touch_fn(10_000, 64), push_and_touch_fn(24, 1)]);
    let mut fiber = image.fiber(0, &[], FiberConfig::normal());
    let address = finish(&mut fiber);
    assert_ne!(address, 0);
    assert_eq!(address % 64, 0);
    assert_eq!(fiber.side_stack_chunks(), 1);

    let mut fiber = image.fiber(1, &[], FiberConfig::normal());
    assert_ne!(finish(&mut fiber), 0);
}
