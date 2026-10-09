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

//! The list and map functions called from generated code on a fiber, while
//! the stack moves.

mod common;

use std::sync::Arc;

use crag_abi::{ElementLayout, LEN_OFFSET, LIST_SIZE, MAP_SIZE, RuntimeFn, TypeDescriptor};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::{FiberConfig, FiberState, Types, Worker};

use common::{Image, r};

const LIST: i64 = 5;
const MAP: i64 = 6;

fn konst(dst: u32, value: i64) -> Inst {
    Inst::Const { dst: r(dst), value }
}

fn call(func: RuntimeFn, args: &[u32], dst: u32) -> Inst {
    Inst::CallRuntime {
        func,
        args: args.iter().map(|&a| r(a)).collect(),
        dsts: vec![r(dst)],
    }
}

fn bin(op: BinOp, dst: u32, a: u32, b: u32) -> Inst {
    Inst::Bin {
        op,
        dst: r(dst),
        a: r(a),
        b: r(b),
    }
}

fn store(src: u32, addr: u32, offset: i32) -> Inst {
    Inst::Store {
        src: r(src),
        addr: r(addr),
        offset,
    }
}

fn load(dst: u32, addr: u32, offset: i32) -> Inst {
    Inst::Load {
        dst: r(dst),
        addr: r(addr),
        offset,
    }
}

/// Gives up the reference in `ptr`, the only one: the count drops to zero
/// and the runtime frees the collection.
fn free(ptr: u32, scratch: u32) -> [Inst; 3] {
    [
        konst(scratch, -1),
        Inst::AtomicAdd {
            dst: r(scratch),
            addr: r(ptr),
            offset: 0,
            value: r(scratch),
        },
        Inst::CallRuntime {
            func: RuntimeFn::Release,
            args: vec![r(ptr)],
            dsts: Vec::new(),
        },
    ]
}

/// `f(n)`: pushes `0..n` onto a list and binds each `i` to `2 i` in a map,
/// polling on the way, then adds the list's elements, the map's value of
/// `n - 1` and the length of the list without its ends, and frees all.
fn collections_fn() -> LirFunction {
    // r0 n, r1 list, r2 map, r3 i, r4 zero, r5 one, r6 flag, r7 sum,
    // r8 element address, r9 word, r10 slice, r11.. scratch.
    let branch = |cond: u32, then, otherwise| Term::Branch {
        cond: r(cond),
        then: BlockId(then),
        otherwise: BlockId(otherwise),
    };
    let tracked: Vec<VReg> = [1, 2, 10].into_iter().map(r).collect();
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 16,
        tracked,
        blocks: vec![
            Block {
                insts: vec![
                    konst(4, 0),
                    konst(5, 1),
                    konst(11, i64::from(LIST_SIZE)),
                    konst(12, LIST),
                    call(RuntimeFn::Alloc, &[11, 12], 1),
                    store(4, 1, LEN_OFFSET),
                    store(4, 1, 24),
                    store(4, 1, 32),
                    konst(11, i64::from(MAP_SIZE)),
                    konst(12, MAP),
                    call(RuntimeFn::Alloc, &[11, 12], 2),
                    store(4, 2, LEN_OFFSET),
                    store(4, 2, 24),
                    konst(3, 0),
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Eq,
                    dst: r(6),
                    a: r(3),
                    b: r(0),
                }],
                term: branch(6, 3, 2),
            },
            Block {
                insts: vec![
                    call(RuntimeFn::ListPush, &[1, 3, 4], 1),
                    bin(BinOp::Add, 11, 3, 3),
                    call(RuntimeFn::MapInsert, &[2, 3, 4, 11, 4], 2),
                    bin(BinOp::Add, 3, 3, 5),
                    Inst::Poll,
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![konst(3, 0), konst(7, 0)],
                term: Term::Jump(BlockId(4)),
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Eq,
                    dst: r(6),
                    a: r(3),
                    b: r(0),
                }],
                term: branch(6, 6, 5),
            },
            Block {
                insts: vec![
                    call(RuntimeFn::ListElem, &[1, 3], 8),
                    load(9, 8, 0),
                    bin(BinOp::Add, 7, 7, 9),
                    bin(BinOp::Add, 3, 3, 5),
                    Inst::Poll,
                ],
                term: Term::Jump(BlockId(4)),
            },
            Block {
                insts: [
                    vec![
                        bin(BinOp::Sub, 11, 0, 5),
                        call(RuntimeFn::MapGet, &[2, 11, 4], 8),
                        load(9, 8, 0),
                        bin(BinOp::Add, 7, 7, 9),
                        call(RuntimeFn::ListSlice, &[1, 5, 5], 10),
                        load(9, 10, LEN_OFFSET),
                        bin(BinOp::Add, 7, 7, 9),
                    ],
                    free(1, 13).to_vec(),
                    free(2, 13).to_vec(),
                    free(10, 13).to_vec(),
                ]
                .concat(),
                term: Term::Return(vec![r(7)]),
            },
        ],
    }
}

fn check(config: FiberConfig) {
    let mut image = Image::new(&[collections_fn()]);
    let n = 3000u64;
    let mut fiber = image.fiber(0, &[n], config);
    let mut worker = Worker::new();
    let word = ElementLayout {
        words: 1,
        counted: Vec::new(),
    };
    worker.set_types(Arc::new(Types::new([
        (
            LIST as u32,
            TypeDescriptor::List {
                element: word.clone(),
            },
        ),
        (
            MAP as u32,
            TypeDescriptor::Map {
                key: word.clone(),
                value: word,
            },
        ),
    ])));
    assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
    let expected = n * (n - 1) / 2 + 2 * (n - 1) + (n - 2);
    assert_eq!(fiber.results().unwrap()[0], expected);
    assert_eq!(worker.heap().live_blocks(), 0);
}

#[test]
fn generated_code_builds_and_reads_collections() {
    check(FiberConfig::default());
}

#[test]
fn generated_code_builds_and_reads_collections_while_the_stack_moves() {
    crag_runtime::stress::run_tortured(check);
}
