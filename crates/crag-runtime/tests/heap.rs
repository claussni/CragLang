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

//! `rt_alloc` called from generated code on a fiber, while its stack moves.

mod common;

use common::{Image, finish, r};
use crag_abi::{FuncId, RuntimeFn};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::FiberConfig;

/// `f(n)`: allocates a box of three words with type index `n` and `n` in
/// its field, recurses with `n - 1`, and then adds the box's count, type
/// index and field to the result, so every box must survive the calls made
/// after it was allocated. `f(n) = n * (n + 1) + n`.
fn boxes_fn() -> LirFunction {
    let load = |dst, offset| Inst::Load {
        dst: r(dst),
        addr: r(4),
        offset,
    };
    let add = Inst::Bin {
        op: BinOp::Add,
        dst: r(7),
        a: r(7),
        b: r(8),
    };
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 9,
        tracked: vec![r(4)],
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
                    Inst::Const {
                        dst: r(3),
                        value: 24,
                    },
                    Inst::CallRuntime {
                        func: RuntimeFn::Alloc,
                        args: vec![r(3), r(0)],
                        dsts: vec![r(4)],
                    },
                    Inst::Store {
                        src: r(0),
                        addr: r(4),
                        offset: 16,
                    },
                    Inst::Const {
                        dst: r(5),
                        value: 1,
                    },
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(6),
                        a: r(0),
                        b: r(5),
                    },
                    Inst::Call {
                        func: FuncId(0).into(),
                        args: vec![r(6)],
                        dsts: vec![r(7)],
                    },
                    load(8, 0),
                    add.clone(),
                    load(8, 8),
                    add.clone(),
                    load(8, 16),
                    add,
                ],
                term: Term::Return(vec![r(7)]),
            },
        ],
        data: Vec::new(),
    }
}

fn check(config: FiberConfig) {
    let mut image = Image::new(&[boxes_fn()]);
    let n = 5000u64;
    let mut fiber = image.fiber(0, &[n], config);
    assert_eq!(finish(&mut fiber), n * (n + 1) + n);
}

#[test]
fn generated_code_allocates() {
    check(FiberConfig::default());
}

#[test]
fn generated_code_allocates_while_the_stack_moves() {
    crag_runtime::stress::run_tortured(check);
}
