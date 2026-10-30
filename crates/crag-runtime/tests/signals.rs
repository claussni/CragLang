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

//! Signals of blocks (Plan §11.7.10): which emissions an outcome delivers,
//! in what order, and that the others and those of a task that stops are
//! given up.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};

mod common;

use common::{Image, r};
use crag_abi::{
    CountedField, ElementLayout, REF_COMMITTED, REF_CONFLICT, RuntimeFn, SIGNAL_FAIL, SIGNAL_NONE,
    SIGNAL_OK, SIGNAL_PLAIN, SIGNAL_RETRY, TrapKind, TypeDescriptor,
};
use crag_codegen::{Block, Inst, LirFunction, Term, VReg};
use crag_runtime::{FiberConfig, FiberState, Types, Worker};

/// The list type whose elements the signals are laid out as: one word.
const INTS: u64 = 1;

/// A list type of boxes.
const BOXES: u64 = 2;

/// The signals a script can take at its end.
const MOST: usize = 8;

/// A step of a script, which runs on one fiber.
#[derive(Clone, Copy)]
enum Step {
    Begin,
    Commit,
    Abort,
    Retry,
    Emit(u64, u64, u64),
    /// Reads the ref, as an update closure starts.
    Read,
    /// Commits the update with a value: its status is the script's result.
    RefCommit(u64),
    Done,
    /// Writes the ref as another task would.
    Swap(u64),
    Trap,
}

/// Registers: the ref cell, room for a read, the signals' words and
/// their list types; then the script's own.
struct Builder {
    insts: Vec<Inst>,
    next: u32,
    version: VReg,
    status: VReg,
}

impl Builder {
    fn reg(&mut self) -> VReg {
        self.next += 1;
        r(self.next - 1)
    }

    fn konst(&mut self, value: u64) -> VReg {
        let dst = self.reg();
        self.insts.push(Inst::Const {
            dst,
            value: value as i64,
        });
        dst
    }

    fn call(&mut self, func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) {
        self.insts.push(Inst::CallRuntime { func, args, dsts });
    }
}

/// `script(cell, scratch, out, lists) = status`: runs the steps, then takes
/// up to [`MOST`] signals, three words each to `out` and their list types to
/// `lists`. The status is that of the last ref commit.
fn script(steps: &[Step]) -> LirFunction {
    let (cell, scratch, out, lists) = (r(0), r(1), r(2), r(3));
    let mut b = Builder {
        insts: Vec::new(),
        next: 6,
        version: r(4),
        status: r(5),
    };
    let status = b.status;
    b.insts.push(Inst::Const {
        dst: status,
        value: -1,
    });
    let mut term = None;
    for &step in steps {
        match step {
            Step::Begin => b.call(RuntimeFn::TxBegin, vec![], vec![]),
            Step::Commit => {
                let s = b.reg();
                b.call(RuntimeFn::TxCommit, vec![], vec![s]);
            }
            Step::Abort => b.call(RuntimeFn::TxAbort, vec![], vec![]),
            Step::Retry => b.call(RuntimeFn::TxRetry, vec![], vec![]),
            Step::Emit(qualifier, list, w0) => {
                let args = vec![
                    b.konst(qualifier),
                    b.konst(list),
                    b.konst(w0),
                    b.konst(0),
                    b.konst(0),
                ];
                let held = b.reg();
                b.call(RuntimeFn::SignalEmit, args, vec![held]);
            }
            Step::Read => {
                let version = b.version;
                b.call(RuntimeFn::RefRead, vec![cell, scratch], vec![version]);
            }
            Step::RefCommit(value) => {
                let args = vec![b.version, b.konst(INTS), b.konst(value), b.konst(0)];
                let args = [vec![cell], args].concat();
                b.call(RuntimeFn::RefCommit, args, vec![status]);
            }
            Step::Done => b.call(RuntimeFn::RefDone, vec![], vec![]),
            Step::Swap(value) => {
                let args = vec![cell, b.konst(INTS), b.konst(value), b.konst(0)];
                let (o0, o1) = (b.reg(), b.reg());
                b.call(RuntimeFn::RefSwap, args, vec![o0, o1]);
            }
            Step::Trap => {
                term = Some(Term::Trap {
                    kind: TrapKind::Overflow,
                    position: None,
                });
                break;
            }
        }
    }
    // A script that traps takes nothing.
    let takes = if term.is_some() { 0 } else { MOST };
    for i in 0..takes {
        let (offset, at, list) = (b.konst(24 * i as u64), b.reg(), b.reg());
        b.insts.push(Inst::Bin {
            op: crag_codegen::BinOp::Add,
            dst: at,
            a: out,
            b: offset,
        });
        b.call(RuntimeFn::SignalNext, vec![at], vec![list]);
        b.insts.push(Inst::Store {
            src: list,
            addr: lists,
            offset: 8 * i as i32,
        });
    }
    LirFunction {
        params: 4,
        returns: 1,
        vregs: b.next,
        tracked: vec![],
        blocks: vec![Block {
            insts: b.insts,
            term: term.unwrap_or(Term::Return(vec![status])),
        }],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

fn types() -> Arc<Types> {
    let list = |counted: Vec<CountedField>| TypeDescriptor::List {
        element: ElementLayout {
            words: 1,
            counted: counted.clone(),
        },
        cell: ElementLayout { words: 1, counted },
    };
    Arc::new(Types::new([
        (INTS as u32, list(vec![])),
        (BOXES as u32, list(vec![CountedField::Box(0)])),
    ]))
}

/// What a script did.
struct Run {
    state: FiberState,
    status: u64,
    /// The first word of each signal taken, in order.
    taken: Vec<u64>,
    /// The ref's value at the end.
    value: u64,
}

fn run_script(steps: &[Step]) -> Run {
    let mut image = Image::new(&[script(steps)]);
    let mut worker = Worker::new();
    worker.set_types(types());
    let cell = Box::new([AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)]);
    let mut scratch = [0u64; 2];
    let mut out = [0u64; 3 * MOST];
    let mut lists = [SIGNAL_NONE; MOST];
    let args = [
        std::ptr::from_ref(&*cell) as u64,
        scratch.as_mut_ptr() as u64,
        out.as_mut_ptr() as u64,
        lists.as_mut_ptr() as u64,
    ];
    let mut fiber = image.fiber_returning(0, &args, 1, FiberConfig::default());
    let state = worker.resume(&mut fiber);
    let status = fiber.results().map_or(u64::MAX, |r| r[0]);
    let taken = lists
        .iter()
        .take_while(|&&list| list != SIGNAL_NONE)
        .enumerate()
        .map(|(i, _)| out[3 * i])
        .collect();
    Run {
        state,
        status,
        taken,
        value: cell[1].load(Ordering::SeqCst),
    }
}

/// A box the test owns: a header whose count the runtime changes, which
/// never reaches zero, so the runtime never frees it.
#[repr(C, align(16))]
struct FakeBox {
    count: AtomicU64,
    type_index: u64,
}

impl FakeBox {
    fn new() -> Box<FakeBox> {
        Box::new(FakeBox {
            count: AtomicU64::new(1_000),
            type_index: 0,
        })
    }

    fn count(&self) -> u64 {
        self.count.load(Ordering::SeqCst)
    }

    /// A reference for the script to emit, which owns it.
    fn reference(&self) -> u64 {
        self.count.fetch_add(1, Ordering::SeqCst);
        std::ptr::from_ref(self) as u64
    }
}

use Step::*;

fn plain(w: u64) -> Step {
    Emit(SIGNAL_PLAIN, INTS, w)
}

fn ok(w: u64) -> Step {
    Emit(SIGNAL_OK, INTS, w)
}

fn fail(w: u64) -> Step {
    Emit(SIGNAL_FAIL, INTS, w)
}

fn retry(w: u64) -> Step {
    Emit(SIGNAL_RETRY, INTS, w)
}

#[test]
fn a_commit_delivers_the_plain_and_ok_signals_in_order() {
    let got = run_script(&[Begin, plain(1), fail(2), ok(3), retry(4), plain(5), Commit]);
    assert_eq!(got.state, FiberState::Finished);
    assert_eq!(got.taken, [1, 3, 5]);
}

#[test]
fn nothing_is_delivered_before_the_outcome() {
    let got = run_script(&[Begin, plain(1), ok(2), Begin, plain(3), Commit]);
    assert_eq!(got.taken, [] as [u64; 0]);
}

#[test]
fn an_inner_block_that_commits_hands_its_signals_to_the_outer() {
    let got = run_script(&[
        Begin,
        plain(1),
        Begin,
        plain(2),
        fail(3),
        Commit,
        plain(4),
        Commit,
    ]);
    assert_eq!(got.taken, [1, 2, 4]);
    // The outer block fails instead: the inner block's fail signals go
    // with it.
    let got = run_script(&[Begin, fail(1), Begin, plain(2), fail(3), Commit, Abort]);
    assert_eq!(got.taken, [1, 3]);
}

#[test]
fn an_inner_block_that_fails_delivers_its_fail_signals_at_once() {
    let got = run_script(&[
        Begin,
        plain(1),
        Begin,
        plain(2),
        fail(3),
        retry(4),
        Abort,
        plain(5),
        Commit,
    ]);
    assert_eq!(got.taken, [3, 1, 5]);
}

#[test]
fn a_conflict_delivers_the_attempts_retry_signals_also_after_an_inner_failure() {
    let got = run_script(&[
        Begin,
        plain(1),
        retry(2),
        Begin,
        fail(3),
        retry(4),
        Abort,
        retry(5),
        Retry,
        plain(6),
        Commit,
    ]);
    assert_eq!(got.state, FiberState::Finished);
    assert_eq!(got.taken, [3, 2, 4, 5, 6]);
}

#[test]
fn an_update_delivers_by_its_outcome() {
    // A conflict delivers the retry signals; the rerun commits.
    let got = run_script(&[
        Read,
        plain(1),
        retry(2),
        Swap(7),
        RefCommit(9),
        Read,
        plain(3),
        RefCommit(9),
    ]);
    assert_eq!(got.status, REF_COMMITTED);
    assert_eq!(got.value, 9);
    assert_eq!(got.taken, [2, 3]);
    let conflicted = run_script(&[Read, plain(1), Swap(7), RefCommit(9)]);
    assert_eq!(conflicted.status, REF_CONFLICT);
    assert_eq!(conflicted.taken, [] as [u64; 0]);
    // A closure that gives an error delivers its fail signals.
    let got = run_script(&[Read, plain(1), fail(2), Done]);
    assert_eq!(got.taken, [2]);
}

#[test]
fn signals_not_delivered_are_given_up() {
    let x = FakeBox::new();
    let steps = [
        Begin,
        Emit(SIGNAL_FAIL, BOXES, x.reference()),
        Emit(SIGNAL_RETRY, BOXES, x.reference()),
        Emit(SIGNAL_PLAIN, BOXES, x.reference()),
        Commit,
    ];
    let got = run_script(&steps);
    assert_eq!(got.taken.len(), 1);
    // The delivered one was lent until the next take; the others were
    // given up.
    assert_eq!(x.count(), 1_000);
}

#[test]
fn a_task_that_stops_in_a_block_gives_its_signals_up() {
    let x = FakeBox::new();
    let steps = [
        Begin,
        Emit(SIGNAL_PLAIN, BOXES, x.reference()),
        Begin,
        Emit(SIGNAL_FAIL, BOXES, x.reference()),
        Abort,
        Trap,
    ];
    let got = run_script(&steps);
    assert_eq!(got.state, FiberState::Trapped);
    // Also the one the inner failure made ready, which nobody took.
    assert_eq!(x.count(), 1_000);
}
