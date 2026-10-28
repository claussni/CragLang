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

//! Deferred teardown (Plan §11.7.12): a large drop frees a budget of boxes
//! and leaves the rest to the scheduler, which runs the dispose handlers in
//! it as detached tasks; a small one, or one outside a scheduler, frees
//! everything at once.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::{CountedField, RuntimeFn, TrapKind, TypeDescriptor};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::teardown::BUDGET;
use crag_runtime::{FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const DEFERRED: usize = 0;
const PLAIN: usize = 1;
const HANDLER: usize = 2;
const TRAPPING: usize = 3;

/// A node of a chain: a box holding a union, the next node or the tail.
const NODE: i64 = 3;

/// The tail of a chain: a box with a dispose handler, whose word of the
/// handler's code is at 16, and the address of a counter at 24.
const HANDLED: i64 = 4;

fn konst(dst: VReg, value: i64) -> Inst {
    Inst::Const { dst, value }
}

fn call(func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) -> Inst {
    Inst::CallRuntime { func, args, dsts }
}

fn store(src: VReg, addr: VReg, offset: i32) -> Inst {
    Inst::Store { src, addr, offset }
}

fn add_atomic(dst: VReg, addr: VReg, value: VReg) -> Inst {
    Inst::AtomicAdd {
        dst,
        addr,
        offset: 0,
        value,
    }
}

fn branch(cond: VReg, then: u32, otherwise: u32) -> Term {
    Term::Branch {
        cond,
        then: BlockId(then),
        otherwise: BlockId(otherwise),
    }
}

fn eq(dst: VReg, a: VReg, b: VReg) -> Inst {
    Inst::Cmp {
        cond: Cond::Eq,
        dst,
        a,
        b,
    }
}

fn block(insts: Vec<Inst>, term: Term) -> Block {
    Block { insts, term }
}

/// `dropper(n, code, counter) = (handled, disposal)`: builds a chain of `n`
/// nodes ending in a box whose handler is `code` and counts at `counter`,
/// gives up its reference to the first node with `release`, and returns
/// the counter as it is then and the dispose code the task's queue gives.
fn dropper(release: RuntimeFn) -> LirFunction {
    let (n, code, counter) = (r(0), r(1), r(2));
    let (index, payload, size, handled, tail, one, zero, node) =
        (r(3), r(4), r(5), r(6), r(7), r(8), r(9), r(10));
    let (done, fresh, minus, old, last, count, ptr, disposal) =
        (r(11), r(12), r(13), r(14), r(15), r(16), r(17), r(18));
    LirFunction {
        params: 3,
        returns: 2,
        vregs: 19,
        tracked: vec![payload, fresh],
        blocks: vec![
            block(
                vec![
                    konst(size, 32),
                    konst(handled, HANDLED),
                    call(RuntimeFn::Alloc, vec![size, handled], vec![tail]),
                    store(code, tail, 16),
                    store(counter, tail, 24),
                    Inst::Move {
                        dst: index,
                        src: handled,
                    },
                    Inst::Move {
                        dst: payload,
                        src: tail,
                    },
                    konst(one, 1),
                    konst(zero, 0),
                    konst(node, NODE),
                ],
                Term::Jump(BlockId(1)),
            ),
            block(vec![eq(done, n, zero)], branch(done, 3, 2)),
            block(
                vec![
                    call(RuntimeFn::Alloc, vec![size, node], vec![fresh]),
                    store(index, fresh, 16),
                    store(payload, fresh, 24),
                    Inst::Move {
                        dst: index,
                        src: node,
                    },
                    Inst::Move {
                        dst: payload,
                        src: fresh,
                    },
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: n,
                        a: n,
                        b: one,
                    },
                    Inst::Poll,
                ],
                Term::Jump(BlockId(1)),
            ),
            block(
                vec![
                    konst(minus, -1),
                    add_atomic(old, payload, minus),
                    eq(last, old, one),
                ],
                branch(last, 4, 5),
            ),
            block(
                vec![call(release, vec![payload], vec![])],
                Term::Jump(BlockId(5)),
            ),
            block(
                vec![
                    Inst::Load {
                        dst: count,
                        addr: counter,
                        offset: 0,
                    },
                    call(RuntimeFn::Disposal, vec![], vec![ptr, disposal]),
                ],
                Term::Return(vec![count, disposal]),
            ),
        ],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// `handler(ptr)`: a dispose handler that counts its run at the box's
/// counter and gives up the box's reference.
fn handler() -> LirFunction {
    let (ptr, counter, one, before, minus, old, last) = (r(0), r(1), r(2), r(3), r(4), r(5), r(6));
    LirFunction {
        params: 1,
        returns: 0,
        vregs: 7,
        tracked: vec![],
        blocks: vec![
            block(
                vec![
                    Inst::Load {
                        dst: counter,
                        addr: ptr,
                        offset: 24,
                    },
                    konst(one, 1),
                    add_atomic(before, counter, one),
                    konst(minus, -1),
                    add_atomic(old, ptr, minus),
                    eq(last, old, one),
                ],
                branch(last, 1, 2),
            ),
            block(
                vec![call(RuntimeFn::Release, vec![ptr], vec![])],
                Term::Jump(BlockId(2)),
            ),
            block(vec![], Term::Return(vec![])),
        ],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// `trapping(ptr)`: a dispose handler that traps.
fn trapping() -> LirFunction {
    LirFunction {
        params: 1,
        returns: 0,
        vregs: 1,
        tracked: vec![],
        blocks: vec![block(
            vec![],
            Term::Trap {
                kind: TrapKind::Overflow,
                position: None,
            },
        )],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

fn types() -> Arc<Types> {
    Arc::new(Types::new([
        (
            NODE as u32,
            TypeDescriptor::Record {
                counted: vec![CountedField::Union {
                    offset: 16,
                    boxed: vec![NODE as u32, HANDLED as u32],
                }],
                dispose: None,
            },
        ),
        (
            HANDLED as u32,
            TypeDescriptor::Record {
                counted: vec![],
                dispose: Some(16),
            },
        ),
    ]))
}

/// Ends the test process if the test hangs, as a teardown that never ends
/// would keep the scheduler waiting.
struct Watchdog(#[allow(dead_code)] mpsc::Sender<()>);

fn watchdog() -> Watchdog {
    let (done, waiting) = mpsc::channel::<()>();
    std::thread::spawn(move || {
        if waiting.recv_timeout(Duration::from_secs(60)) == Err(RecvTimeoutError::Timeout) {
            eprintln!("a teardown test hung for 60 seconds");
            std::process::abort();
        }
    });
    Watchdog(done)
}

fn image() -> Image {
    let mut image = Image::new(&[
        dropper(RuntimeFn::ReleaseDeferred),
        dropper(RuntimeFn::Release),
        handler(),
        trapping(),
    ]);
    image.with_task_entries();
    image
}

/// What a drop on a scheduler gave: the counter when the drop returned,
/// the dispose code the task's queue gave, the counter once the scheduler
/// is idle, and the deferred handlers that trapped.
fn drop_on_scheduler(n: u64, handler: usize) -> (u64, u64, u64, u64) {
    let counter = Box::new(AtomicU64::new(0));
    let mut image = image();
    let args = [
        n,
        image.functions[handler] as u64,
        std::ptr::from_ref(&*counter) as u64,
    ];
    let fiber = image.fiber_returning(DEFERRED, &args, 2, FiberConfig::default());
    let scheduler = Scheduler::new(
        SchedulerConfig {
            workers: 2,
            slice: Some(Duration::from_millis(1)),
        },
        types(),
        Arc::new(std::mem::take(&mut image.code)),
    );
    scheduler.spawn(fiber);
    let fibers = scheduler.wait();
    // Detached handlers are not among the fibers given back.
    assert_eq!(fibers.len(), 1);
    assert_eq!(
        fibers[0].state(),
        FiberState::Finished,
        "{:?}",
        fibers[0].trap()
    );
    let [before, disposal] = fibers[0].results().unwrap();
    (
        before,
        disposal,
        counter.load(Ordering::SeqCst),
        scheduler.deferred_traps(),
    )
}

#[test]
fn a_large_drop_leaves_the_rest_to_the_workers_which_run_its_handlers_as_tasks() {
    let _watchdog = watchdog();
    let (before, disposal, after, traps) = drop_on_scheduler(200 * BUDGET as u64, HANDLER);
    // The drop returned before the end of the chain was reached, and its
    // handler was not queued for the task.
    assert_eq!((before, disposal), (0, 0));
    // Once the scheduler is idle the teardown is done and the handler ran.
    assert_eq!((after, traps), (1, 0));
}

#[test]
fn a_small_drop_runs_its_handlers_through_the_tasks_queue() {
    let _watchdog = watchdog();
    let (before, disposal, after, _) = drop_on_scheduler(10, HANDLER);
    assert_eq!(before, 0);
    assert_ne!(disposal, 0);
    // No task ran it: the dropping function only took it.
    assert_eq!(after, 0);
}

#[test]
fn a_deferred_handler_that_traps_is_reported_and_no_one_waits_for_it() {
    let _watchdog = watchdog();
    let (_, disposal, after, traps) = drop_on_scheduler(5 * BUDGET as u64, TRAPPING);
    assert_eq!((disposal, after, traps), (0, 0, 1));
}

#[test]
fn without_a_scheduler_a_deferred_release_frees_everything_at_once() {
    let _watchdog = watchdog();
    for release in [DEFERRED, PLAIN] {
        let counter = Box::new(AtomicU64::new(0));
        let mut image = image();
        let args = [
            5 * BUDGET as u64,
            image.functions[HANDLER] as u64,
            std::ptr::from_ref(&*counter) as u64,
        ];
        let mut fiber = image.fiber_returning(release, &args, 2, FiberConfig::default());
        let mut worker = Worker::new();
        worker.set_types(types());
        assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
        let [_, disposal] = fiber.results().unwrap();
        assert_ne!(disposal, 0);
        // Only the tail lives on, with the reference its handler takes.
        assert_eq!(worker.heap().live_blocks(), 1);
    }
}
