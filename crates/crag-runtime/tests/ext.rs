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

//! `ext` (Plan §11.7.9): tasks take turns at the lock, also when they
//! suspend while holding it; a cancelled wait leaves the queue, and a task
//! that stops holding the lock gives it up.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::{RuntimeFn, TrapKind};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::{Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const EXT_NEW: usize = 0;
const EXT_FREE: usize = 1;
const TURNS: usize = 2;
const HOLD: usize = 3;
const ONCE: usize = 4;
const TRAP_HOLDING: usize = 5;

fn konst(dst: VReg, value: i64) -> Inst {
    Inst::Const { dst, value }
}

fn runtime(func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) -> Inst {
    Inst::CallRuntime { func, args, dsts }
}

fn block(insts: Vec<Inst>, term: Term) -> Block {
    Block { insts, term }
}

fn lir(params: u32, returns: u32, vregs: u32, blocks: Vec<Block>) -> LirFunction {
    LirFunction {
        params,
        returns,
        vregs,
        tracked: vec![],
        blocks,
        data: Vec::new(),
    }
}

fn calling(func: RuntimeFn, params: u32, results: u32) -> LirFunction {
    let args = (0..params).map(r).collect();
    let dsts: Vec<_> = (params..params + results).map(r).collect();
    lir(
        params,
        results,
        params + results,
        vec![block(
            vec![runtime(func, args, dsts.clone())],
            Term::Return(dsts),
        )],
    )
}

/// `turns(ext, counter, n) = n`: `n` times, adds one to the word at
/// `counter` while it holds the lock, yielding between the load and the
/// store, so that a second holder would lose an increment.
fn turns() -> LirFunction {
    let (ext, counter, n) = (r(0), r(1), r(2));
    let (i, one, flag, v) = (r(3), r(4), r(5), r(6));
    lir(
        3,
        1,
        7,
        vec![
            block(vec![konst(i, 0), konst(one, 1)], Term::Jump(BlockId(1))),
            block(
                vec![Inst::Cmp {
                    cond: Cond::Ge,
                    dst: flag,
                    a: i,
                    b: n,
                }],
                Term::Branch {
                    cond: flag,
                    then: BlockId(3),
                    otherwise: BlockId(2),
                },
            ),
            block(
                vec![
                    runtime(RuntimeFn::ExtLock, vec![ext], vec![]),
                    Inst::Load {
                        dst: v,
                        addr: counter,
                        offset: 0,
                    },
                    runtime(RuntimeFn::Yield, vec![], vec![]),
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: v,
                        a: v,
                        b: one,
                    },
                    Inst::Store {
                        src: v,
                        addr: counter,
                        offset: 0,
                    },
                    runtime(RuntimeFn::ExtUnlock, vec![ext], vec![]),
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: i,
                        a: i,
                        b: one,
                    },
                    Inst::Poll,
                ],
                Term::Jump(BlockId(1)),
            ),
            block(vec![], Term::Return(vec![n])),
        ],
    )
}

/// `hold(ext, nanos) = nanos`: holds the lock while it sleeps.
fn hold() -> LirFunction {
    let (ext, nanos) = (r(0), r(1));
    lir(
        2,
        1,
        2,
        vec![block(
            vec![
                runtime(RuntimeFn::ExtLock, vec![ext], vec![]),
                runtime(RuntimeFn::Sleep, vec![nanos], vec![]),
                runtime(RuntimeFn::ExtUnlock, vec![ext], vec![]),
            ],
            Term::Return(vec![nanos]),
        )],
    )
}

/// `once(ext) = ext`: takes the lock and gives it up.
fn once() -> LirFunction {
    let ext = r(0);
    lir(
        1,
        1,
        1,
        vec![block(
            vec![
                runtime(RuntimeFn::ExtLock, vec![ext], vec![]),
                runtime(RuntimeFn::ExtUnlock, vec![ext], vec![]),
            ],
            Term::Return(vec![ext]),
        )],
    )
}

/// `trap_holding(ext)`: takes the lock and traps.
fn trap_holding() -> LirFunction {
    lir(
        1,
        1,
        1,
        vec![block(
            vec![runtime(RuntimeFn::ExtLock, vec![r(0)], vec![])],
            Term::Trap {
                kind: TrapKind::Overflow,
                position: None,
            },
        )],
    )
}

/// Ends the test process if the test hangs, as a lock that is never given
/// up leaves its waiters.
struct Watchdog(#[allow(dead_code)] mpsc::Sender<()>);

fn watchdog() -> Watchdog {
    let (done, waiting) = mpsc::channel::<()>();
    std::thread::spawn(move || {
        if waiting.recv_timeout(Duration::from_secs(60)) == Err(RecvTimeoutError::Timeout) {
            eprintln!("an ext test hung for 60 seconds");
            std::process::abort();
        }
    });
    Watchdog(done)
}

struct Setup {
    image: Image,
    types: Arc<Types>,
    worker: Worker,
}

impl Setup {
    fn new() -> Setup {
        let types = Arc::new(Types::new([]));
        let mut worker = Worker::new();
        worker.set_types(types.clone());
        Setup {
            image: Image::new(&[
                calling(RuntimeFn::ExtNew, 0, 1),
                calling(RuntimeFn::ExtFree, 1, 0),
                turns(),
                hold(),
                once(),
                trap_holding(),
            ]),
            types,
            worker,
        }
    }

    fn fiber(&mut self, func: usize, args: &[u64]) -> Box<Fiber> {
        self.image
            .fiber_returning(func, args, 1, FiberConfig::default())
    }

    /// Runs a function on the setup's worker, outside any scheduler.
    fn resume(&mut self, func: usize, args: &[u64], results: u32) -> Box<Fiber> {
        let mut fiber = self
            .image
            .fiber_returning(func, args, results, FiberConfig::default());
        self.worker.resume(&mut fiber);
        fiber
    }

    fn ext(&mut self) -> u64 {
        let fiber = self.resume(EXT_NEW, &[], 1);
        assert_eq!(fiber.state(), FiberState::Finished);
        fiber.results().unwrap()[0]
    }

    fn free(&mut self, ext: u64) {
        let fiber = self.resume(EXT_FREE, &[ext], 0);
        assert_eq!(fiber.state(), FiberState::Finished);
    }

    fn scheduler(&mut self, workers: usize) -> Scheduler {
        let code = Arc::new(std::mem::take(&mut self.image.code));
        Scheduler::new(
            SchedulerConfig {
                workers,
                slice: Some(Duration::from_millis(1)),
            },
            self.types.clone(),
            code,
        )
    }
}

fn ms(n: u64) -> u64 {
    n * 1_000_000
}

fn kind(fiber: &Fiber) -> TrapKind {
    assert_eq!(fiber.state(), FiberState::Trapped);
    fiber.trap().unwrap().kind
}

#[test]
fn tasks_take_turns_at_the_lock_while_they_suspend_holding_it() {
    let _watchdog = watchdog();
    const TASKS: u64 = 8;
    const EACH: u64 = 500;
    let mut setup = Setup::new();
    let ext = setup.ext();
    let counter = Box::new(AtomicU64::new(0));
    let address = std::ptr::from_ref(&*counter) as u64;
    let fibers = (0..TASKS)
        .map(|_| setup.fiber(TURNS, &[ext, address, EACH]))
        .collect();
    let scheduler = setup.scheduler(4);
    scheduler.spawn_all(fibers);
    for fiber in scheduler.wait() {
        assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    }
    drop(scheduler);
    assert_eq!(counter.load(Ordering::SeqCst), TASKS * EACH);
    setup.free(ext);
}

#[test]
fn a_task_cancelled_while_it_waits_for_the_lock_leaves_the_queue() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let ext = setup.ext();
    let holder = setup.fiber(HOLD, &[ext, ms(100)]);
    let waiter = setup.fiber(ONCE, &[ext]);
    let handle = waiter.cancel_handle();
    let later = setup.fiber(ONCE, &[ext]);
    let scheduler = setup.scheduler(2);
    scheduler.spawn(holder);
    std::thread::sleep(Duration::from_millis(20));
    scheduler.spawn(waiter);
    std::thread::sleep(Duration::from_millis(20));
    handle.cancel();
    scheduler.spawn(later);
    let fibers = scheduler.wait();
    drop(scheduler);
    let mut cancelled = 0;
    for fiber in &fibers {
        match fiber.state() {
            FiberState::Trapped => {
                assert_eq!(kind(fiber), TrapKind::Cancelled);
                cancelled += 1;
            }
            state => assert_eq!(state, FiberState::Finished),
        }
    }
    assert_eq!((fibers.len(), cancelled), (3, 1));
    // The lock is free: a task outside any scheduler takes it at once.
    let fiber = setup.resume(ONCE, &[ext], 1);
    assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    setup.free(ext);
}

#[test]
fn a_task_that_traps_holding_the_lock_gives_it_up() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let ext = setup.ext();
    let fiber = setup.resume(TRAP_HOLDING, &[ext], 1);
    assert_eq!(kind(&fiber), TrapKind::Overflow);
    let fiber = setup.resume(ONCE, &[ext], 1);
    assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    setup.free(ext);
}

#[test]
fn a_task_that_traps_holding_the_lock_hands_it_to_a_waiter() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let ext = setup.ext();
    let holder = setup.fiber(HOLD, &[ext, ms(50)]);
    let handle = holder.cancel_handle();
    let waiter = setup.fiber(ONCE, &[ext]);
    let scheduler = setup.scheduler(2);
    scheduler.spawn(holder);
    std::thread::sleep(Duration::from_millis(10));
    scheduler.spawn(waiter);
    std::thread::sleep(Duration::from_millis(10));
    // The holder stops in its sleep, holding the lock.
    handle.cancel();
    let fibers = scheduler.wait();
    drop(scheduler);
    let states: Vec<_> = fibers.iter().map(|f| f.state()).collect();
    assert!(states.contains(&FiberState::Finished), "{states:?}");
    assert!(states.contains(&FiberState::Trapped), "{states:?}");
    setup.free(ext);
}

#[test]
fn without_a_scheduler_a_lock_that_would_wait_is_unsupported() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let ext = setup.ext();
    let counter = Box::new(AtomicU64::new(0));
    let address = std::ptr::from_ref(&*counter) as u64;
    // A fiber that yields while it holds the lock.
    let mut turns = setup.fiber(TURNS, &[ext, address, 1]);
    let mut worker = Worker::new();
    worker.set_types(setup.types.clone());
    assert_eq!(worker.resume(&mut turns), FiberState::Runnable);
    let fiber = setup.resume(ONCE, &[ext], 1);
    assert_eq!(kind(&fiber), TrapKind::Unsupported);
    assert_eq!(worker.resume(&mut turns), FiberState::Finished);
    setup.free(ext);
}
