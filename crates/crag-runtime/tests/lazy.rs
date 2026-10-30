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

//! Lazy cells (Plan §11.7.11): the first read computes the value while
//! the others wait; a trap in the computation traps every read, a
//! cancelled one passes to a waiting read, and a computation that reads
//! its own value traps with `Cycle`.

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::{
    CountedField, ElementLayout, LAZY_DONE, LAZY_RUN, LAZY_TRAPPED, RuntimeFn, TrapKind,
    TypeDescriptor,
};
use crag_codegen::{Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::{Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const LAZY_NEW: usize = 0;
const LAZY_FREE: usize = 1;
const READER: usize = 2;
const TRAPPER: usize = 3;
const SELF_READER: usize = 4;

/// The list type whose elements the values are laid out as: one word.
const INTS: u64 = 1;

/// A list type of boxes.
const BOXES: u64 = 2;

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
        natives: Vec::new(),
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

/// The first block of a reader: reads the cell, and goes on to block 1
/// if it must compute the value, else to block 2. Registers 0 and 1 are
/// the cell and the place for the value, 4 and 5 the status and a flag.
fn read_first() -> Block {
    let (lazy, out, status, flag, run) = (r(0), r(1), r(4), r(5), r(6));
    block(
        vec![
            runtime(RuntimeFn::LazyGet, vec![lazy, out], vec![status]),
            konst(run, LAZY_RUN as i64),
            Inst::Cmp {
                cond: Cond::Eq,
                dst: flag,
                a: status,
                b: run,
            },
        ],
        Term::Branch {
            cond: flag,
            then: BlockId(1),
            otherwise: BlockId(2),
        },
    )
}

/// `reader(lazy, out, value, nanos) = status`: reads the cell; if it must
/// compute the value, yields, sleeps `nanos` and stores `value`.
fn reader() -> LirFunction {
    let (lazy, value, nanos, status, zero) = (r(0), r(2), r(3), r(4), r(7));
    lir(
        4,
        1,
        8,
        vec![
            read_first(),
            block(
                vec![
                    runtime(RuntimeFn::Yield, vec![], vec![]),
                    runtime(RuntimeFn::Sleep, vec![nanos], vec![]),
                    konst(zero, 0),
                    runtime(RuntimeFn::LazySet, vec![lazy, value, zero], vec![]),
                ],
                Term::Jump(BlockId(2)),
            ),
            block(vec![], Term::Return(vec![status])),
        ],
    )
}

/// `trapper(lazy, out, _, nanos) = status`: reads the cell; if it must
/// compute the value, sleeps `nanos` and traps.
fn trapper() -> LirFunction {
    let (nanos, status) = (r(3), r(4));
    lir(
        4,
        1,
        8,
        vec![
            read_first(),
            block(
                vec![runtime(RuntimeFn::Sleep, vec![nanos], vec![])],
                Term::Trap {
                    kind: TrapKind::Overflow,
                    position: None,
                },
            ),
            block(vec![], Term::Return(vec![status])),
        ],
    )
}

/// `self_reader(lazy, out, _, _) = status`: computing the value, reads it
/// again, and traps with the kind that read gives.
fn self_reader() -> LirFunction {
    let (lazy, out, status, again) = (r(0), r(1), r(4), r(7));
    lir(
        4,
        1,
        8,
        vec![
            read_first(),
            block(
                vec![runtime(RuntimeFn::LazyGet, vec![lazy, out], vec![again])],
                Term::Trap {
                    kind: TrapKind::Cycle,
                    position: None,
                },
            ),
            block(vec![], Term::Return(vec![status])),
        ],
    )
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

/// Ends the test process if the test hangs, as reads that are never
/// woken would.
struct Watchdog(#[allow(dead_code)] mpsc::Sender<()>);

fn watchdog() -> Watchdog {
    let (done, waiting) = mpsc::channel::<()>();
    std::thread::spawn(move || {
        if waiting.recv_timeout(Duration::from_secs(60)) == Err(RecvTimeoutError::Timeout) {
            eprintln!("a lazy test hung for 60 seconds");
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

/// Where a read writes the value.
type Out = Box<[u64; 2]>;

impl Setup {
    fn new() -> Setup {
        let types = types();
        let mut worker = Worker::new();
        worker.set_types(types.clone());
        Setup {
            image: Image::new(&[
                calling(RuntimeFn::LazyNew, 1, 1),
                calling(RuntimeFn::LazyFree, 1, 0),
                reader(),
                trapper(),
                self_reader(),
            ]),
            types,
            worker,
        }
    }

    fn fiber(
        &mut self,
        func: usize,
        lazy: u64,
        out: &mut Out,
        value: u64,
        nanos: u64,
    ) -> Box<Fiber> {
        let args = [lazy, out.as_mut_ptr() as u64, value, nanos];
        self.image
            .fiber_returning(func, &args, 1, FiberConfig::default())
    }

    /// Runs a function on the setup's worker, outside any scheduler, past
    /// its yields.
    fn resume(&mut self, mut fiber: Box<Fiber>) -> Box<Fiber> {
        while self.worker.resume(&mut fiber) == FiberState::Runnable {}
        fiber
    }

    fn lazy(&mut self, list: u64) -> u64 {
        let fiber = self
            .image
            .fiber_returning(LAZY_NEW, &[list], 1, FiberConfig::default());
        let fiber = self.resume(fiber);
        fiber.results().unwrap()[0]
    }

    fn free(&mut self, lazy: u64) {
        let fiber = self
            .image
            .fiber_returning(LAZY_FREE, &[lazy], 0, FiberConfig::default());
        assert_eq!(self.resume(fiber).state(), FiberState::Finished);
    }

    /// A read on the setup's worker: its status and what it wrote.
    fn read(&mut self, lazy: u64) -> (u64, u64) {
        let mut out: Out = Box::new([0; 2]);
        let fiber = self.fiber(READER, lazy, &mut out, 0, 0);
        let fiber = self.resume(fiber);
        assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
        (fiber.results().unwrap()[0], out[0])
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

fn pause(n: u64) {
    std::thread::sleep(Duration::from_millis(n));
}

/// Runs the fibers until all have stopped, and gives them back in the
/// order they were passed.
#[allow(clippy::vec_box)]
fn in_order(stopped: Vec<Box<Fiber>>, order: &[*const Fiber]) -> Vec<Box<Fiber>> {
    let mut stopped = stopped;
    order
        .iter()
        .map(|&p| {
            let i = stopped
                .iter()
                .position(|f| std::ptr::eq(&raw const **f, p))
                .expect("stopped");
            stopped.swap_remove(i)
        })
        .collect()
}

fn status(fiber: &Fiber) -> u64 {
    assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    fiber.results().unwrap()[0]
}

#[test]
fn the_first_read_computes_the_value_and_the_others_wait_for_it() {
    let _watchdog = watchdog();
    const READERS: u64 = 8;
    let mut setup = Setup::new();
    let lazy = setup.lazy(INTS);
    let mut outs: Vec<Out> = (0..READERS).map(|_| Box::new([0; 2])).collect();
    let fibers: Vec<_> = outs
        .iter_mut()
        .enumerate()
        .map(|(i, out)| setup.fiber(READER, lazy, out, 100 + i as u64, ms(20)))
        .collect();
    let scheduler = setup.scheduler(4);
    scheduler.spawn_all(fibers);
    let fibers = scheduler.wait();
    drop(scheduler);
    let statuses: Vec<u64> = fibers.iter().map(|f| status(f)).collect();
    assert_eq!(statuses.iter().filter(|&&s| s == LAZY_RUN).count(), 1);
    assert_eq!(statuses.iter().filter(|&&s| s == LAZY_DONE).count(), 7);
    // Every read that waited got the one value, and so does a later one.
    let (_, value) = setup.read(lazy);
    assert!((100..100 + READERS).contains(&value));
    let waited = outs.iter().filter(|o| o[0] == value).count();
    assert_eq!(waited, 7);
    assert_eq!(setup.read(lazy), (LAZY_DONE, value));
    setup.free(lazy);
}

#[test]
fn a_trap_in_the_computation_traps_every_read() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let lazy = setup.lazy(INTS);
    let (mut a, mut b) = (Box::new([0; 2]), Box::new([0; 2]));
    let computing = setup.fiber(TRAPPER, lazy, &mut a, 0, ms(30));
    let waiting = setup.fiber(READER, lazy, &mut b, 7, 0);
    let order = [&raw const *computing, &raw const *waiting];
    let scheduler = setup.scheduler(2);
    scheduler.spawn(computing);
    pause(10);
    scheduler.spawn(waiting);
    let fibers = in_order(scheduler.wait(), &order);
    drop(scheduler);
    assert_eq!(fibers[0].trap().unwrap().kind, TrapKind::Overflow);
    assert_eq!(status(&fibers[1]), LAZY_TRAPPED);
    assert_eq!(b[0], TrapKind::Overflow as u64);
    assert_eq!(setup.read(lazy), (LAZY_TRAPPED, TrapKind::Overflow as u64));
    setup.free(lazy);
}

#[test]
fn a_cancelled_computation_passes_to_a_waiting_read() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let lazy = setup.lazy(INTS);
    let (mut a, mut b) = (Box::new([0; 2]), Box::new([0; 2]));
    let computing = setup.fiber(READER, lazy, &mut a, 1, ms(10_000));
    let handle = computing.cancel_handle();
    let waiting = setup.fiber(READER, lazy, &mut b, 2, 0);
    let order = [&raw const *computing, &raw const *waiting];
    let scheduler = setup.scheduler(2);
    scheduler.spawn(computing);
    pause(10);
    scheduler.spawn(waiting);
    pause(10);
    handle.cancel();
    let fibers = in_order(scheduler.wait(), &order);
    drop(scheduler);
    assert_eq!(fibers[0].trap().unwrap().kind, TrapKind::Cancelled);
    assert_eq!(status(&fibers[1]), LAZY_RUN);
    assert_eq!(setup.read(lazy), (LAZY_DONE, 2));
    setup.free(lazy);
}

#[test]
fn a_cancelled_computation_with_no_one_waiting_leaves_the_cell_unstarted() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let lazy = setup.lazy(INTS);
    let mut a = Box::new([0; 2]);
    let computing = setup.fiber(READER, lazy, &mut a, 1, ms(10_000));
    let handle = computing.cancel_handle();
    let scheduler = setup.scheduler(1);
    scheduler.spawn(computing);
    pause(10);
    handle.cancel();
    let fibers = scheduler.wait();
    drop(scheduler);
    assert_eq!(fibers[0].trap().unwrap().kind, TrapKind::Cancelled);
    // The next read computes it.
    assert_eq!(setup.read(lazy), (LAZY_RUN, 0));
    assert_eq!(setup.read(lazy), (LAZY_DONE, 0));
    setup.free(lazy);
}

#[test]
fn a_computation_that_reads_its_own_value_traps_with_cycle() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let lazy = setup.lazy(INTS);
    let mut a = Box::new([0; 2]);
    let fiber = setup.fiber(SELF_READER, lazy, &mut a, 0, 0);
    let fiber = setup.resume(fiber);
    assert_eq!(fiber.trap().unwrap().kind, TrapKind::Cycle);
    assert_eq!(a[0], TrapKind::Cycle as u64);
    assert_eq!(setup.read(lazy), (LAZY_TRAPPED, TrapKind::Cycle as u64));
    setup.free(lazy);
}

#[test]
fn reads_get_references_of_their_own_and_the_cell_releases_its() {
    let _watchdog = watchdog();
    let x = Box::new([AtomicU64::new(1_000), AtomicU64::new(0)]);
    let address = std::ptr::from_ref(&*x) as u64;
    let mut setup = Setup::new();
    let lazy = setup.lazy(BOXES);
    // The computing read gives its reference to the cell.
    x[0].fetch_add(1, Ordering::SeqCst);
    let mut out = Box::new([0; 2]);
    let fiber = setup.fiber(READER, lazy, &mut out, address, 0);
    assert_eq!(status(&setup.resume(fiber)), LAZY_RUN);
    assert_eq!(x[0].load(Ordering::SeqCst), 1_001);
    let fiber = setup.fiber(READER, lazy, &mut out, 0, 0);
    assert_eq!(status(&setup.resume(fiber)), LAZY_DONE);
    assert_eq!((out[0], x[0].load(Ordering::SeqCst)), (address, 1_002));
    setup.free(lazy);
    assert_eq!(x[0].load(Ordering::SeqCst), 1_001);
}

#[test]
fn without_a_scheduler_a_read_that_would_wait_is_unsupported() {
    let _watchdog = watchdog();
    let mut setup = Setup::new();
    let lazy = setup.lazy(INTS);
    let (mut a, mut b) = (Box::new([0; 2]), Box::new([0; 2]));
    // A read that computes the value and yields first.
    let mut computing = setup.fiber(READER, lazy, &mut a, 5, 0);
    let mut worker = Worker::new();
    worker.set_types(setup.types.clone());
    assert_eq!(worker.resume(&mut computing), FiberState::Runnable);
    let fiber = setup.fiber(READER, lazy, &mut b, 0, 0);
    let fiber = setup.resume(fiber);
    assert_eq!(fiber.trap().unwrap().kind, TrapKind::Unsupported);
    assert_eq!(worker.resume(&mut computing), FiberState::Finished);
    assert_eq!(setup.read(lazy), (LAZY_DONE, 5));
    setup.free(lazy);
}
