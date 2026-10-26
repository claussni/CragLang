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

//! Transactions (Plan §11.7.7): concurrent transfers keep their total and
//! never show a torn state, reads and commits after another write
//! conflict, a block reads its own writes, an inner block that fails
//! keeps the outer writes, and a block that runs alone holds the other
//! writes off and keeps its worker.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::{CountedField, ElementLayout, RuntimeFn, TX_CONFLICT, TX_OK, TypeDescriptor};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::sentinel::StopReason;
use crag_runtime::{FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const TRANSFER: usize = 0;
const CHECK: usize = 1;
const SWAP: usize = 2;
const READ_LATE: usize = 3;
const COMMIT_LATE: usize = 4;
const NESTED: usize = 5;
const OWN_WRITE: usize = 6;
const UNCHANGED: usize = 7;
const ALONE: usize = 8;
const ABANDON: usize = 9;
const BUSY_ALONE: usize = 10;

/// The reruns after which a block runs alone, as the runtime has it.
const ALONE_AFTER: usize = 8;

/// The list type whose elements the values are laid out as: one word.
const INTS: i64 = 1;

/// A list type of boxes.
const BOXES: i64 = 2;

fn konst(dst: VReg, value: i64) -> Inst {
    Inst::Const { dst, value }
}

fn runtime(func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) -> Inst {
    Inst::CallRuntime { func, args, dsts }
}

fn bin(op: BinOp, dst: VReg, a: VReg, b: VReg) -> Inst {
    Inst::Bin { op, dst, a, b }
}

fn load(dst: VReg, addr: VReg) -> Inst {
    Inst::Load {
        dst,
        addr,
        offset: 0,
    }
}

fn ne(dst: VReg, a: VReg, b: VReg) -> Inst {
    Inst::Cmp {
        cond: Cond::Ne,
        dst,
        a,
        b,
    }
}

fn branch(cond: VReg, then: u32, otherwise: u32) -> Term {
    Term::Branch {
        cond,
        then: BlockId(then),
        otherwise: BlockId(otherwise),
    }
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

/// A function of one block.
fn straight(params: u32, vregs: u32, insts: Vec<Inst>, results: Vec<VReg>) -> LirFunction {
    lir(
        params,
        results.len() as u32,
        vregs,
        vec![block(insts, Term::Return(results))],
    )
}

fn begin() -> Inst {
    runtime(RuntimeFn::TxBegin, vec![], vec![])
}

fn yields() -> Inst {
    runtime(RuntimeFn::Yield, vec![], vec![])
}

fn retries(n: usize) -> impl Iterator<Item = Inst> {
    (0..n).map(|_| runtime(RuntimeFn::TxRetry, vec![], vec![]))
}

/// `transfer(a, b, n, out) = conflicts`: moves one from `a` to `b` `n`
/// times, each in an `atomic` block, rerunning on conflicts.
fn transfer() -> LirFunction {
    let (a, b, n, out) = (r(0), r(1), r(2), r(3));
    let (i, one, zero, list, s, flag, va, vb, conflicts) =
        (r(4), r(5), r(6), r(7), r(8), r(9), r(10), r(11), r(12));
    lir(
        4,
        1,
        13,
        vec![
            block(
                vec![
                    konst(i, 0),
                    konst(one, 1),
                    konst(zero, 0),
                    konst(list, INTS),
                    konst(conflicts, 0),
                ],
                Term::Jump(BlockId(1)),
            ),
            block(
                vec![Inst::Cmp {
                    cond: Cond::Ge,
                    dst: flag,
                    a: i,
                    b: n,
                }],
                branch(flag, 7, 2),
            ),
            block(vec![begin()], Term::Jump(BlockId(3))),
            block(
                vec![
                    runtime(RuntimeFn::TxRead, vec![a, out], vec![s]),
                    load(va, out),
                    runtime(RuntimeFn::TxRead, vec![b, out], vec![flag]),
                    load(vb, out),
                    bin(BinOp::Or, s, s, flag),
                    ne(flag, s, zero),
                ],
                branch(flag, 5, 4),
            ),
            block(
                vec![
                    bin(BinOp::Sub, va, va, one),
                    bin(BinOp::Add, vb, vb, one),
                    runtime(RuntimeFn::TxWrite, vec![a, list, va, zero], vec![]),
                    runtime(RuntimeFn::TxWrite, vec![b, list, vb, zero], vec![]),
                    runtime(RuntimeFn::TxCommit, vec![], vec![s]),
                    ne(flag, s, zero),
                ],
                branch(flag, 5, 6),
            ),
            block(
                vec![
                    runtime(RuntimeFn::TxRetry, vec![], vec![]),
                    bin(BinOp::Add, conflicts, conflicts, one),
                ],
                Term::Jump(BlockId(3)),
            ),
            block(
                vec![bin(BinOp::Add, i, i, one), Inst::Poll],
                Term::Jump(BlockId(1)),
            ),
            block(vec![], Term::Return(vec![conflicts])),
        ],
    )
}

/// `check(a, b, n, total, out) = torn`: reads `a` and `b` in an `atomic`
/// block `n` times and counts the sums that are not `total`.
fn check() -> LirFunction {
    let (a, b, n, total, out) = (r(0), r(1), r(2), r(3), r(4));
    let (i, one, zero, s, flag, va, vb, torn) = (r(5), r(6), r(7), r(8), r(9), r(10), r(11), r(12));
    lir(
        5,
        1,
        13,
        vec![
            block(
                vec![konst(i, 0), konst(one, 1), konst(zero, 0), konst(torn, 0)],
                Term::Jump(BlockId(1)),
            ),
            block(
                vec![Inst::Cmp {
                    cond: Cond::Ge,
                    dst: flag,
                    a: i,
                    b: n,
                }],
                branch(flag, 7, 2),
            ),
            block(vec![begin()], Term::Jump(BlockId(3))),
            block(
                vec![
                    runtime(RuntimeFn::TxRead, vec![a, out], vec![s]),
                    load(va, out),
                    runtime(RuntimeFn::TxRead, vec![b, out], vec![flag]),
                    load(vb, out),
                    bin(BinOp::Or, s, s, flag),
                    ne(flag, s, zero),
                ],
                branch(flag, 5, 4),
            ),
            block(
                vec![
                    runtime(RuntimeFn::TxCommit, vec![], vec![s]),
                    bin(BinOp::Add, va, va, vb),
                    ne(flag, va, total),
                    bin(BinOp::Add, torn, torn, flag),
                ],
                Term::Jump(BlockId(6)),
            ),
            block(
                vec![runtime(RuntimeFn::TxRetry, vec![], vec![])],
                Term::Jump(BlockId(3)),
            ),
            block(
                vec![bin(BinOp::Add, i, i, one), Inst::Poll],
                Term::Jump(BlockId(1)),
            ),
            block(vec![], Term::Return(vec![torn])),
        ],
    )
}

/// `swap(cell, list, w0, w1) = old`.
fn swap() -> LirFunction {
    let dsts = vec![r(4), r(5)];
    straight(
        4,
        6,
        vec![runtime(
            RuntimeFn::RefSwap,
            vec![r(0), r(1), r(2), r(3)],
            dsts.clone(),
        )],
        dsts,
    )
}

/// `read_late(a, out) = status`: begins, yields, then reads `a`.
fn read_late() -> LirFunction {
    let (a, out, s) = (r(0), r(1), r(2));
    straight(
        2,
        3,
        vec![
            begin(),
            yields(),
            runtime(RuntimeFn::TxRead, vec![a, out], vec![s]),
            runtime(RuntimeFn::TxAbort, vec![], vec![]),
        ],
        vec![s],
    )
}

/// `commit_late(a, b, out) = (read, commit)`: reads `a`, yields, writes
/// 9 to `b` and commits.
fn commit_late() -> LirFunction {
    let (a, b, out, s, c, list, nine, zero) = (r(0), r(1), r(2), r(3), r(4), r(5), r(6), r(7));
    straight(
        3,
        8,
        vec![
            konst(list, INTS),
            konst(nine, 9),
            konst(zero, 0),
            begin(),
            runtime(RuntimeFn::TxRead, vec![a, out], vec![s]),
            yields(),
            runtime(RuntimeFn::TxWrite, vec![b, list, nine, zero], vec![]),
            runtime(RuntimeFn::TxCommit, vec![], vec![c]),
        ],
        vec![s, c],
    )
}

/// `nested(a, b, x, y) = status`: writes `x` to `a`, then in an inner
/// block `y` to `b`, which fails, and commits.
fn nested() -> LirFunction {
    let (a, b, x, y, s, list, zero) = (r(0), r(1), r(2), r(3), r(4), r(5), r(6));
    straight(
        4,
        7,
        vec![
            konst(list, BOXES),
            konst(zero, 0),
            begin(),
            runtime(RuntimeFn::TxWrite, vec![a, list, x, zero], vec![]),
            begin(),
            runtime(RuntimeFn::TxWrite, vec![b, list, y, zero], vec![]),
            runtime(RuntimeFn::TxAbort, vec![], vec![]),
            runtime(RuntimeFn::TxCommit, vec![], vec![s]),
        ],
        vec![s],
    )
}

/// `own_write(a, out) = (read, commit)`: writes 5 to `a` and reads it.
fn own_write() -> LirFunction {
    let (a, out, v, c, list, five, zero, s) = (r(0), r(1), r(2), r(3), r(4), r(5), r(6), r(7));
    straight(
        2,
        8,
        vec![
            konst(list, INTS),
            konst(five, 5),
            konst(zero, 0),
            begin(),
            runtime(RuntimeFn::TxWrite, vec![a, list, five, zero], vec![]),
            runtime(RuntimeFn::TxRead, vec![a, out], vec![s]),
            load(v, out),
            runtime(RuntimeFn::TxCommit, vec![], vec![c]),
        ],
        vec![v, c],
    )
}

/// `unchanged(a, out) = commit`: writes back what it read.
fn unchanged() -> LirFunction {
    let (a, out, v, c, list, zero, s) = (r(0), r(1), r(2), r(3), r(4), r(5), r(6));
    straight(
        2,
        7,
        vec![
            konst(list, INTS),
            konst(zero, 0),
            begin(),
            runtime(RuntimeFn::TxRead, vec![a, out], vec![s]),
            load(v, out),
            runtime(RuntimeFn::TxWrite, vec![a, list, v, zero], vec![]),
            runtime(RuntimeFn::TxCommit, vec![], vec![c]),
        ],
        vec![c],
    )
}

/// `alone(a) = commit`: reruns until it runs alone, yields, writes 1 to
/// `a` and commits.
fn alone() -> LirFunction {
    let (a, c, list, one, zero) = (r(0), r(1), r(2), r(3), r(4));
    let mut insts = vec![konst(list, INTS), konst(one, 1), konst(zero, 0), begin()];
    insts.extend(retries(ALONE_AFTER));
    insts.extend([
        yields(),
        runtime(RuntimeFn::TxWrite, vec![a, list, one, zero], vec![]),
        runtime(RuntimeFn::TxCommit, vec![], vec![c]),
    ]);
    straight(1, 5, insts, vec![c])
}

/// `abandon(a, x)`: runs alone, writes `x` to `a` and returns without
/// ending the block.
fn abandon() -> LirFunction {
    let (a, x, list, zero) = (r(0), r(1), r(2), r(3));
    let mut insts = vec![konst(list, BOXES), konst(zero, 0), begin()];
    insts.extend(retries(ALONE_AFTER));
    insts.push(runtime(RuntimeFn::TxWrite, vec![a, list, x, zero], vec![]));
    straight(2, 4, insts, vec![zero])
}

/// `busy_alone(n) = commit`: runs alone, yields, polls `n` times and
/// commits.
fn busy_alone() -> LirFunction {
    let (n, i, one, flag, c) = (r(0), r(1), r(2), r(3), r(4));
    let mut first = vec![konst(i, 0), konst(one, 1), begin()];
    first.extend(retries(ALONE_AFTER));
    first.push(yields());
    lir(
        1,
        1,
        5,
        vec![
            block(first, Term::Jump(BlockId(1))),
            block(
                vec![Inst::Cmp {
                    cond: Cond::Ge,
                    dst: flag,
                    a: i,
                    b: n,
                }],
                branch(flag, 3, 2),
            ),
            block(
                vec![bin(BinOp::Add, i, i, one), Inst::Poll],
                Term::Jump(BlockId(1)),
            ),
            block(
                vec![runtime(RuntimeFn::TxCommit, vec![], vec![c])],
                Term::Return(vec![c]),
            ),
        ],
    )
}

fn types() -> Arc<Types> {
    let list = |counted| TypeDescriptor::List {
        element: ElementLayout { words: 1, counted },
    };
    Arc::new(Types::new([
        (INTS as u32, list(vec![])),
        (BOXES as u32, list(vec![CountedField::Box(0)])),
    ]))
}

/// The clock and its bit for a block that runs alone are the process's.
static SERIAL: Mutex<()> = Mutex::new(());

/// A test's hold on the process, which ends it if the test hangs: a test
/// that fails while a block runs alone leaves every other write waiting.
struct Serial {
    _guard: MutexGuard<'static, ()>,
    _done: mpsc::Sender<()>,
}

fn serial() -> Serial {
    let guard = SERIAL.lock().unwrap_or_else(|e| e.into_inner());
    let (done, waiting) = mpsc::channel::<()>();
    std::thread::spawn(move || {
        if waiting.recv_timeout(Duration::from_secs(60)) == Err(RecvTimeoutError::Timeout) {
            eprintln!("an STM test hung for 60 seconds");
            std::process::abort();
        }
    });
    Serial {
        _guard: guard,
        _done: done,
    }
}

struct Setup {
    image: Image,
    types: Arc<Types>,
    worker: Worker,
}

impl Setup {
    fn new() -> Setup {
        let types = types();
        let mut worker = Worker::new();
        worker.set_types(types.clone());
        Setup {
            image: Image::new(&[
                transfer(),
                check(),
                swap(),
                read_late(),
                commit_late(),
                nested(),
                own_write(),
                unchanged(),
                alone(),
                abandon(),
                busy_alone(),
            ]),
            types,
            worker,
        }
    }

    fn fiber(&mut self, func: usize, args: &[u64], results: u32) -> Box<crag_runtime::Fiber> {
        self.image
            .fiber_returning(func, args, results, FiberConfig::default())
    }

    /// Runs a function to its end on the setup's worker.
    fn call(&mut self, func: usize, args: &[u64], results: u32) -> [u64; 2] {
        let mut fiber = self.fiber(func, args, results);
        assert_eq!(self.worker.resume(&mut fiber), FiberState::Finished);
        fiber.results().unwrap()
    }
}

/// A ref cell holding `value`, at version 0.
fn cell(value: u64) -> Box<[AtomicU64; 3]> {
    Box::new([AtomicU64::new(0), AtomicU64::new(value), AtomicU64::new(0)])
}

fn addr<T>(x: &T) -> u64 {
    std::ptr::from_ref(x) as u64
}

fn value(cell: &[AtomicU64; 3]) -> u64 {
    cell[1].load(Ordering::SeqCst)
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

    /// A reference for the test to give away.
    fn reference(&self) -> u64 {
        self.count.fetch_add(1, Ordering::SeqCst);
        addr(self)
    }
}

#[test]
fn transfers_keep_their_total_and_show_no_torn_state() {
    let _serial = serial();
    const START: u64 = 1_000_000;
    let mut setup = Setup::new();
    let (a, b) = (cell(START), cell(0));
    let mut outs = [[0u64; 2]; 8];
    let mut fibers = Vec::new();
    for (k, out) in outs.iter_mut().enumerate() {
        let out = out.as_mut_ptr() as u64;
        fibers.push(if k < 6 {
            setup.fiber(TRANSFER, &[addr(&*a), addr(&*b), 2_000, out], 1)
        } else {
            setup.fiber(CHECK, &[addr(&*a), addr(&*b), 2_000, START, out], 1)
        });
    }
    let code = Arc::new(std::mem::take(&mut setup.image.code));
    let scheduler = Scheduler::new(
        SchedulerConfig {
            workers: 4,
            slice: Some(Duration::from_millis(1)),
        },
        setup.types.clone(),
        code,
    );
    let checkers: Vec<*const crag_runtime::Fiber> =
        fibers[6..].iter().map(|f| &raw const **f).collect();
    scheduler.spawn_all(fibers);
    for fiber in scheduler.wait() {
        assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
        if checkers.contains(&(&raw const *fiber)) {
            assert_eq!(fiber.results().unwrap()[0], 0, "torn reads");
        }
    }
    assert_eq!(value(&a), START - 12_000);
    assert_eq!(value(&b), 12_000);
}

#[test]
fn a_read_after_another_write_conflicts() {
    let _serial = serial();
    let mut setup = Setup::new();
    let a = cell(1);
    let mut out = [0u64; 2];
    let mut tx = setup.fiber(READ_LATE, &[addr(&*a), out.as_mut_ptr() as u64], 1);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Runnable);
    setup.call(SWAP, &[addr(&*a), INTS as u64, 2, 0], 2);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Finished);
    assert_eq!(tx.results().unwrap()[0], TX_CONFLICT);
}

#[test]
fn a_commit_after_another_write_conflicts() {
    let _serial = serial();
    let mut setup = Setup::new();
    let (a, b) = (cell(1), cell(0));
    let mut out = [0u64; 2];
    let args = [addr(&*a), addr(&*b), out.as_mut_ptr() as u64];
    let mut tx = setup.fiber(COMMIT_LATE, &args, 2);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Runnable);
    setup.call(SWAP, &[addr(&*a), INTS as u64, 2, 0], 2);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Finished);
    assert_eq!(tx.results().unwrap(), [TX_OK, TX_CONFLICT]);
    assert_eq!(value(&b), 0);
    // Without the other write it commits.
    let mut tx = setup.fiber(COMMIT_LATE, &args, 2);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Runnable);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Finished);
    assert_eq!(tx.results().unwrap(), [TX_OK, TX_OK]);
    assert_eq!(value(&b), 9);
}

#[test]
fn an_inner_block_that_fails_keeps_the_outer_writes() {
    let _serial = serial();
    let [old_a, old_b, x, y] = [(); 4].map(|_| FakeBox::new());
    let mut setup = Setup::new();
    let (a, b) = (cell(addr(&*old_a)), cell(addr(&*old_b)));
    let args = [addr(&*a), addr(&*b), x.reference(), y.reference()];
    assert_eq!(setup.call(NESTED, &args, 1)[0], TX_OK);
    assert_eq!(value(&a), addr(&*x));
    assert_eq!(value(&b), addr(&*old_b));
    // `a`'s old value was released, the cell holds `x`, and `y` went
    // with the inner block.
    assert_eq!(
        [old_a.count(), old_b.count(), x.count(), y.count()],
        [999, 1_000, 1_001, 1_000]
    );
}

#[test]
fn a_block_reads_its_own_writes() {
    let _serial = serial();
    let mut setup = Setup::new();
    let a = cell(1);
    let mut out = [0u64; 2];
    let [v, c] = setup.call(OWN_WRITE, &[addr(&*a), out.as_mut_ptr() as u64], 2);
    assert_eq!([v, c], [5, TX_OK]);
    assert_eq!(value(&a), 5);
}

#[test]
fn an_unchanged_value_is_not_written() {
    let _serial = serial();
    let mut setup = Setup::new();
    let a = cell(3);
    let mut out = [0u64; 2];
    assert_eq!(
        setup.call(UNCHANGED, &[addr(&*a), out.as_mut_ptr() as u64], 1)[0],
        TX_OK
    );
    assert_eq!(a[0].load(Ordering::SeqCst), 0);
}

/// A fiber handed to another thread before it runs.
struct Moved(Box<crag_runtime::Fiber>);

// SAFETY: the fiber has not started, and only the thread it goes to
// runs it.
unsafe impl Send for Moved {}

impl Moved {
    /// The fiber, moving the whole wrapper into the closure that calls it.
    fn take(self) -> Box<crag_runtime::Fiber> {
        self.0
    }
}

#[test]
fn a_block_that_runs_alone_holds_other_writes_off() {
    let _serial = serial();
    let mut setup = Setup::new();
    let a = cell(0);
    let mut tx = setup.fiber(ALONE, &[addr(&*a)], 1);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Runnable);
    // A swap on another thread waits for the block.
    let swap = Moved(setup.fiber(SWAP, &[addr(&*a), INTS as u64, 2, 0], 2));
    let types = setup.types.clone();
    let done = Arc::new(AtomicBool::new(false));
    let swapped = {
        let done = done.clone();
        std::thread::spawn(move || {
            let mut swap = swap.take();
            let mut worker = Worker::new();
            worker.set_types(types);
            assert_eq!(worker.resume(&mut swap), FiberState::Finished);
            done.store(true, Ordering::SeqCst);
            swap.results().unwrap()[0]
        })
    };
    std::thread::sleep(Duration::from_millis(50));
    assert!(!done.load(Ordering::SeqCst));
    assert_eq!(value(&a), 0);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Finished);
    assert_eq!(tx.results().unwrap()[0], TX_OK);
    assert_eq!(swapped.join().unwrap(), 1);
    assert_eq!(value(&a), 2);
}

#[test]
fn a_task_that_stops_in_a_block_gives_its_writes_up() {
    let _serial = serial();
    let x = FakeBox::new();
    let mut setup = Setup::new();
    let a = cell(0);
    setup.call(ABANDON, &[addr(&*a), x.reference()], 1);
    assert_eq!(x.count(), 1_000);
    assert_eq!(value(&a), 0);
    // It runs alone no more: this write would wait forever.
    setup.call(SWAP, &[addr(&*a), INTS as u64, 2, 0], 2);
    assert_eq!(value(&a), 2);
}

#[test]
fn a_block_that_runs_alone_is_not_preempted() {
    let _serial = serial();
    let mut setup = Setup::new();
    let mut tx = setup.fiber(BUSY_ALONE, &[10_000], 1);
    assert_eq!(setup.worker.resume(&mut tx), FiberState::Runnable);
    tx.stop_handle().request_stop(StopReason::Preempt);
    // Run to the end before checking, so that a failure leaves no block
    // running alone.
    let mut resumes = 1;
    while setup.worker.resume(&mut tx) != FiberState::Finished {
        resumes += 1;
    }
    assert_eq!(resumes, 1);
    assert_eq!(tx.results().unwrap()[0], TX_OK);
}
