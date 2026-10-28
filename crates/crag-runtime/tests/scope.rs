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

//! Scopes and cancellation (Plan §11.7.3, §11.7.4): tasks that a parent
//! starts and takes back, limits, cancelling the rest, traps that cancel
//! their siblings, and cancelled tasks that stop whether they wait or
//! compute.

use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::sync::Arc;
use std::time::{Duration, Instant};

mod common;

use common::{Image, r};
use crag_abi::{
    FuncId, RuntimeFn, SCOPE_DONE, START_EXEMPT, TASK_CANCELLED, TASK_RETURNED, TASK_TRAPPED,
    TrapKind,
};
use crag_codegen::{BinOp, Block, BlockId, CallTarget, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::{Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const SLEEPER: usize = 0;
const SPINNER: usize = 1;
const TRAPPER: usize = 2;
const PARENT: usize = 3;
const BODY: usize = 4;
const GUARDED: usize = 5;
const READER: usize = 6;

/// A parent's policy: cancel the rest once it has taken a task.
const CANCEL_AFTER_FIRST: u64 = 1;
/// A parent's policy: start one task, exempt from the limit, with the
/// scope as its environment, as a group's body is started.
const AS_BODY: u64 = 2;

fn konst(dst: VReg, value: i64) -> Inst {
    Inst::Const { dst, value }
}

fn bin(op: BinOp, dst: VReg, a: VReg, b: VReg) -> Inst {
    Inst::Bin { op, dst, a, b }
}

fn runtime(func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) -> Inst {
    Inst::CallRuntime { func, args, dsts }
}

fn block(insts: Vec<Inst>, term: Term) -> Block {
    Block { insts, term }
}

fn function(params: u32, vregs: u32, blocks: Vec<Block>) -> LirFunction {
    LirFunction {
        params,
        returns: 1,
        vregs,
        tracked: vec![],
        blocks,
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// `sleeper(ms) = ms`, after sleeping that many milliseconds.
fn sleeper() -> LirFunction {
    function(
        1,
        3,
        vec![block(
            vec![
                konst(r(1), 1_000_000),
                bin(BinOp::Mul, r(2), r(0), r(1)),
                runtime(RuntimeFn::Sleep, vec![r(2)], vec![]),
            ],
            Term::Return(vec![r(0)]),
        )],
    )
}

/// `spinner(_)`: computes forever, passing a check on each round.
fn spinner() -> LirFunction {
    function(
        1,
        1,
        vec![
            block(vec![], Term::Jump(BlockId(1))),
            block(vec![Inst::Poll], Term::Jump(BlockId(1))),
        ],
    )
}

/// `trapper(ms)`: traps with `Hole` after sleeping.
fn trapper() -> LirFunction {
    function(
        1,
        3,
        vec![block(
            vec![
                konst(r(1), 1_000_000),
                bin(BinOp::Mul, r(2), r(0), r(1)),
                runtime(RuntimeFn::Sleep, vec![r(2)], vec![]),
            ],
            Term::Trap {
                kind: TrapKind::Hole,
                position: Some(42),
            },
        )],
    )
}

/// `parent(limit, code, n, inputs, out, policy) = given`: a scope with
/// `limit` whose tasks run `code` on each of the `n` words at `inputs`,
/// then takes every task, writing its index, status and first result word
/// to `out`, three words each, and ends the scope. Gives how many tasks
/// it took.
fn parent() -> LirFunction {
    let (limit, code, n, inputs, out, policy) = (r(0), r(1), r(2), r(3), r(4), r(5));
    let (scope, i, one, flag, eight, flags, index, status, done) =
        (r(6), r(7), r(8), r(9), r(10), r(11), r(12), r(13), r(14));
    let (w0, w1, given, addr, words, tmp, body, env) =
        (r(15), r(16), r(17), r(18), r(19), r(20), r(21), r(22));
    function(
        6,
        23,
        vec![
            // 0: the scope, and constants.
            block(
                vec![
                    konst(one, 1),
                    konst(eight, 8),
                    konst(done, SCOPE_DONE as i64),
                    konst(words, 24),
                    konst(i, 0),
                    konst(given, 0),
                    konst(tmp, AS_BODY as i64),
                    bin(BinOp::And, body, policy, tmp),
                    runtime(RuntimeFn::ScopeNew, vec![limit], vec![scope]),
                ],
                Term::Jump(BlockId(1)),
            ),
            // 1: start while i < n.
            block(
                vec![Inst::Cmp {
                    cond: Cond::Lt,
                    dst: flag,
                    a: i,
                    b: n,
                }],
                Term::Branch {
                    cond: flag,
                    then: BlockId(2),
                    otherwise: BlockId(3),
                },
            ),
            // 2: start a task on inputs[i], or the body on the scope.
            block(
                vec![
                    bin(BinOp::Mul, tmp, i, eight),
                    bin(BinOp::Add, addr, inputs, tmp),
                    Inst::Load {
                        dst: env,
                        addr,
                        offset: 0,
                    },
                    Inst::Select {
                        dst: env,
                        cond: body,
                        a: scope,
                        b: env,
                    },
                    konst(flags, 1 | START_EXEMPT as i64),
                    Inst::Select {
                        dst: flags,
                        cond: body,
                        a: flags,
                        b: one,
                    },
                    runtime(
                        RuntimeFn::ScopeStart,
                        vec![scope, code, env, flags],
                        vec![tmp],
                    ),
                    bin(BinOp::Add, i, i, one),
                    Inst::Poll,
                ],
                Term::Jump(BlockId(1)),
            ),
            // 3: take the next task.
            block(
                vec![
                    runtime(RuntimeFn::ScopeNext, vec![scope], vec![index, status]),
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: flag,
                        a: index,
                        b: done,
                    },
                ],
                Term::Branch {
                    cond: flag,
                    then: BlockId(7),
                    otherwise: BlockId(4),
                },
            ),
            // 4: record it.
            block(
                vec![
                    bin(BinOp::Mul, tmp, given, words),
                    bin(BinOp::Add, addr, out, tmp),
                    Inst::Store {
                        src: index,
                        addr,
                        offset: 0,
                    },
                    Inst::Store {
                        src: status,
                        addr,
                        offset: 8,
                    },
                    bin(BinOp::Add, given, given, one),
                    konst(tmp, TASK_RETURNED as i64),
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: flag,
                        a: status,
                        b: tmp,
                    },
                ],
                Term::Branch {
                    cond: flag,
                    then: BlockId(5),
                    otherwise: BlockId(6),
                },
            ),
            // 5: its result.
            block(
                vec![
                    runtime(RuntimeFn::ScopeResult, vec![scope, index], vec![w0, w1]),
                    Inst::Store {
                        src: w0,
                        addr,
                        offset: 16,
                    },
                ],
                Term::Jump(BlockId(6)),
            ),
            // 6: cancel the rest, if the policy says so.
            block(
                vec![bin(BinOp::And, flag, policy, one)],
                Term::Branch {
                    cond: flag,
                    then: BlockId(8),
                    otherwise: BlockId(9),
                },
            ),
            // 7: the end.
            block(
                vec![runtime(RuntimeFn::ScopeEnd, vec![scope], vec![])],
                Term::Return(vec![given]),
            ),
            // 8
            block(
                vec![runtime(RuntimeFn::ScopeCancel, vec![scope], vec![])],
                Term::Jump(BlockId(9)),
            ),
            // 9
            block(vec![Inst::Poll], Term::Jump(BlockId(3))),
        ],
    )
}

/// `body(scope) = 0`: starts three sleepers of 10 ms into the scope, as a
/// group's body does.
fn body() -> LirFunction {
    let (scope, code, ms, flags, index) = (r(0), r(1), r(2), r(3), r(4));
    let start = runtime(
        RuntimeFn::ScopeStart,
        vec![scope, code, ms, flags],
        vec![index],
    );
    function(
        1,
        5,
        vec![block(
            vec![
                Inst::FuncAddr {
                    dst: code,
                    func: CallTarget::Direct(FuncId(SLEEPER as u32)),
                    params: 1,
                    returns: 1,
                },
                konst(ms, 10),
                konst(flags, 1),
                start.clone(),
                start.clone(),
                start,
                konst(index, 0),
            ],
            Term::Return(vec![index]),
        )],
    )
}

/// `guarded(ms) = 7`: sleeps in a region where cancellation waits.
fn guarded() -> LirFunction {
    function(
        1,
        4,
        vec![block(
            vec![
                runtime(RuntimeFn::EnterNoCancel, vec![], vec![]),
                konst(r(1), 1_000_000),
                bin(BinOp::Mul, r(2), r(0), r(1)),
                runtime(RuntimeFn::Sleep, vec![r(2)], vec![]),
                runtime(RuntimeFn::ExitNoCancel, vec![], vec![]),
                konst(r(3), 7),
            ],
            Term::Return(vec![r(3)]),
        )],
    )
}

/// `reader(fd, buf, len) = n`: one read.
fn reader() -> LirFunction {
    LirFunction {
        params: 3,
        returns: 2,
        vregs: 5,
        tracked: vec![],
        blocks: vec![block(
            vec![runtime(
                RuntimeFn::IoRead,
                vec![r(0), r(1), r(2)],
                vec![r(3), r(4)],
            )],
            Term::Return(vec![r(3), r(4)]),
        )],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

fn image() -> Image {
    let mut image = Image::new(&[
        sleeper(),
        spinner(),
        trapper(),
        parent(),
        body(),
        guarded(),
        reader(),
    ]);
    image.with_task_entries();
    image
}

fn scheduler(image: &mut Image, workers: usize) -> Scheduler {
    let code = Arc::new(std::mem::take(&mut image.code));
    Scheduler::new(
        SchedulerConfig {
            workers,
            slice: Some(Duration::from_millis(5)),
        },
        Arc::new(Types::default()),
        code,
    )
}

/// What a parent took: index, status and first result word of each task.
struct Run {
    inputs: Vec<u64>,
    out: Vec<[u64; 3]>,
}

impl Run {
    /// Room for a task per input, and for those a body starts.
    fn new(inputs: &[u64]) -> Run {
        Run {
            inputs: inputs.to_vec(),
            out: vec![[u64::MAX; 3]; inputs.len() + 8],
        }
    }

    /// A parent fiber running `code` on the inputs with `limit` and
    /// `policy`.
    fn parent(&mut self, image: &mut Image, limit: u64, code: usize, policy: u64) -> Box<Fiber> {
        let args = [
            limit,
            image.functions[code] as u64,
            self.inputs.len() as u64,
            self.inputs.as_ptr() as u64,
            self.out.as_mut_ptr() as u64,
            policy,
        ];
        image.fiber(PARENT, &args, FiberConfig::default())
    }

    /// The tasks taken, in the order the parent took them.
    fn taken(&self, n: usize) -> &[[u64; 3]] {
        &self.out[..n]
    }
}

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

fn kind(fiber: &Fiber) -> TrapKind {
    assert_eq!(fiber.state(), FiberState::Trapped);
    fiber.trap().unwrap().kind
}

#[test]
fn the_parent_takes_every_task_in_the_order_they_finish() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let mut run = Run::new(&[60, 20, 40]);
    scheduler.spawn(run.parent(&mut image, 0, SLEEPER, 0));
    let parent = scheduler.wait().pop().unwrap();
    assert_eq!(parent.results().unwrap()[0], 3);
    assert_eq!(
        run.taken(3),
        [
            [1, TASK_RETURNED, 20],
            [2, TASK_RETURNED, 40],
            [0, TASK_RETURNED, 60]
        ]
    );
}

#[test]
fn tasks_run_at_once_up_to_the_limit() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 4);
    let mut run = Run::new(&[50; 6]);
    let start = Instant::now();
    scheduler.spawn(run.parent(&mut image, 2, SLEEPER, 0));
    let parent = scheduler.wait().pop().unwrap();
    let elapsed = start.elapsed();
    assert_eq!(parent.results().unwrap()[0], 6);
    assert!(elapsed >= ms(150), "three rounds of two: {elapsed:?}");
    assert!(elapsed < ms(290), "not one at a time: {elapsed:?}");
    let mut indexes: Vec<u64> = run.taken(6).iter().map(|t| t[0]).collect();
    indexes.sort();
    assert_eq!(indexes, [0, 1, 2, 3, 4, 5]);
    assert!(run.taken(6).iter().all(|t| t[1] == TASK_RETURNED));
}

#[test]
fn many_tasks_on_many_workers_all_come_back() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 4);
    let inputs: Vec<u64> = (0..300).map(|i| i % 3).collect();
    let mut run = Run::new(&inputs);
    scheduler.spawn(run.parent(&mut image, 16, SLEEPER, 0));
    let parent = scheduler.wait().pop().unwrap();
    assert_eq!(parent.results().unwrap()[0], 300);
    let mut taken: Vec<[u64; 3]> = run.taken(300).to_vec();
    taken.sort();
    for (i, t) in taken.iter().enumerate() {
        assert_eq!(*t, [i as u64, TASK_RETURNED, inputs[i]]);
    }
}

#[test]
fn cancelling_the_rest_stops_waiting_tasks_at_once() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let mut run = Run::new(&[10, 10_000, 10_000]);
    let start = Instant::now();
    scheduler.spawn(run.parent(&mut image, 0, SLEEPER, CANCEL_AFTER_FIRST));
    let parent = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() < ms(2_000));
    assert_eq!(parent.results().unwrap()[0], 3);
    let taken = run.taken(3);
    assert_eq!(taken[0], [0, TASK_RETURNED, 10]);
    assert_eq!(taken[1][1], TASK_CANCELLED);
    assert_eq!(taken[2][1], TASK_CANCELLED);
}

#[test]
fn a_cancelled_parent_stops_tasks_that_compute() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let mut run = Run::new(&[0; 4]);
    let parent = run.parent(&mut image, 0, SPINNER, 0);
    let handle = parent.cancel_handle();
    scheduler.spawn(parent);
    std::thread::sleep(ms(50));
    handle.cancel();
    let parent = scheduler.wait().pop().unwrap();
    assert_eq!(kind(&parent), TrapKind::Cancelled);
    for task in run.taken(4) {
        assert_eq!(task[1], TASK_CANCELLED);
    }
}

#[test]
fn a_trap_cancels_the_other_tasks_and_reaches_the_parent() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let mut run = Run::new(&[10, 10_000, 10_000]);
    let start = Instant::now();
    scheduler.spawn(run.parent(&mut image, 0, TRAPPER, 0));
    let parent = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() < ms(2_000));
    let trap = parent.trap().unwrap();
    assert_eq!(trap.kind, TrapKind::Hole);
    assert_eq!(trap.position, Some(42));
    let taken = run.taken(3);
    assert_eq!(taken[0][..2], [0, TASK_TRAPPED]);
    assert_eq!(taken[1][1], TASK_CANCELLED);
    assert_eq!(taken[2][1], TASK_CANCELLED);
}

#[test]
fn a_body_starts_tasks_into_its_scope_beside_the_limit() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    // With a limit of one, a body that counted would wait forever for
    // the place it holds itself.
    let mut run = Run::new(&[0]);
    let start = Instant::now();
    scheduler.spawn(run.parent(&mut image, 1, BODY, AS_BODY));
    let parent = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() >= ms(30), "one sleeper at a time");
    assert_eq!(parent.results().unwrap()[0], 4);
    let mut taken = run.taken(4).to_vec();
    taken.sort();
    assert_eq!(
        taken,
        [
            [0, TASK_RETURNED, 0],
            [1, TASK_RETURNED, 10],
            [2, TASK_RETURNED, 10],
            [3, TASK_RETURNED, 10]
        ]
    );
}

#[test]
fn a_cancelled_parent_cancels_its_tasks_and_stops_at_the_end() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let mut run = Run::new(&[10_000, 10_000, 10_000]);
    // A limit, so that one task waits for a place when the cancel comes.
    let parent = run.parent(&mut image, 2, SLEEPER, 0);
    let handle = parent.cancel_handle();
    let start = Instant::now();
    scheduler.spawn(parent);
    std::thread::sleep(ms(30));
    handle.cancel();
    let parent = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() < ms(2_000));
    assert_eq!(kind(&parent), TrapKind::Cancelled);
    let mut taken = run.taken(3).to_vec();
    taken.sort();
    for (i, t) in taken.iter().enumerate() {
        assert_eq!(t[..2], [i as u64, TASK_CANCELLED]);
    }
}

#[test]
fn a_cancelled_sleep_ends_at_once() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let fiber = image.fiber(SLEEPER, &[10_000], FiberConfig::default());
    let handle = fiber.cancel_handle();
    let start = Instant::now();
    scheduler.spawn(fiber);
    std::thread::sleep(ms(20));
    handle.cancel();
    let fiber = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() < ms(2_000));
    assert_eq!(kind(&fiber), TrapKind::Cancelled);
}

#[test]
fn a_computing_fiber_stops_at_its_next_check() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let fiber = image.fiber(SPINNER, &[0], FiberConfig::default());
    let handle = fiber.cancel_handle();
    scheduler.spawn(fiber);
    std::thread::sleep(ms(20));
    handle.cancel();
    let fiber = scheduler.wait().pop().unwrap();
    assert_eq!(kind(&fiber), TrapKind::Cancelled);
}

#[test]
fn a_fiber_cancelled_before_it_runs_never_starts() {
    let mut image = image();
    let fiber = image.fiber(SLEEPER, &[10_000], FiberConfig::default());
    fiber.cancel_handle().cancel();
    let scheduler = scheduler(&mut image, 1);
    let start = Instant::now();
    scheduler.spawn(fiber);
    let fiber = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() < ms(2_000));
    assert_eq!(kind(&fiber), TrapKind::Cancelled);
}

/// A non-blocking pipe: its read end and write end.
fn pipe() -> (OwnedFd, OwnedFd) {
    let mut fds = [0; 2];
    // SAFETY: the call fills both descriptors, which are then owned.
    unsafe {
        assert_eq!(
            libc::pipe2(fds.as_mut_ptr(), libc::O_NONBLOCK | libc::O_CLOEXEC),
            0
        );
        (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1]))
    }
}

fn reading(image: &mut Image, fd: RawFd, buf: &mut [u8]) -> Box<Fiber> {
    image.fiber_returning(
        READER,
        &[fd as u64, buf.as_mut_ptr() as u64, buf.len() as u64],
        2,
        FiberConfig::default(),
    )
}

#[test]
fn a_cancelled_read_leaves_the_descriptor_to_the_next() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let (rx, tx) = pipe();
    let mut first = [0u8; 4];
    let fiber = reading(&mut image, rx.as_raw_fd(), &mut first);
    let handle = fiber.cancel_handle();
    scheduler.spawn(fiber);
    std::thread::sleep(ms(20));
    handle.cancel();
    let fiber = scheduler.wait().pop().unwrap();
    assert_eq!(kind(&fiber), TrapKind::Cancelled);

    let mut second = [0u8; 4];
    scheduler.spawn(reading(&mut image, rx.as_raw_fd(), &mut second));
    std::thread::sleep(ms(20));
    // SAFETY: writes from a live buffer.
    let n = unsafe { libc::write(tx.as_raw_fd(), b"crag".as_ptr().cast(), 4) };
    assert_eq!(n, 4);
    let fiber = scheduler.wait().pop().unwrap();
    assert_eq!(fiber.results().unwrap(), [4, 0]);
    assert_eq!(&second, b"crag");
    assert_eq!(first, [0; 4]);
}

#[test]
fn cancellation_waits_for_the_region_to_end() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let fiber = image.fiber(GUARDED, &[100], FiberConfig::default());
    let handle = fiber.cancel_handle();
    let start = Instant::now();
    scheduler.spawn(fiber);
    std::thread::sleep(ms(20));
    handle.cancel();
    let fiber = scheduler.wait().pop().unwrap();
    assert!(start.elapsed() >= ms(100), "the sleep was not called off");
    assert_eq!(kind(&fiber), TrapKind::Cancelled);
}

#[test]
fn a_region_left_without_a_cancellation_returns() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    scheduler.spawn(image.fiber(GUARDED, &[1], FiberConfig::default()));
    let fiber = scheduler.wait().pop().unwrap();
    assert_eq!(fiber.results().unwrap()[0], 7);
}

#[test]
fn without_a_scheduler_a_scope_is_unsupported() {
    let mut image = image();
    let mut run = Run::new(&[1]);
    let mut parent = run.parent(&mut image, 0, SLEEPER, 0);
    let mut worker = Worker::new();
    worker.set_code_map(Arc::new(std::mem::take(&mut image.code)));
    assert_eq!(worker.resume(&mut parent), FiberState::Trapped);
    assert_eq!(parent.trap().unwrap().kind, TrapKind::Unsupported);
}
