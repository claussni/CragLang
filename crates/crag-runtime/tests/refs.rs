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

//! Refs (Plan §11.7.6): updates that race lose nothing, a stale commit
//! conflicts, an unchanged value is not written, and a value a write
//! replaces keeps its reference until no task borrows it. Commutative
//! updates (§11.7.8) race with the others and lose nothing, and one that
//! overflows changes nothing.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::{
    CountedField, ElementLayout, REF_ADD, REF_AND, REF_COMMITTED, REF_CONFLICT, REF_MAX, REF_MIN,
    REF_MUL, REF_OR, REF_OVERFLOW, REF_SUB, REF_UNSIGNED, REF_XOR, RuntimeFn, TypeDescriptor,
};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::{FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const INCREMENT: usize = 0;
const HOLD: usize = 1;
const READ: usize = 2;
const COMMIT: usize = 3;
const SWAP: usize = 4;
const SWAPPER: usize = 5;
const READER: usize = 6;
const APPLY: usize = 7;
const ADDER: usize = 8;

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

fn add(dst: VReg, a: VReg, b: VReg) -> Inst {
    Inst::Bin {
        op: BinOp::Add,
        dst,
        a,
        b,
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

/// A function of `params` parameters that calls runtime function `func`
/// with them and returns its `results` results.
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

/// `increment(cell, n, out) = conflicts`: adds one to the ref `n` times,
/// as `update { v -> v + 1 }` does, rerunning on conflicts, which it
/// counts.
fn increment() -> LirFunction {
    let (cell, n, out) = (r(0), r(1), r(2));
    let (i, conflicts, one, zero, list, flag, version, v, status) =
        (r(3), r(4), r(5), r(6), r(7), r(8), r(9), r(10), r(11));
    lir(
        3,
        1,
        12,
        vec![
            block(
                vec![
                    konst(i, 0),
                    konst(conflicts, 0),
                    konst(one, 1),
                    konst(zero, 0),
                    konst(list, INTS as i64),
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
                Term::Branch {
                    cond: flag,
                    then: BlockId(5),
                    otherwise: BlockId(2),
                },
            ),
            block(
                vec![
                    runtime(RuntimeFn::RefRead, vec![cell, out], vec![version]),
                    Inst::Load {
                        dst: v,
                        addr: out,
                        offset: 0,
                    },
                    add(v, v, one),
                    runtime(
                        RuntimeFn::RefCommit,
                        vec![cell, version, list, v, zero],
                        vec![status],
                    ),
                    Inst::Cmp {
                        cond: Cond::Ne,
                        dst: flag,
                        a: status,
                        b: zero,
                    },
                ],
                Term::Branch {
                    cond: flag,
                    then: BlockId(3),
                    otherwise: BlockId(4),
                },
            ),
            block(
                vec![add(conflicts, conflicts, one), Inst::Poll],
                Term::Jump(BlockId(2)),
            ),
            block(vec![add(i, i, one), Inst::Poll], Term::Jump(BlockId(1))),
            block(vec![], Term::Return(vec![conflicts])),
        ],
    )
}

/// `hold(cell, out) = version`: reads the ref, yields while it borrows the
/// value, and ends the read.
fn hold() -> LirFunction {
    let (cell, out, version) = (r(0), r(1), r(2));
    lir(
        2,
        1,
        3,
        vec![block(
            vec![
                runtime(RuntimeFn::RefRead, vec![cell, out], vec![version]),
                runtime(RuntimeFn::Yield, vec![], vec![]),
                runtime(RuntimeFn::RefDone, vec![], vec![]),
            ],
            Term::Return(vec![version]),
        )],
    )
}

/// A function of `params` parameters, the last of them a count, that
/// runs `body` that many times, with a poll after each, and returns
/// `result`. Registers from `params + 3` on are the body's.
fn repeat(params: u32, vregs: u32, body: Vec<Inst>, result: VReg) -> LirFunction {
    let n = r(params - 1);
    let (i, one, flag) = (r(params), r(params + 1), r(params + 2));
    let mut body = body;
    body.extend([add(i, i, one), Inst::Poll]);
    lir(
        params,
        1,
        vregs,
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
            block(body, Term::Jump(BlockId(1))),
            block(vec![], Term::Return(vec![result])),
        ],
    )
}

/// `swapper(cell, value, n) = value`: swaps its value into the ref `n`
/// times, each time with the one it got back, and gives the last.
fn swapper() -> LirFunction {
    let (cell, value) = (r(0), r(1));
    let (list, zero, unused) = (r(6), r(7), r(8));
    repeat(
        3,
        9,
        vec![
            konst(list, BOXES as i64),
            konst(zero, 0),
            runtime(
                RuntimeFn::RefSwap,
                vec![cell, list, value, zero],
                vec![value, unused],
            ),
        ],
        value,
    )
}

/// `reader(cell, out, n) = n`: borrows the ref's value `n` times, polling
/// while it holds it.
fn reader() -> LirFunction {
    let (cell, out, n) = (r(0), r(1), r(2));
    let version = r(6);
    repeat(
        3,
        7,
        vec![
            runtime(RuntimeFn::RefRead, vec![cell, out], vec![version]),
            Inst::Poll,
            runtime(RuntimeFn::RefDone, vec![], vec![]),
        ],
        n,
    )
}

/// `adder(cell, n) = n`: adds one to the ref `n` times, as a commutative
/// update does.
fn adder() -> LirFunction {
    let cell = r(0);
    let (op, ty, one, status) = (r(5), r(6), r(7), r(8));
    repeat(
        2,
        9,
        vec![
            konst(op, REF_ADD as i64),
            konst(ty, 64),
            konst(one, 1),
            runtime(RuntimeFn::RefApply, vec![cell, op, ty, one], vec![status]),
        ],
        r(1),
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

/// The epoch is the process's: the tests that watch releases must not
/// pin it for each other.
static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(|e| e.into_inner())
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
                increment(),
                hold(),
                calling(RuntimeFn::RefRead, 2, 1),
                calling(RuntimeFn::RefCommit, 5, 1),
                calling(RuntimeFn::RefSwap, 4, 2),
                swapper(),
                reader(),
                calling(RuntimeFn::RefApply, 4, 1),
                adder(),
            ]),
            types,
            worker,
        }
    }

    fn scheduler(&mut self) -> Scheduler {
        let code = Arc::new(std::mem::take(&mut self.image.code));
        Scheduler::new(
            SchedulerConfig {
                workers: 4,
                slice: Some(Duration::from_millis(1)),
            },
            self.types.clone(),
            code,
        )
    }

    /// Runs a function to its end on the setup's worker.
    fn call(&mut self, func: usize, args: &[u64], results: u32) -> [u64; 2] {
        let mut fiber = self
            .image
            .fiber_returning(func, args, results, FiberConfig::default());
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
}

#[test]
fn updates_that_race_lose_no_increment() {
    let _serial = serial();
    const TASKS: u64 = 8;
    const EACH: u64 = 5_000;
    let mut setup = Setup::new();
    let cell = cell(0);
    let mut outs = vec![[0u64; 2]; TASKS as usize];
    let fibers = outs
        .iter_mut()
        .map(|out| {
            let args = [addr(&*cell), EACH, out.as_mut_ptr() as u64];
            setup
                .image
                .fiber_returning(INCREMENT, &args, 1, FiberConfig::default())
        })
        .collect();
    let scheduler = setup.scheduler();
    scheduler.spawn_all(fibers);
    for fiber in scheduler.wait() {
        assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    }
    assert_eq!(cell[1].load(Ordering::SeqCst), TASKS * EACH);
    let version = cell[0].load(Ordering::SeqCst);
    assert!(
        version > 0 && version.is_multiple_of(2),
        "version {version}"
    );
}

#[test]
fn a_commit_after_another_write_conflicts() {
    let _serial = serial();
    let mut setup = Setup::new();
    let cell = cell(5);
    let mut out = [0u64; 2];
    let [version, _] = setup.call(READ, &[addr(&*cell), out.as_mut_ptr() as u64], 1);
    assert_eq!(out[0], 5);
    // Another task writes meanwhile.
    let [old, _] = setup.call(SWAP, &[addr(&*cell), INTS, 7, 0], 2);
    assert_eq!(old, 5);
    let [status, _] = setup.call(COMMIT, &[addr(&*cell), version, INTS, 6, 0], 1);
    assert_eq!(status, REF_CONFLICT);
    assert_eq!(cell[1].load(Ordering::SeqCst), 7);
    // Read again, the update commits.
    let [version, _] = setup.call(READ, &[addr(&*cell), out.as_mut_ptr() as u64], 1);
    let [status, _] = setup.call(COMMIT, &[addr(&*cell), version, INTS, 8, 0], 1);
    assert_eq!(status, REF_COMMITTED);
    assert_eq!(cell[1].load(Ordering::SeqCst), 8);
    assert!(cell[0].load(Ordering::SeqCst) > version);
}

#[test]
fn an_unchanged_value_is_not_written() {
    let _serial = serial();
    let fake = FakeBox::new();
    let mut setup = Setup::new();
    let cell = cell(addr(&*fake));
    let mut out = [0u64; 2];
    let [version, _] = setup.call(READ, &[addr(&*cell), out.as_mut_ptr() as u64], 1);
    // The closure gives its input back, with a reference of its own.
    fake.count.fetch_add(1, Ordering::SeqCst);
    let [status, _] = setup.call(COMMIT, &[addr(&*cell), version, BOXES, out[0], 0], 1);
    assert_eq!(status, REF_COMMITTED);
    assert_eq!(cell[0].load(Ordering::SeqCst), version);
    assert_eq!(fake.count(), 1_000);
}

#[test]
fn a_replaced_value_keeps_its_reference_while_a_task_borrows_it() {
    let _serial = serial();
    let (a, b) = (FakeBox::new(), FakeBox::new());
    let mut setup = Setup::new();
    let cell = cell(addr(&*a));
    let mut out = [0u64; 2];
    let mut holder = setup.image.fiber_returning(
        HOLD,
        &[addr(&*cell), out.as_mut_ptr() as u64],
        1,
        FiberConfig::default(),
    );
    // The holder reads and yields with the value borrowed.
    assert_eq!(setup.worker.resume(&mut holder), FiberState::Runnable);
    assert_eq!(out[0], addr(&*a));
    let [old, _] = setup.call(SWAP, &[addr(&*cell), BOXES, addr(&*b), 0], 2);
    assert_eq!(old, addr(&*a));
    // The swap's caller has a reference of its own; the cell's waits.
    assert_eq!(a.count(), 1_001);
    assert_eq!(setup.worker.resume(&mut holder), FiberState::Finished);
    assert_eq!(a.count(), 1_000);
    assert_eq!(b.count(), 1_000);
}

#[test]
fn a_task_that_stops_while_it_borrows_is_unpinned() {
    let _serial = serial();
    let (a, b) = (FakeBox::new(), FakeBox::new());
    let mut setup = Setup::new();
    let cell = cell(addr(&*a));
    let mut out = [0u64; 2];
    // A read that is never ended: its task finishes pinned.
    setup.call(READ, &[addr(&*cell), out.as_mut_ptr() as u64], 1);
    // Nothing borrows the old value: the cell's reference goes at once.
    setup.call(SWAP, &[addr(&*cell), BOXES, addr(&*b), 0], 2);
    assert_eq!(a.count(), 1_000);
}

#[test]
fn borrowed_reads_racing_writes_keep_every_reference() {
    let _serial = serial();
    let boxes = [FakeBox::new(), FakeBox::new(), FakeBox::new()];
    let mut setup = Setup::new();
    let cell = cell(addr(&*boxes[0]));
    let mut outs = vec![[0u64; 2]; 4];
    let mut fibers = Vec::new();
    for b in &boxes[1..] {
        // Each writer owns a reference to its first value.
        b.count.fetch_add(1, Ordering::SeqCst);
        let args = [addr(&*cell), addr(&**b), 5_000];
        fibers.push(
            setup
                .image
                .fiber_returning(SWAPPER, &args, 1, FiberConfig::default()),
        );
    }
    for out in &mut outs {
        let args = [addr(&*cell), out.as_mut_ptr() as u64, 20_000];
        fibers.push(
            setup
                .image
                .fiber_returning(READER, &args, 1, FiberConfig::default()),
        );
    }
    let scheduler = setup.scheduler();
    scheduler.spawn_all(fibers);
    for fiber in scheduler.wait() {
        assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    }
    // A read with no task pinned releases all that waits.
    let mut out = [0u64; 2];
    setup.call(READ, &[addr(&*cell), out.as_mut_ptr() as u64], 1);
    // The cell and the two writers hold one reference each.
    let total: u64 = boxes.iter().map(|b| b.count()).sum();
    assert_eq!(total, 3_000 + 2);
    assert!(out[0] == addr(&*boxes[0]) || out[0] == addr(&*boxes[1]) || out[0] == addr(&*boxes[2]));
}

#[test]
fn commutative_updates_that_race_with_others_lose_nothing() {
    let _serial = serial();
    const EACH: u64 = 5_000;
    let mut setup = Setup::new();
    let cell = cell(0);
    let mut outs = [[0u64; 2]; 4];
    let mut fibers: Vec<_> = outs
        .iter_mut()
        .map(|out| {
            let args = [addr(&*cell), EACH, out.as_mut_ptr() as u64];
            setup
                .image
                .fiber_returning(INCREMENT, &args, 1, FiberConfig::default())
        })
        .collect();
    fibers.extend((0..4).map(|_| {
        setup
            .image
            .fiber_returning(ADDER, &[addr(&*cell), EACH], 1, FiberConfig::default())
    }));
    let scheduler = setup.scheduler();
    scheduler.spawn_all(fibers);
    for fiber in scheduler.wait() {
        assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    }
    assert_eq!(cell[1].load(Ordering::SeqCst), 8 * EACH);
}

#[test]
fn a_commutative_update_applies_its_operation() {
    let _serial = serial();
    let mut setup = Setup::new();
    let u = REF_UNSIGNED;
    let minus = |x: i64| x as u64;
    // (operation, type, value, k, result)
    let cases = [
        (REF_ADD, 64, 5, 3, 8),
        (REF_SUB, 64, 5, 7, minus(-2)),
        (REF_MUL, 64, minus(-4), 3, minus(-12)),
        (REF_AND, 64, 0b1100, 0b1010, 0b1000),
        (REF_OR, 64, 0b1100, 0b1010, 0b1110),
        (REF_XOR, 64, 0b1100, 0b1010, 0b0110),
        (REF_MIN, 64, minus(-1), 1, minus(-1)),
        (REF_MAX, 64, minus(-1), 1, 1),
        (REF_MIN, 64 | u, u64::MAX, 1, 1),
        (REF_MAX, 64 | u, u64::MAX, 1, u64::MAX),
        (REF_ADD, 64 | u, u64::MAX - 1, 1, u64::MAX),
        (REF_ADD, 8, 126, 1, 127),
        (REF_SUB, 8, minus(-127), 1, minus(-128)),
        (REF_ADD, 8 | u, 254, 1, 255),
        (REF_MUL, 32 | u, 65_536, 65_535, 4_294_901_760),
    ];
    for (op, ty, value, k, result) in cases {
        let cell = cell(value);
        let [status, _] = setup.call(APPLY, &[addr(&*cell), op, ty, k], 1);
        assert_eq!(status, REF_COMMITTED, "{op} {ty:#x} {value} {k}");
        assert_eq!(
            cell[1].load(Ordering::SeqCst),
            result,
            "{op} {ty:#x} {value} {k}"
        );
        assert_eq!(cell[0].load(Ordering::SeqCst) % 2, 0);
        assert!(cell[0].load(Ordering::SeqCst) > 0);
    }
}

#[test]
fn a_commutative_update_that_overflows_changes_nothing() {
    let _serial = serial();
    let mut setup = Setup::new();
    let u = REF_UNSIGNED;
    let minus = |x: i64| x as u64;
    let cases = [
        (REF_ADD, 64, i64::MAX as u64, 1),
        (REF_SUB, 64, minus(i64::MIN), 1),
        (REF_MUL, 64, 1 << 62, 2),
        (REF_ADD, 64 | u, u64::MAX, 1),
        (REF_SUB, 64 | u, 0, 1),
        (REF_MUL, 64 | u, u64::MAX, u64::MAX),
        (REF_ADD, 8, 127, 1),
        (REF_SUB, 8, minus(-128), 1),
        (REF_ADD, 8 | u, 255, 1),
        (REF_SUB, 16 | u, 3, 4),
        (REF_MUL, 32, 65_536, 32_768),
    ];
    for (op, ty, value, k) in cases {
        let cell = cell(value);
        let [status, _] = setup.call(APPLY, &[addr(&*cell), op, ty, k], 1);
        assert_eq!(status, REF_OVERFLOW, "{op} {ty:#x} {value} {k}");
        assert_eq!(cell[1].load(Ordering::SeqCst), value);
        assert_eq!(cell[0].load(Ordering::SeqCst), 0);
    }
}

#[test]
fn a_commit_after_a_commutative_update_conflicts() {
    let _serial = serial();
    let mut setup = Setup::new();
    let cell = cell(5);
    let mut out = [0u64; 2];
    let [version, _] = setup.call(READ, &[addr(&*cell), out.as_mut_ptr() as u64], 1);
    let [status, _] = setup.call(APPLY, &[addr(&*cell), REF_ADD, 64, 1], 1);
    assert_eq!(status, REF_COMMITTED);
    let [status, _] = setup.call(COMMIT, &[addr(&*cell), version, INTS, 10, 0], 1);
    assert_eq!(status, REF_CONFLICT);
    assert_eq!(cell[1].load(Ordering::SeqCst), 6);
}
