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

//! Streams and hubs (Plan §11.7.5): values in order through a buffer or
//! a hand-off, the ends closed or abandoned, puts that wait or fail at
//! once, fan-out, broadcast and release, and cancelled waits, also as a
//! value comes.

use std::sync::Arc;
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::{
    CountedField, ElementLayout, HUB_BROADCAST, HUB_FAN_OUT, RuntimeFn, STREAM_ABANDONED,
    STREAM_CLOSED, STREAM_FULL, STREAM_OK, TrapKind, TypeDescriptor,
};
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term, VReg};
use crag_runtime::{Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

const PRODUCER: usize = 0;
const CONSUMER: usize = 1;
const STREAM_NEW: usize = 2;
const HUB_NEW: usize = 3;
const HUB_SINK: usize = 4;
const HUB_SOURCE: usize = 5;
const HUB_SEAL: usize = 6;
const HUB_RELEASE: usize = 7;
const HUB_DROP: usize = 8;
const TRY_PUTS: usize = 9;
const CLOSE: usize = 10;
const DISPOSE: usize = 11;

/// The list type whose elements the values are laid out as: one word.
const INTS: u64 = 1;

/// A list type of boxes.
const BOXES: u64 = 2;

/// A consumer that takes every value.
const ALL: u64 = u64::MAX;

fn konst(dst: VReg, value: i64) -> Inst {
    Inst::Const { dst, value }
}

fn runtime(func: RuntimeFn, args: Vec<VReg>, dsts: Vec<VReg>) -> Inst {
    Inst::CallRuntime { func, args, dsts }
}

fn cmp(cond: Cond, dst: VReg, a: VReg, b: VReg) -> Inst {
    Inst::Cmp { cond, dst, a, b }
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
        natives: Vec::new(),
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

/// `producer(sink, n, close, fixed) = (sent, status)`: puts 1 to `n`, or
/// `n` times `fixed` when it is not zero, until a put fails, closes the
/// sink if `close` is set, and disposes it.
fn producer() -> LirFunction {
    let (sink, n, close, fixed) = (r(0), r(1), r(2), r(3));
    let (i, one, flag, status, zero, sent, value) = (r(4), r(5), r(6), r(7), r(8), r(9), r(10));
    lir(
        4,
        2,
        11,
        vec![
            block(
                vec![konst(one, 1), konst(zero, 0), konst(i, 1), konst(status, 0)],
                Term::Jump(BlockId(1)),
            ),
            block(vec![cmp(Cond::Gt, flag, i, n)], branch(flag, 3, 2)),
            block(
                vec![
                    cmp(Cond::Ne, flag, fixed, zero),
                    Inst::Select {
                        dst: value,
                        cond: flag,
                        a: fixed,
                        b: i,
                    },
                    runtime(RuntimeFn::StreamPut, vec![sink, value, zero], vec![status]),
                    cmp(Cond::Ne, flag, status, zero),
                ],
                branch(flag, 3, 4),
            ),
            block(
                vec![
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: sent,
                        a: i,
                        b: one,
                    },
                    cmp(Cond::Ne, flag, close, zero),
                ],
                branch(flag, 5, 6),
            ),
            block(
                vec![
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
            block(
                vec![runtime(RuntimeFn::StreamClose, vec![sink], vec![])],
                Term::Jump(BlockId(6)),
            ),
            block(
                vec![runtime(RuntimeFn::StreamDispose, vec![sink], vec![])],
                Term::Return(vec![sent, status]),
            ),
        ],
    )
}

/// `consumer(source, out, slot, limit) = (count, status)`: takes values
/// into `out` until the stream ends, or closes the source after `limit`,
/// and disposes it.
fn consumer() -> LirFunction {
    let (source, out, slot, limit) = (r(0), r(1), r(2), r(3));
    let (count, status, eight, addr, tmp, zero, one, flag, v) =
        (r(4), r(5), r(6), r(7), r(8), r(9), r(10), r(11), r(12));
    lir(
        4,
        2,
        13,
        vec![
            block(
                vec![
                    konst(count, 0),
                    konst(status, 0),
                    konst(eight, 8),
                    konst(zero, 0),
                    konst(one, 1),
                ],
                Term::Jump(BlockId(1)),
            ),
            block(vec![cmp(Cond::Eq, flag, count, limit)], branch(flag, 5, 2)),
            block(
                vec![
                    runtime(RuntimeFn::StreamNext, vec![source, slot], vec![status]),
                    cmp(Cond::Ne, flag, status, zero),
                ],
                branch(flag, 4, 3),
            ),
            block(
                vec![
                    Inst::Load {
                        dst: v,
                        addr: slot,
                        offset: 0,
                    },
                    Inst::Bin {
                        op: BinOp::Mul,
                        dst: tmp,
                        a: count,
                        b: eight,
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: addr,
                        a: out,
                        b: tmp,
                    },
                    Inst::Store {
                        src: v,
                        addr,
                        offset: 0,
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: count,
                        a: count,
                        b: one,
                    },
                    Inst::Poll,
                ],
                Term::Jump(BlockId(1)),
            ),
            block(
                vec![runtime(RuntimeFn::StreamDispose, vec![source], vec![])],
                Term::Return(vec![count, status]),
            ),
            block(
                vec![runtime(RuntimeFn::StreamClose, vec![source], vec![])],
                Term::Jump(BlockId(4)),
            ),
        ],
    )
}

/// `try_puts(sink) = (first, second)`: the statuses of two puts that do
/// not wait.
fn try_puts() -> LirFunction {
    let (sink, a, b, one, zero) = (r(0), r(1), r(2), r(3), r(4));
    lir(
        1,
        2,
        5,
        vec![block(
            vec![
                konst(one, 1),
                konst(zero, 0),
                runtime(RuntimeFn::StreamTryPut, vec![sink, one, zero], vec![a]),
                runtime(RuntimeFn::StreamTryPut, vec![sink, one, zero], vec![b]),
            ],
            Term::Return(vec![a, b]),
        )],
    )
}

fn types() -> Arc<Types> {
    let list = |counted: Vec<CountedField>| TypeDescriptor::List {
        element: ElementLayout::of_words(1, counted.clone()),
        cell: ElementLayout::of_words(1, counted),
    };
    Arc::new(Types::new([
        (INTS as u32, list(vec![])),
        (BOXES as u32, list(vec![CountedField::Box(0)])),
    ]))
}

struct Setup {
    image: Image,
    types: Arc<Types>,
}

impl Setup {
    fn new() -> Setup {
        Setup {
            image: Image::new(&[
                producer(),
                consumer(),
                calling(RuntimeFn::StreamNew, 2, 2),
                calling(RuntimeFn::HubNew, 3, 1),
                calling(RuntimeFn::HubSink, 1, 1),
                calling(RuntimeFn::HubSource, 1, 1),
                calling(RuntimeFn::HubSeal, 1, 0),
                calling(RuntimeFn::HubRelease, 2, 0),
                calling(RuntimeFn::HubDrop, 1, 0),
                try_puts(),
                calling(RuntimeFn::StreamClose, 1, 0),
                calling(RuntimeFn::StreamDispose, 1, 0),
            ]),
            types: types(),
        }
    }

    fn scheduler(&mut self, workers: usize) -> Scheduler {
        let code = Arc::new(std::mem::take(&mut self.image.code));
        Scheduler::new(
            SchedulerConfig {
                workers,
                slice: Some(Duration::from_millis(5)),
            },
            self.types.clone(),
            code,
        )
    }

    /// Runs a function on a worker of its own, outside any scheduler.
    fn call(&mut self, func: usize, args: &[u64], results: u32) -> [u64; 2] {
        let mut fiber = self
            .image
            .fiber_returning(func, args, results, FiberConfig::default());
        let mut worker = Worker::new();
        worker.set_types(self.types.clone());
        assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
        fiber.results().unwrap()
    }

    fn stream(&mut self, capacity: u64) -> (u64, u64) {
        self.stream_of(capacity, INTS)
    }

    fn stream_of(&mut self, capacity: u64, list: u64) -> (u64, u64) {
        let [sink, source] = self.call(STREAM_NEW, &[capacity, list], 2);
        (sink, source)
    }

    fn hub(&mut self, capacity: u64, kind: u64) -> u64 {
        self.hub_of(capacity, kind, INTS)
    }

    fn hub_of(&mut self, capacity: u64, kind: u64, list: u64) -> u64 {
        self.call(HUB_NEW, &[capacity, list, kind], 1)[0]
    }

    fn producer(&mut self, sink: u64, n: u64, close: bool) -> Box<Fiber> {
        self.putting(sink, n, close, 0)
    }

    /// A producer that puts `value` `n` times.
    fn putting(&mut self, sink: u64, n: u64, close: bool, value: u64) -> Box<Fiber> {
        self.image.fiber_returning(
            PRODUCER,
            &[sink, n, close as u64, value],
            2,
            FiberConfig::default(),
        )
    }

    fn consumer(&mut self, source: u64, taken: &mut Taken, limit: u64) -> Box<Fiber> {
        let args = [
            source,
            taken.values.as_mut_ptr() as u64,
            taken.slot.as_mut_ptr() as u64,
            limit,
        ];
        self.image
            .fiber_returning(CONSUMER, &args, 2, FiberConfig::default())
    }
}

/// Where a consumer writes what it takes.
struct Taken {
    values: Vec<u64>,
    slot: [u64; 2],
}

impl Taken {
    fn new(n: usize) -> Taken {
        Taken {
            values: vec![0; n],
            slot: [0; 2],
        }
    }

    fn first(&self, n: u64) -> &[u64] {
        &self.values[..n as usize]
    }
}

/// Runs the fibers until all have stopped, and gives them back in the
/// order they were passed: a fiber keeps its address in the scheduler.
#[allow(clippy::vec_box)]
fn run(scheduler: &Scheduler, fibers: Vec<Box<Fiber>>) -> Vec<Box<Fiber>> {
    let order: Vec<*const Fiber> = fibers.iter().map(|f| &raw const **f).collect();
    scheduler.spawn_all(fibers);
    let mut stopped = scheduler.wait();
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

fn results(fiber: &Fiber) -> [u64; 2] {
    assert_eq!(fiber.state(), FiberState::Finished, "{:?}", fiber.trap());
    fiber.results().unwrap()
}

fn kind(fiber: &Fiber) -> TrapKind {
    assert_eq!(fiber.state(), FiberState::Trapped);
    fiber.trap().unwrap().kind
}

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

fn one_to(n: u64) -> Vec<u64> {
    (1..=n).collect()
}

/// Runs a producer and a consumer of a new stream: what each gave, and
/// what the consumer took.
fn pipe(capacity: u64, n: u64, close: bool, limit: u64) -> ([u64; 2], [u64; 2], Taken) {
    let mut setup = Setup::new();
    let (sink, source) = setup.stream(capacity);
    let mut taken = Taken::new(n as usize + 1);
    let consumer = setup.consumer(source, &mut taken, limit);
    let producer = setup.producer(sink, n, close);
    let scheduler = setup.scheduler(2);
    let fibers = run(&scheduler, vec![producer, consumer]);
    (results(&fibers[0]), results(&fibers[1]), taken)
}

#[test]
fn a_stream_carries_its_values_in_order_and_then_closes() {
    let (producer, consumer, taken) = pipe(2, 200, true, ALL);
    assert_eq!(producer, [200, STREAM_OK]);
    assert_eq!(consumer, [200, STREAM_CLOSED]);
    assert_eq!(taken.first(200), one_to(200));
}

#[test]
fn a_stream_without_a_buffer_hands_each_value_over() {
    let (producer, consumer, taken) = pipe(0, 100, true, ALL);
    assert_eq!(producer, [100, STREAM_OK]);
    assert_eq!(consumer, [100, STREAM_CLOSED]);
    assert_eq!(taken.first(100), one_to(100));
}

#[test]
fn a_sink_that_goes_without_closing_abandons_the_stream() {
    let (producer, consumer, taken) = pipe(4, 30, false, ALL);
    assert_eq!(producer, [30, STREAM_OK]);
    assert_eq!(consumer, [30, STREAM_ABANDONED]);
    assert_eq!(taken.first(30), one_to(30));
}

#[test]
fn a_consumer_that_closes_stops_the_producer() {
    let (producer, consumer, taken) = pipe(1, 1_000, true, 5);
    assert_eq!(consumer, [5, STREAM_OK]);
    assert_eq!(taken.first(5), one_to(5));
    // Five taken, at most one in the buffer and one handed over or waiting.
    assert_eq!(producer[1], STREAM_CLOSED);
    assert!((5..=7).contains(&producer[0]), "{producer:?}");
}

#[test]
fn a_put_that_does_not_wait_reports_a_full_buffer() {
    let mut setup = Setup::new();
    let (sink, source) = setup.stream(1);
    assert_eq!(setup.call(TRY_PUTS, &[sink], 2), [STREAM_OK, STREAM_FULL]);
    setup.call(CLOSE, &[source], 0);
    // The consumer is gone: puts give `Closed`.
    assert_eq!(
        setup.call(TRY_PUTS, &[sink], 2),
        [STREAM_CLOSED, STREAM_CLOSED]
    );
    setup.call(DISPOSE, &[source], 0);
    setup.call(DISPOSE, &[sink], 0);
}

#[test]
fn a_put_waiting_for_room_is_cancelled() {
    let mut setup = Setup::new();
    let (sink, _source) = setup.stream(0);
    let producer = setup.producer(sink, 10, true);
    let handle = producer.cancel_handle();
    let scheduler = setup.scheduler(1);
    scheduler.spawn(producer);
    std::thread::sleep(ms(20));
    handle.cancel();
    let producer = scheduler.wait().pop().unwrap();
    assert_eq!(kind(&producer), TrapKind::Cancelled);
}

#[test]
fn a_take_waiting_for_a_value_is_cancelled() {
    let mut setup = Setup::new();
    let (_sink, source) = setup.stream(4);
    let mut taken = Taken::new(1);
    let consumer = setup.consumer(source, &mut taken, ALL);
    let handle = consumer.cancel_handle();
    let scheduler = setup.scheduler(1);
    scheduler.spawn(consumer);
    std::thread::sleep(ms(20));
    handle.cancel();
    let consumer = scheduler.wait().pop().unwrap();
    assert_eq!(kind(&consumer), TrapKind::Cancelled);
}

#[test]
fn a_take_cancelled_as_a_value_comes_loses_no_value() {
    // A cancellation and a put race for a waiting take: the value goes to
    // the take, which returns it, or stays with the put, which hands it to
    // the other consumer. Every value is taken exactly once either way.
    const N: u64 = 200;
    let mut midway = 0;
    for round in 0..100u64 {
        let mut setup = Setup::new();
        let hub = setup.hub(round % 2, HUB_FAN_OUT);
        let sink = setup.call(HUB_SINK, &[hub], 1)[0];
        let mut taken = [Taken::new(N as usize + 1), Taken::new(N as usize + 1)];
        let sources = [0, 1].map(|_| setup.call(HUB_SOURCE, &[hub], 1)[0]);
        setup.call(HUB_DROP, &[hub], 0);
        let producer = setup.producer(sink, N, true);
        let [a, b] = &mut taken;
        let cancelled = setup.consumer(sources[0], a, ALL);
        let other = setup.consumer(sources[1], b, ALL);
        let handle = cancelled.cancel_handle();
        let scheduler = setup.scheduler(4);
        let order: Vec<*const Fiber> = [&producer, &cancelled, &other]
            .map(|f| &raw const **f)
            .to_vec();
        scheduler.spawn_all(vec![producer, cancelled, other]);
        std::thread::sleep(Duration::from_micros(round % 50 * 20));
        handle.cancel();
        let fibers = scheduler.wait();
        let at = |i: usize| {
            fibers
                .iter()
                .find(|&f| std::ptr::eq(&raw const **f, order[i]))
                .expect("stopped")
        };
        assert_eq!(results(at(0)), [N, STREAM_OK]);
        assert_eq!(results(at(2))[1], STREAM_CLOSED);
        if at(1).state() == FiberState::Trapped {
            assert_eq!(kind(at(1)), TrapKind::Cancelled);
            // Its source was left as it was; the test disposes it.
            setup.call(DISPOSE, &[sources[0]], 0);
            midway += u32::from(taken[0].values[0] != 0);
        }
        let mut all: Vec<u64> = taken
            .iter()
            .flat_map(|t| t.values.iter().copied().filter(|&v| v != 0))
            .collect();
        all.sort();
        assert_eq!(all, one_to(N), "round {round}");
    }
    // The race was run: some takes were cancelled amid the values.
    assert!(midway > 0);
}

#[test]
fn without_a_scheduler_a_take_that_would_wait_is_unsupported() {
    let mut setup = Setup::new();
    let (_sink, source) = setup.stream(1);
    let mut taken = Taken::new(1);
    let mut consumer = setup.consumer(source, &mut taken, ALL);
    let mut worker = Worker::new();
    worker.set_types(setup.types.clone());
    assert_eq!(worker.resume(&mut consumer), FiberState::Trapped);
    assert_eq!(consumer.trap().unwrap().kind, TrapKind::Unsupported);
}

/// What each producer and consumer gave, and what each consumer took.
type Outcome = (Vec<[u64; 2]>, Vec<([u64; 2], Taken)>);

/// Runs producers and consumers of a hub of `kind`, sealed and dropped
/// once their ends are made: what each producer and consumer gave, and
/// what each consumer took.
fn hub(kind: u64, capacity: u64, producers: &[(u64, bool)], consumers: usize) -> Outcome {
    let mut setup = Setup::new();
    let hub = setup.hub(capacity, kind);
    let total: u64 = producers.iter().map(|p| p.0).sum();
    let mut fibers = Vec::new();
    for &(n, close) in producers {
        let sink = setup.call(HUB_SINK, &[hub], 1)[0];
        fibers.push(setup.producer(sink, n, close));
    }
    let mut taken: Vec<Taken> = (0..consumers)
        .map(|_| Taken::new(total as usize + 1))
        .collect();
    for t in &mut taken {
        let source = setup.call(HUB_SOURCE, &[hub], 1)[0];
        fibers.push(setup.consumer(source, t, ALL));
    }
    setup.call(HUB_SEAL, &[hub], 0);
    setup.call(HUB_DROP, &[hub], 0);
    let scheduler = setup.scheduler(4);
    let fibers = run(&scheduler, fibers);
    let (p, c) = fibers.split_at(producers.len());
    (
        p.iter().map(|f| results(f)).collect(),
        c.iter().map(|f| results(f)).zip(taken).collect(),
    )
}

#[test]
fn a_fan_out_hands_each_value_to_one_consumer() {
    let (producers, consumers) = hub(HUB_FAN_OUT, 4, &[(300, true), (300, true)], 4);
    assert_eq!(producers, [[300, STREAM_OK], [300, STREAM_OK]]);
    let mut all = Vec::new();
    for ([count, status], taken) in &consumers {
        assert_eq!(*status, STREAM_CLOSED);
        all.extend_from_slice(taken.first(*count));
    }
    all.sort();
    let mut expected: Vec<u64> = one_to(300).into_iter().chain(one_to(300)).collect();
    expected.sort();
    assert_eq!(all, expected);
}

#[test]
fn a_fan_out_whose_producer_vanishes_ends_abandoned() {
    let (_, consumers) = hub(HUB_FAN_OUT, 2, &[(20, true), (20, false)], 2);
    let taken: u64 = consumers.iter().map(|(r, _)| r[0]).sum();
    assert_eq!(taken, 40);
    for ([_, status], _) in &consumers {
        assert_eq!(*status, STREAM_ABANDONED);
    }
}

#[test]
fn a_broadcast_hands_every_value_to_every_consumer() {
    for capacity in [0, 3] {
        let (producers, consumers) = hub(HUB_BROADCAST, capacity, &[(100, true)], 3);
        assert_eq!(producers, [[100, STREAM_OK]]);
        for ([count, status], taken) in &consumers {
            assert_eq!([*count, *status], [100, STREAM_CLOSED]);
            assert_eq!(taken.first(100), one_to(100));
        }
    }
}

#[test]
fn release_makes_waiting_consumers_read_closed() {
    let mut setup = Setup::new();
    let hub = setup.hub(4, HUB_FAN_OUT);
    let sink = setup.call(HUB_SINK, &[hub], 1)[0];
    let mut taken: Vec<Taken> = (0..3).map(|_| Taken::new(1)).collect();
    let consumers: Vec<Box<Fiber>> = taken
        .iter_mut()
        .map(|t| {
            let source = setup.call(HUB_SOURCE, &[hub], 1)[0];
            setup.consumer(source, t, ALL)
        })
        .collect();
    let scheduler = setup.scheduler(2);
    scheduler.spawn_all(consumers);
    std::thread::sleep(ms(30));
    setup.call(HUB_RELEASE, &[hub, 2], 0);
    std::thread::sleep(ms(30));
    // The third still waits; the producer leaving ends it.
    setup.call(HUB_DROP, &[hub], 0);
    setup.call(CLOSE, &[sink], 0);
    setup.call(DISPOSE, &[sink], 0);
    let stopped = scheduler.wait();
    assert_eq!(stopped.len(), 3);
    for fiber in &stopped {
        assert_eq!(results(fiber), [0, STREAM_CLOSED]);
    }
}

#[test]
fn a_sink_asked_for_after_the_seal_starts_closed() {
    let mut setup = Setup::new();
    let hub = setup.hub(4, HUB_FAN_OUT);
    setup.call(HUB_SEAL, &[hub], 0);
    let sink = setup.call(HUB_SINK, &[hub], 1)[0];
    assert_eq!(
        setup.call(TRY_PUTS, &[sink], 2),
        [STREAM_CLOSED, STREAM_CLOSED]
    );
    setup.call(DISPOSE, &[sink], 0);
    setup.call(HUB_DROP, &[hub], 0);
}

/// A box the test owns: a header whose count the runtime changes, which
/// never reaches zero, so the runtime never frees it.
#[repr(C, align(16))]
struct FakeBox {
    count: std::sync::atomic::AtomicU64,
    type_index: u64,
}

impl FakeBox {
    fn new() -> Box<FakeBox> {
        Box::new(FakeBox {
            count: std::sync::atomic::AtomicU64::new(1_000),
            type_index: 0,
        })
    }

    fn count(&self) -> u64 {
        self.count.load(std::sync::atomic::Ordering::SeqCst)
    }

    fn word(&self) -> u64 {
        std::ptr::from_ref(self) as u64
    }
}

#[test]
fn a_broadcast_gives_each_consumer_a_reference() {
    let fake = FakeBox::new();
    let mut setup = Setup::new();
    let hub = setup.hub_of(2, HUB_BROADCAST, BOXES);
    let sink = setup.call(HUB_SINK, &[hub], 1)[0];
    let mut fibers = vec![setup.putting(sink, 10, true, fake.word())];
    let mut taken: Vec<Taken> = (0..3).map(|_| Taken::new(11)).collect();
    for t in &mut taken {
        let source = setup.call(HUB_SOURCE, &[hub], 1)[0];
        fibers.push(setup.consumer(source, t, ALL));
    }
    setup.call(HUB_DROP, &[hub], 0);
    let scheduler = setup.scheduler(2);
    let fibers = run(&scheduler, fibers);
    for consumer in &fibers[1..] {
        assert_eq!(results(consumer), [10, STREAM_CLOSED]);
    }
    // Ten puts of a reference each, which three consumers hold: twenty
    // more, which the consumers, which keep the values, still hold.
    assert_eq!(fake.count(), 1_020);
}

#[test]
fn values_no_one_will_take_are_released() {
    let fake = FakeBox::new();
    let mut setup = Setup::new();
    let (sink, source) = setup.stream_of(4, BOXES);
    let producer = setup.putting(sink, 4, true, fake.word());
    let scheduler = setup.scheduler(1);
    assert_eq!(results(&run(&scheduler, vec![producer])[0]), [4, STREAM_OK]);
    // The consumer goes without taking the four in the buffer.
    setup.call(CLOSE, &[source], 0);
    setup.call(DISPOSE, &[source], 0);
    assert_eq!(fake.count(), 996);

    // With no consumer yet, a broadcast releases what is put.
    let hub = setup.hub_of(1, HUB_BROADCAST, BOXES);
    let sink = setup.call(HUB_SINK, &[hub], 1)[0];
    let producer = setup.putting(sink, 3, true, fake.word());
    let fibers = run(&scheduler, vec![producer]);
    assert_eq!(results(&fibers[0]), [3, STREAM_OK]);
    assert_eq!(fake.count(), 993);

    // Once the hub is dropped, no consumer can join: puts give `Closed`.
    let sink = setup.call(HUB_SINK, &[hub], 1)[0];
    setup.call(HUB_DROP, &[hub], 0);
    let producer = setup.putting(sink, 3, true, fake.word());
    let fibers = run(&scheduler, vec![producer]);
    assert_eq!(results(&fibers[0]), [0, STREAM_CLOSED]);
    assert_eq!(fake.count(), 993);
}
