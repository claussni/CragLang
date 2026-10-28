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

//! The scheduler (Plan §11.7.1): fibers that yield, many fibers over many
//! workers, stealing, parking and preemption.

use std::sync::Arc;
use std::time::Duration;

mod common;

use common::{Image, r};
use crag_abi::RuntimeFn;
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::{FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

/// `f(n) = n + (n - 1) + ... + 1`, yielding before each addition when
/// `yields` is set.
fn sum_fn(yields: bool) -> LirFunction {
    let mut body = vec![
        Inst::Bin {
            op: BinOp::Add,
            dst: r(1),
            a: r(1),
            b: r(0),
        },
        Inst::Bin {
            op: BinOp::Sub,
            dst: r(0),
            a: r(0),
            b: r(3),
        },
        Inst::Poll,
    ];
    if yields {
        body.insert(
            0,
            Inst::CallRuntime {
                func: RuntimeFn::Yield,
                args: vec![],
                dsts: vec![],
            },
        );
    }
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 5, // n, acc, zero, one, flag
        tracked: vec![],
        blocks: vec![
            Block {
                insts: vec![
                    Inst::Const {
                        dst: r(1),
                        value: 0,
                    },
                    Inst::Const {
                        dst: r(2),
                        value: 0,
                    },
                    Inst::Const {
                        dst: r(3),
                        value: 1,
                    },
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Gt,
                    dst: r(4),
                    a: r(0),
                    b: r(2),
                }],
                term: Term::Branch {
                    cond: r(4),
                    then: BlockId(2),
                    otherwise: BlockId(3),
                },
            },
            Block {
                insts: body,
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![],
                term: Term::Return(vec![r(1)]),
            },
        ],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

const SUM: usize = 0;
const YIELDING: usize = 1;

fn image() -> Image {
    Image::new(&[sum_fn(false), sum_fn(true)])
}

fn scheduler(image: &mut Image, workers: usize, slice: Option<Duration>) -> Scheduler {
    let code = Arc::new(std::mem::take(&mut image.code));
    Scheduler::new(
        SchedulerConfig { workers, slice },
        Arc::new(Types::default()),
        code,
    )
}

fn triangle(n: u64) -> u64 {
    n * (n + 1) / 2
}

#[test]
fn a_fiber_that_yields_lets_the_others_run_first() {
    let mut image = image();
    let mut worker = Worker::new();
    // Alone, a yielding fiber suspends at each yield and is woken at once,
    // so a resume ends as if it were preempted.
    let mut alone = image.fiber(YIELDING, &[3], FiberConfig::default());
    assert_eq!(worker.resume(&mut alone), FiberState::Runnable);
    worker.spawn(alone);
    worker.spawn(image.fiber(SUM, &[10], FiberConfig::default()));
    // The run loop puts it behind the other, which finishes first.
    let stopped = worker.run();
    let results: Vec<u64> = stopped.iter().map(|f| f.results().unwrap()[0]).collect();
    assert_eq!(results, [triangle(10), triangle(3)]);
}

#[test]
fn many_fibers_run_on_many_workers() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 4, None);
    for i in 0..400u64 {
        let func = if i % 2 == 0 { YIELDING } else { SUM };
        scheduler.spawn(image.fiber(func, &[i], FiberConfig::default()));
    }
    let stopped = scheduler.wait();
    assert_eq!(stopped.len(), 400);
    let mut results: Vec<u64> = stopped
        .iter()
        .map(|f| {
            assert_eq!(f.state(), FiberState::Finished);
            f.results().unwrap()[0]
        })
        .collect();
    results.sort_unstable();
    let mut expected: Vec<u64> = (0..400).map(triangle).collect();
    expected.sort_unstable();
    assert_eq!(results, expected);
    // Each yield is a resume of its own.
    let resumes: u64 = scheduler.stats().iter().map(|s| s.resumes).sum();
    let yields: u64 = (0..400).step_by(2).sum();
    assert_eq!(resumes, 400 + yields);
    // Waiting again returns nothing new.
    assert!(scheduler.wait().is_empty());
}

#[test]
fn idle_workers_steal_and_then_park() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2, None);
    // The first worker takes the long fiber and half the rest, which stay
    // in its deque while it runs the long one; the other runs the rest of
    // the global queue and then steals.
    let long = 300_000_000;
    let mut fibers = vec![image.fiber(SUM, &[long], FiberConfig::default())];
    for _ in 0..63 {
        fibers.push(image.fiber(SUM, &[1000], FiberConfig::default()));
    }
    scheduler.spawn_all(fibers);
    let stopped = scheduler.wait();
    assert_eq!(stopped.len(), 64);
    let short = stopped
        .iter()
        .filter(|f| f.results() == Some([triangle(1000), 0]));
    assert_eq!(short.count(), 63);
    let stats = scheduler.stats();
    assert!(stats.iter().map(|s| s.steals).sum::<u64>() > 0, "{stats:?}");
    // With nothing left, both park.
    std::thread::sleep(Duration::from_millis(50));
    assert!(scheduler.stats().iter().all(|s| s.parks > 0), "{stats:?}");
}

#[test]
fn a_long_fiber_is_preempted_so_a_short_one_finishes_first() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1, Some(Duration::from_millis(5)));
    let long = 300_000_000;
    scheduler.spawn(image.fiber(SUM, &[long], FiberConfig::default()));
    std::thread::sleep(Duration::from_millis(20));
    scheduler.spawn(image.fiber(SUM, &[10], FiberConfig::default()));
    let stopped = scheduler.wait();
    let results: Vec<u64> = stopped.iter().map(|f| f.results().unwrap()[0]).collect();
    assert_eq!(results, [triangle(10), triangle(long)]);
    // The long one came back after each preemption.
    assert!(scheduler.stats()[0].resumes > 2);
}

#[test]
fn dropping_the_scheduler_frees_what_it_still_holds() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2, None);
    for i in 0..10 {
        scheduler.spawn(image.fiber(YIELDING, &[i], FiberConfig::default()));
    }
    // Some may still be queued or stopped; dropping frees them all.
    drop(scheduler);
}
