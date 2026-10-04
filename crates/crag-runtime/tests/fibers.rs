//! Runs generated code on fibers: completion, stack growth by copying, tail
//! calls, and stop requests through the sentinel. The last test is the M0
//! exit criterion.

use std::time::Duration;

use crag_abi::{FuncId, RuntimeFn, StackCheck};
use crag_codegen::{
    BinOp, Block, BlockId, CodeObject, CodegenSettings, Cond, Inst, LirFunction, OptLevel, Term,
    VReg, compile, compile_entry_stub, target_for,
};
use crag_loader::{CodeArena, SymbolTable, load, load_group};
use crag_runtime::stress::run_tortured;
use crag_runtime::{Fiber, FiberConfig, FiberState, StopReason, Worker, request_stop};

/// Loaded functions; `FuncId(i)` is the i-th.
struct Image {
    functions: Vec<usize>,
    arena: CodeArena,
    symbols: SymbolTable,
    settings: CodegenSettings,
}

impl Image {
    fn new(functions: &[LirFunction]) -> Image {
        let settings = CodegenSettings {
            target: target_for("x86_64-unknown-linux-gnu").unwrap(),
            opt: OptLevel::None,
        };
        let objects: Vec<CodeObject> = functions
            .iter()
            .map(|f| compile(f, &settings).unwrap())
            .collect();
        let mut arena = CodeArena::new(1 << 20).unwrap();
        let mut symbols = SymbolTable::new();
        symbols.define_runtime(
            RuntimeFn::Morestack,
            crag_runtime::runtime_fn_addr(RuntimeFn::Morestack),
        );
        let group: Vec<_> = (0..).map(FuncId).zip(&objects).collect();
        let entries = load_group(&mut arena, &mut symbols, &group).unwrap();
        Image {
            functions: entries.iter().map(|e| e.addr()).collect(),
            arena,
            symbols,
            settings,
        }
    }

    /// A fiber that will call function `func` with `args`, expecting one
    /// result.
    fn fiber(&mut self, func: usize, args: &[u64], config: FiberConfig) -> Box<Fiber> {
        let stub = compile_entry_stub(args.len() as u32, 1, &self.settings).unwrap();
        let stub = load(&mut self.arena, &self.symbols, &stub).unwrap();
        // SAFETY: the stub was compiled for this argument count and one
        // result, like every function in these tests, and the image outlives
        // the fiber in each test.
        unsafe { Fiber::new(stub.addr(), self.functions[func], args, config).unwrap() }
    }
}

fn r(i: u32) -> VReg {
    VReg(i)
}

/// `f(a, b) = a + b`
fn add_fn() -> LirFunction {
    LirFunction {
        params: 2,
        returns: 1,
        vregs: 3,
        blocks: vec![Block {
            insts: vec![Inst::Bin {
                op: BinOp::Add,
                dst: r(2),
                a: r(0),
                b: r(1),
            }],
            term: Term::Return(vec![r(2)]),
        }],
    }
}

/// `f(n) = if n == 0 { 0 } else { n * n + f(n - 1) }`: not a tail call, and
/// `n` must survive in the frame across the recursive call.
fn sum_squares_fn(self_id: u32) -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 6, // n, zero, flag, one, n - 1 / n * n, result
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
                        value: 1,
                    },
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(4),
                        a: r(0),
                        b: r(3),
                    },
                    Inst::Call {
                        func: FuncId(self_id),
                        args: vec![r(4)],
                        dsts: vec![r(5)],
                    },
                    Inst::Bin {
                        op: BinOp::Mul,
                        dst: r(4),
                        a: r(0),
                        b: r(0),
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: r(5),
                        a: r(5),
                        b: r(4),
                    },
                ],
                term: Term::Return(vec![r(5)]),
            },
        ],
    }
}

fn sum_squares(n: u64) -> u64 {
    n * (n + 1) * (2 * n + 1) / 6
}

/// `f(n, acc) = if n == 0 { acc } else { f(n - 1, acc + n) }` in tail position.
fn countdown_fn(self_id: u32) -> LirFunction {
    LirFunction {
        params: 2,
        returns: 1,
        vregs: 5, // n, acc, zero, one, flag
        blocks: vec![
            Block {
                insts: vec![
                    Inst::Const {
                        dst: r(2),
                        value: 0,
                    },
                    Inst::Cmp {
                        cond: Cond::Eq,
                        dst: r(4),
                        a: r(0),
                        b: r(2),
                    },
                ],
                term: Term::Branch {
                    cond: r(4),
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
                        value: 1,
                    },
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
                ],
                term: Term::TailCall {
                    func: FuncId(self_id),
                    args: vec![r(0), r(1)],
                },
            },
        ],
    }
}

/// `f(n) = n + (n - 1) + ... + 1` as a loop with a poll on the back-edge.
fn sum_loop_fn() -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 5, // n, acc, zero, one, flag
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
                insts: vec![
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
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![],
                term: Term::Return(vec![r(1)]),
            },
        ],
    }
}

/// `f(p) = add(p, 0) + ... + add(p, live - 1)`, with every term kept in the
/// frame until the sum, so the frame exceeds the budget.
fn wide_fn(live: u32, add: u32) -> LirFunction {
    let tmp = live + 1;
    let acc = live + 2;
    let mut insts = Vec::new();
    for i in 0..live {
        insts.push(Inst::Const {
            dst: r(tmp),
            value: i64::from(i),
        });
        insts.push(Inst::Call {
            func: FuncId(add),
            args: vec![r(0), r(tmp)],
            dsts: vec![r(1 + i)],
        });
    }
    insts.push(Inst::Const {
        dst: r(acc),
        value: 0,
    });
    for i in 0..live {
        insts.push(Inst::Bin {
            op: BinOp::Add,
            dst: r(acc),
            a: r(acc),
            b: r(1 + i),
        });
    }
    LirFunction {
        params: 1,
        returns: 1,
        vregs: live + 3,
        blocks: vec![Block {
            insts,
            term: Term::Return(vec![r(acc)]),
        }],
    }
}

fn finish(fiber: &mut Fiber) -> u64 {
    assert_eq!(Worker::new().resume(fiber), FiberState::Finished);
    fiber.results().unwrap()[0]
}

#[test]
fn a_fiber_runs_a_function_to_completion() {
    let mut image = Image::new(&[add_fn()]);
    let mut fiber = image.fiber(0, &[40, 2], FiberConfig::default());
    assert_eq!(fiber.state(), FiberState::Runnable);
    assert_eq!(fiber.results(), None);
    assert_eq!(finish(&mut fiber), 42);
}

#[test]
fn deep_recursion_grows_the_stack_by_doubling() {
    let mut image = Image::new(&[sum_squares_fn(0)]);
    let mut fiber = image.fiber(0, &[100_000], FiberConfig::normal());
    assert_eq!(fiber.stack_size(), 4096);
    assert_eq!(finish(&mut fiber), sum_squares(100_000));
    // 100,000 frames need megabytes; doubling gets there in a few steps.
    assert!(
        fiber.stack_size() >= 1 << 21,
        "stack is {} bytes",
        fiber.stack_size()
    );
    assert!(
        (9..=16).contains(&fiber.growths()),
        "{} growths",
        fiber.growths()
    );
}

#[test]
fn a_frame_over_the_budget_grows_the_stack_before_it_is_allocated() {
    let functions = [wide_fn(600, 1), add_fn()];
    let wide = compile(&functions[0], &Image::new(&[]).settings).unwrap();
    assert!(matches!(wide.stack_check, StackCheck::Sized { needed } if needed > 4096));

    for config in [FiberConfig::normal(), FiberConfig::tortured()] {
        let mut image = Image::new(&functions);
        // The frame alone is larger than the first stack.
        let mut fiber = image.fiber(0, &[7], config);
        assert_eq!(finish(&mut fiber), 600 * 7 + 599 * 600 / 2);
        assert!(fiber.growths() >= 1);
    }
}

#[test]
fn a_pause_request_stops_the_fiber_at_its_next_check() {
    let mut image = Image::new(&[sum_loop_fn()]);
    let mut worker = Worker::new();
    let mut fiber = image.fiber(0, &[1000], FiberConfig::default());

    // Requested before the fiber runs: it stops at the entry check.
    request_stop(&fiber, StopReason::Pause);
    assert_eq!(worker.resume(&mut fiber), FiberState::Paused);
    assert_eq!(fiber.results(), None);

    // Requested again while paused: it stops at the first loop poll.
    request_stop(&fiber, StopReason::Pause);
    assert_eq!(worker.resume(&mut fiber), FiberState::Paused);

    assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
    assert_eq!(fiber.results().unwrap()[0], 500_500);
}

#[test]
fn another_thread_can_pause_a_running_loop() {
    let mut image = Image::new(&[sum_loop_fn()]);
    // Far too many iterations to finish: only the pause ends this resume.
    let mut fiber = image.fiber(0, &[u64::MAX >> 1], FiberConfig::default());
    let handle = fiber.stop_handle();
    let stopper = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(20));
        handle.request_stop(StopReason::Pause);
    });
    assert_eq!(Worker::new().resume(&mut fiber), FiberState::Paused);
    stopper.join().unwrap();
}

#[test]
fn the_run_loop_gives_preempted_fibers_another_turn() {
    let mut image = Image::new(&[sum_loop_fn(), sum_squares_fn(1)]);
    let mut worker = Worker::new();
    let first = image.fiber(0, &[100], FiberConfig::default());
    let second = image.fiber(1, &[100], FiberConfig::default());
    let paused = image.fiber(0, &[5], FiberConfig::default());
    request_stop(&first, StopReason::Preempt);
    request_stop(&second, StopReason::Preempt);
    request_stop(&paused, StopReason::Pause);
    worker.spawn(first);
    worker.spawn(second);
    worker.spawn(paused);

    // The paused fiber leaves the queue first; the preempted ones come back
    // and finish in their order.
    let stopped = worker.run();
    let states: Vec<_> = stopped.iter().map(|f| f.state()).collect();
    assert_eq!(
        states,
        [
            FiberState::Paused,
            FiberState::Finished,
            FiberState::Finished
        ]
    );
    assert_eq!(stopped[1].results().unwrap()[0], 5050);
    assert_eq!(stopped[2].results().unwrap()[0], sum_squares(100));
}

/// The M0 exit criterion: a hand-written function runs on a fiber, grows its
/// stack a thousand times, and tail-calls without stack growth.
#[test]
fn m0_exit() {
    run_tortured(|config| {
        let mut image = Image::new(&[sum_squares_fn(0), countdown_fn(1)]);

        // Tortured, every call moves the stack: a thousand nested calls are
        // a thousand growths, and each frame's `n` must arrive intact.
        let mut fiber = image.fiber(0, &[1000], config);
        assert_eq!(finish(&mut fiber), sum_squares(1000));
        assert!(fiber.growths() >= 1000, "{} growths", fiber.growths());

        // A tail call replaces its frame, so a million of them use exactly
        // the stack that one does.
        let mut one = image.fiber(1, &[1, 0], config);
        assert_eq!(finish(&mut one), 1);
        let mut million = image.fiber(1, &[1_000_000, 0], config);
        assert_eq!(finish(&mut million), 500_000_500_000);
        assert_eq!(million.growths(), one.growths());
        assert_eq!(million.stack_size(), one.stack_size());
    });
}
