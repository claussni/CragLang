//! Runs generated code and observes the stack check: when it calls
//! `rt_morestack`, with which size, and that tail calls reuse their frame.
//!
//! The tests run on the test thread's own stack with a made-up limit, and a
//! hook stands in for `rt_morestack`. Growing a real fiber stack is the
//! runtime's test.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use crag_abi::{FRAME_BUDGET, RuntimeFn, STACK_LIMIT_SENTINEL};
use crag_codegen::{
    BinOp, Block, BlockId, CodeObject, CodegenError, CodegenSettings, Cond, FuncId, Inst,
    LirFunction, OptLevel, RelocTarget, StackCheck, Term, VReg, compile, compile_entry_stub,
    target_for,
};
use crag_loader::{CodeArena, SymbolTable, load_group};

const TRIPLE: &str = "x86_64-unknown-linux-gnu";

fn settings(opt: OptLevel) -> CodegenSettings {
    CodegenSettings {
        target: target_for(TRIPLE).unwrap(),
        opt,
    }
}

/// The test's task context. Generated code reads only `stack_limit`.
#[repr(C)]
struct Ctx {
    stack_limit: usize,
    /// How often the hook ran.
    calls: usize,
    /// The `needed` argument of the last call.
    last_needed: usize,
    /// On this call number the hook stores `new_limit`; zero means never.
    reset_on_call: usize,
    new_limit: usize,
}

impl Ctx {
    fn new(stack_limit: usize) -> Ctx {
        Ctx {
            stack_limit,
            calls: 0,
            last_needed: 0,
            reset_on_call: 0,
            new_limit: 0,
        }
    }
}

/// Stands in for `rt_morestack`, which must preserve every register: saves
/// the registers the C calling convention lets `morestack_hook` clobber. The
/// tests compute with integers only, so vector registers are left alone.
#[unsafe(naked)]
extern "C" fn morestack_stub() {
    // Nine pushes after the return address leave the stack 16-byte aligned.
    std::arch::naked_asm!(
        "push rax",
        "push rcx",
        "push rdx",
        "push rsi",
        "push rdi",
        "push r8",
        "push r9",
        "push r10",
        "push r11",
        "call {hook}",
        "pop r11",
        "pop r10",
        "pop r9",
        "pop r8",
        "pop rdi",
        "pop rsi",
        "pop rdx",
        "pop rcx",
        "pop rax",
        "ret",
        hook = sym morestack_hook,
    )
}

extern "C" fn morestack_hook(ctx: *mut Ctx, needed: usize) {
    // SAFETY: generated code passes the context pointer it was given, which
    // points to the `Ctx` that `run` borrows mutably for the whole call.
    let ctx = unsafe { &mut *ctx };
    ctx.calls += 1;
    ctx.last_needed = needed;
    if ctx.calls == ctx.reset_on_call {
        ctx.stack_limit = ctx.new_limit;
    }
}

/// Code objects loaded into an arena. `FuncId(i)` resolves to the i-th
/// object.
struct Image {
    entries: Vec<usize>,
    /// Keeps the code mapped.
    _arena: CodeArena,
}

fn load(objects: &[&CodeObject]) -> Image {
    let mut arena = CodeArena::new(1 << 20).unwrap();
    let mut symbols = SymbolTable::new();
    symbols.define_runtime(RuntimeFn::Morestack, morestack_stub as *const () as usize);
    let group: Vec<_> = (0..).map(FuncId).zip(objects.iter().copied()).collect();
    let entries = load_group(&mut arena, &mut symbols, &group).unwrap();
    Image {
        entries: entries.iter().map(|e| e.addr()).collect(),
        _arena: arena,
    }
}

/// Calls `image.entries[func]` through `image.entries[stub]`.
fn run(image: &Image, stub: usize, func: usize, ctx: &mut Ctx, args: &[u64]) -> [u64; 2] {
    type Stub = extern "C" fn(*mut Ctx, usize, *const u64, *mut u64);
    let mut results = [0u64; 2];
    // SAFETY: the address is the entry of a stub from `compile_entry_stub`,
    // which has this signature, and the callers pass as many arguments as the
    // stub and function were compiled for.
    unsafe {
        let stub: Stub = std::mem::transmute(image.entries[stub]);
        stub(
            ctx,
            image.entries[func],
            args.as_ptr(),
            results.as_mut_ptr(),
        );
    }
    results
}

/// An address near the current stack pointer.
#[inline(never)]
fn stack_address() -> usize {
    let marker = 0u8;
    std::hint::black_box(&marker) as *const u8 as usize
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

/// `f(n) = n + (n - 1) + ... + 1`, as a loop with a poll on the back-edge.
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

/// `f(n, acc) = if n == 0 { acc } else { f(n - 1, acc + n) }`, calling itself
/// as `FuncId(self_id)` in tail position.
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

/// `f(p) = callee(p, p) + callee(p, 0) + ... + callee(p, live - 1)`, with
/// every term computed before the sum starts, so `live` call results stay in
/// the frame across the later calls. Results of calls are used because the
/// backend recomputes plain arithmetic at its use instead of keeping it.
fn wide_fn(live: u32, callee: u32) -> LirFunction {
    let tmp = live + 1;
    let acc = live + 2;
    let mut insts = Vec::new();
    for i in 0..live {
        insts.push(Inst::Const {
            dst: r(tmp),
            value: i64::from(i),
        });
        insts.push(Inst::Call {
            func: FuncId(callee),
            args: vec![r(0), r(tmp)],
            dsts: vec![r(1 + i)],
        });
    }
    insts.push(Inst::Call {
        func: FuncId(callee),
        args: vec![r(0), r(0)],
        dsts: vec![r(acc)],
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

fn wide_expected(live: u64, p: u64) -> u64 {
    2 * p + live * p + live * (live - 1) / 2
}

#[test]
fn passing_check_does_not_enter_the_runtime() {
    let s = settings(OptLevel::None);
    let add = compile(&add_fn(), &s).unwrap();
    assert_eq!(add.stack_check, StackCheck::Margin);
    assert!(add.footprint <= FRAME_BUDGET);
    let stub = compile_entry_stub(2, 1, &s).unwrap();
    let image = load(&[&add, &stub]);

    let mut ctx = Ctx::new(0);
    assert_eq!(run(&image, 1, 0, &mut ctx, &[40, 2])[0], 42);
    assert_eq!(ctx.calls, 0);
}

#[test]
fn sentinel_forces_the_entry_check_into_the_runtime() {
    let s = settings(OptLevel::None);
    let add = compile(&add_fn(), &s).unwrap();
    let stub = compile_entry_stub(2, 1, &s).unwrap();
    let image = load(&[&add, &stub]);

    let mut ctx = Ctx::new(STACK_LIMIT_SENTINEL);
    assert_eq!(run(&image, 1, 0, &mut ctx, &[40, 2])[0], 42);
    assert_eq!(ctx.calls, 1);
    assert_eq!(ctx.last_needed, 0);
}

#[test]
fn poll_checks_on_every_iteration() {
    for opt in [OptLevel::None, OptLevel::Speed] {
        let s = settings(opt);
        let sum = compile(&sum_loop_fn(), &s).unwrap();
        let stub = compile_entry_stub(1, 1, &s).unwrap();
        let image = load(&[&sum, &stub]);

        // A limit that passes: no calls.
        let mut ctx = Ctx::new(0);
        assert_eq!(run(&image, 1, 0, &mut ctx, &[10])[0], 55);
        assert_eq!(ctx.calls, 0);

        // The sentinel stays: once at entry, once per iteration.
        let mut ctx = Ctx::new(STACK_LIMIT_SENTINEL);
        assert_eq!(run(&image, 1, 0, &mut ctx, &[10])[0], 55);
        assert_eq!(ctx.calls, 11);

        // The runtime restores the limit at the third poll: the loop reads
        // the limit afresh, so the remaining iterations pass.
        let mut ctx = Ctx::new(STACK_LIMIT_SENTINEL);
        ctx.reset_on_call = 4;
        assert_eq!(run(&image, 1, 0, &mut ctx, &[10])[0], 55);
        assert_eq!(ctx.calls, 4);
    }
}

#[test]
fn tail_calls_do_not_grow_the_stack() {
    for opt in [OptLevel::None, OptLevel::Speed] {
        let s = settings(opt);
        let countdown = compile(&countdown_fn(0), &s).unwrap();
        let stub = compile_entry_stub(2, 1, &s).unwrap();
        let image = load(&[&countdown, &stub]);

        // A million frames would need far more than 64 KiB.
        let n = 1_000_000u64;
        let mut ctx = Ctx::new(stack_address() - 64 * 1024);
        assert_eq!(run(&image, 1, 0, &mut ctx, &[n, 0])[0], n * (n + 1) / 2);
        assert_eq!(ctx.calls, 0);
    }
}

#[test]
fn large_frame_gets_the_sized_check() {
    let s = settings(OptLevel::None);
    let live = 600u32;
    let wide = compile(&wide_fn(live, 1), &s).unwrap();
    let add = compile(&add_fn(), &s).unwrap();
    let stub = compile_entry_stub(1, 1, &s).unwrap();
    let image = load(&[&wide, &add, &stub]);

    let StackCheck::Sized { needed } = wide.stack_check else {
        panic!("expected the sized check, got {:?}", wide.stack_check);
    };
    assert_eq!(needed, wide.footprint);
    assert!(
        needed >= live * 8,
        "{live} live words need more than {needed} bytes"
    );
    // The wrapper comes first and reaches the body through a local reloc.
    assert_eq!(wide.entry, 0);
    assert!(
        wide.relocs
            .iter()
            .any(|r| matches!(r.target, RelocTarget::Local(off) if off > 0))
    );

    // Plenty of stack: neither check fails.
    let mut ctx = Ctx::new(0);
    assert_eq!(
        run(&image, 2, 0, &mut ctx, &[7])[0],
        wide_expected(live.into(), 7)
    );
    assert_eq!(ctx.calls, 0);

    // A limit 2 KiB below here: the wrapper's own frame fits, the body's does
    // not, so the wrapper asks for the body's footprint. The hook then
    // "grows" the stack by lowering the limit.
    let mut ctx = Ctx::new(stack_address() - 2048);
    ctx.reset_on_call = 1;
    assert_eq!(
        run(&image, 2, 0, &mut ctx, &[7])[0],
        wide_expected(live.into(), 7)
    );
    assert_eq!(ctx.calls, 1);
    assert_eq!(ctx.last_needed, needed as usize);

    // The sentinel fails the sized check too.
    let mut ctx = Ctx::new(STACK_LIMIT_SENTINEL);
    ctx.reset_on_call = 1;
    assert_eq!(
        run(&image, 2, 0, &mut ctx, &[7])[0],
        wide_expected(live.into(), 7)
    );
    assert_eq!(ctx.calls, 1);
    assert_eq!(ctx.last_needed, needed as usize);
}

#[test]
fn tail_call_with_more_arguments_counts_toward_the_footprint() {
    let s = settings(OptLevel::None);
    // callee(a0..a11) = a0 + ... + a11; twelve arguments do not fit in
    // registers.
    let mut insts = vec![Inst::Const {
        dst: r(12),
        value: 0,
    }];
    for i in 0..12 {
        insts.push(Inst::Bin {
            op: BinOp::Add,
            dst: r(12),
            a: r(12),
            b: r(i),
        });
    }
    let callee = LirFunction {
        params: 12,
        returns: 1,
        vregs: 13,
        blocks: vec![Block {
            insts,
            term: Term::Return(vec![r(12)]),
        }],
    };
    // caller(a) = callee(a, a, ..., a) in tail position.
    let caller = LirFunction {
        params: 1,
        returns: 1,
        vregs: 1,
        blocks: vec![Block {
            insts: vec![],
            term: Term::TailCall {
                func: FuncId(1),
                args: vec![r(0); 12],
            },
        }],
    };
    let plain = compile(&add_fn(), &s).unwrap();
    let caller = compile(&caller, &s).unwrap();
    let callee = compile(&callee, &s).unwrap();
    assert!(caller.footprint >= plain.footprint + 13 * 8);
    let stub = compile_entry_stub(1, 1, &s).unwrap();
    let image = load(&[&caller, &callee, &stub]);

    let mut ctx = Ctx::new(0);
    assert_eq!(run(&image, 2, 0, &mut ctx, &[5])[0], 60);
    assert_eq!(ctx.calls, 0);
}

#[test]
fn malformed_input_is_rejected() {
    let s = settings(OptLevel::None);
    let mut three_results = add_fn();
    three_results.returns = 3;
    assert!(matches!(
        compile(&three_results, &s),
        Err(CodegenError::InvalidLir(_))
    ));

    let mut bad_register = add_fn();
    bad_register.vregs = 2;
    assert!(matches!(
        compile(&bad_register, &s),
        Err(CodegenError::InvalidLir(_))
    ));

    assert!(target_for("pdp11-unknown-none").is_err());
}
