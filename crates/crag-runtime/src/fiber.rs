//! Fiber records, the context switch and the single-worker run loop (Plan §11.3.1).
//!
//! A fiber is a stack plus a saved stack pointer. Everything else a suspended
//! fiber needs, its registers and where to continue, lies on its own stack,
//! pushed there by the routine that suspended it. Switching is therefore
//! "push my registers, store my stack pointer, load the other stack pointer,
//! pop its registers, return".

use std::collections::VecDeque;
use std::io;
use std::mem::offset_of;
use std::sync::Arc;
use std::sync::atomic::{AtomicPtr, AtomicUsize, Ordering};

use crag_abi::{STACK_LIMIT_OFFSET, STACK_MARGIN};

use crate::stack::StackMemory;

/// The per-task record generated code receives as its implicit first
/// argument (Compiler Architecture §10). Generated code reads only
/// `stack_limit`; the assembly routines of this crate use the other fields
/// by offset.
///
/// The fields are atomics because another thread may request a stop, and
/// because the record is shared between the fiber and its stop handles.
#[repr(C)]
pub struct TaskContext {
    /// Compared with the stack pointer by every stack check.
    pub(crate) stack_limit: AtomicUsize,
    /// The worker running the fiber. The assembly routines find the system
    /// stack through it.
    pub(crate) worker: AtomicPtr<Worker>,
    /// The fiber's stack pointer while it is not running.
    pub(crate) saved_sp: AtomicUsize,
    /// Set to `STATUS_FINISHED` when the fiber's function has returned.
    pub(crate) status: AtomicUsize,
    /// Stop reasons that wait for the next stack check.
    pub(crate) pending: AtomicUsize,
    /// The fiber this context belongs to, while a worker runs it.
    pub(crate) fiber: AtomicPtr<Fiber>,
}

const _: () = assert!(offset_of!(TaskContext, stack_limit) == STACK_LIMIT_OFFSET as usize);

pub(crate) const STATUS_FINISHED: usize = 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FiberState {
    /// Ready to be resumed.
    Runnable,
    /// On a worker right now.
    Running,
    /// Stopped by a pause request; resuming continues it.
    Paused,
    /// Its function returned; the results are available.
    Finished,
}

/// How a fiber's stack starts and grows.
#[derive(Clone, Copy, Debug)]
pub struct FiberConfig {
    /// Usable bytes of the first stack, rounded up to whole pages.
    pub initial_stack: usize,
    /// Growth beyond this many bytes ends the process with a stack overflow.
    pub max_stack: usize,
    /// Stress mode (Plan §11.3.9): the stack limit is kept so tight that
    /// every call fails its check, and every failure moves the stack to a
    /// fresh mapping and verifies the frame-pointer chain.
    pub torture: bool,
}

impl FiberConfig {
    pub const fn normal() -> FiberConfig {
        FiberConfig {
            initial_stack: 4096,
            max_stack: 1 << 30,
            torture: false,
        }
    }

    pub const fn tortured() -> FiberConfig {
        FiberConfig {
            torture: true,
            ..FiberConfig::normal()
        }
    }
}

impl Default for FiberConfig {
    /// The normal configuration, or the tortured one when the environment
    /// variable `CRAG_TORTURE` is set, so a whole test run can be stressed.
    fn default() -> FiberConfig {
        if std::env::var_os("CRAG_TORTURE").is_some() {
            FiberConfig::tortured()
        } else {
            FiberConfig::normal()
        }
    }
}

/// A task with its own stack.
pub struct Fiber {
    pub(crate) ctx: Arc<TaskContext>,
    pub(crate) stack: StackMemory,
    /// The limit generated code checks against, kept here because
    /// `ctx.stack_limit` may hold the sentinel instead.
    pub(crate) limit: usize,
    pub(crate) state: FiberState,
    pub(crate) config: FiberConfig,
    pub(crate) growths: u64,
    /// The function's arguments and results. They live on the heap, not on
    /// the fiber stack, so the entry stub's pointers to them survive growth.
    _args: Box<[u64]>,
    results: Box<[u64; 2]>,
}

impl Fiber {
    /// Creates a fiber that will call the Crag function at `func` with
    /// `args`, through the entry stub at `stub`.
    ///
    /// # Safety
    ///
    /// `stub` must be the entry of a stub from `compile_entry_stub` and
    /// `func` the entry of a function compiled by the facade, both loaded and
    /// kept loaded while the fiber exists. The stub's parameter count must be
    /// `args.len()`, and both must agree on the number of results.
    pub unsafe fn new(
        stub: usize,
        func: usize,
        args: &[u64],
        config: FiberConfig,
    ) -> io::Result<Box<Fiber>> {
        let stack = StackMemory::new(config.initial_stack)?;
        let args: Box<[u64]> = args.into();
        let mut results = Box::new([0u64; 2]);
        let ctx = Arc::new(TaskContext {
            stack_limit: AtomicUsize::new(0),
            worker: AtomicPtr::new(std::ptr::null_mut()),
            saved_sp: AtomicUsize::new(0),
            status: AtomicUsize::new(0),
            pending: AtomicUsize::new(0),
            fiber: AtomicPtr::new(std::ptr::null_mut()),
        });

        // The first switch into the fiber pops six registers and returns, so
        // lay out what it will pop: the values `fiber_start` expects in
        // callee-saved registers, then `fiber_start` as the return address.
        // Sixteen bytes stay free above, so the stack is aligned as the C
        // calling convention requires when `fiber_start` makes its call.
        let frame: [usize; 7] = [
            args.as_ptr() as usize,            // r15: third stub argument
            func,                              // r14: second stub argument
            Arc::as_ptr(&ctx) as usize,        // r13: the task context
            stub,                              // r12: the function to call
            results.as_mut_ptr() as usize,     // rbx: fourth stub argument
            0,                                 // rbp: ends the frame-pointer chain
            fiber_start as *const () as usize, // return address
        ];
        let sp = stack.top() - 16 - size_of_val(&frame);
        // SAFETY: the stack is at least a page, freshly mapped and writable,
        // and the frame lies just below its top.
        unsafe { (sp as *mut [usize; 7]).write(frame) };
        ctx.saved_sp.store(sp, Ordering::Relaxed);

        // In stress mode start with a limit no frame passes, so the very
        // first check already moves the stack.
        let limit = if config.torture {
            sp
        } else {
            stack.low() + STACK_MARGIN as usize
        };
        ctx.stack_limit.store(limit, Ordering::Relaxed);

        Ok(Box::new(Fiber {
            ctx,
            stack,
            limit,
            state: FiberState::Runnable,
            config,
            growths: 0,
            _args: args,
            results,
        }))
    }

    pub fn state(&self) -> FiberState {
        self.state
    }

    /// The function's results, once the fiber has finished. A function with
    /// fewer than two results leaves the rest zero.
    pub fn results(&self) -> Option<[u64; 2]> {
        (self.state == FiberState::Finished).then_some(*self.results)
    }

    /// How often the stack has moved to a new mapping.
    pub fn growths(&self) -> u64 {
        self.growths
    }

    /// Usable bytes of the current stack.
    pub fn stack_size(&self) -> usize {
        self.stack.size()
    }
}

/// A thread that runs fibers. The thread's own stack is the system stack:
/// the worker's loop runs on it, and so does all runtime code a fiber calls.
#[repr(C)]
pub struct Worker {
    /// The system stack pointer while a fiber runs. The assembly routines
    /// load it to switch back, so it must stay the first field.
    sp: usize,
    queue: VecDeque<Box<Fiber>>,
}

const _: () = assert!(offset_of!(Worker, sp) == 0);

impl Default for Worker {
    fn default() -> Worker {
        Worker::new()
    }
}

impl Worker {
    pub fn new() -> Worker {
        Worker {
            sp: 0,
            queue: VecDeque::new(),
        }
    }

    /// Runs the fiber until it finishes or stops, and returns its new state:
    /// `Finished`, `Paused`, or `Runnable` after a preemption.
    pub fn resume(&mut self, fiber: &mut Fiber) -> FiberState {
        assert!(
            matches!(fiber.state, FiberState::Runnable | FiberState::Paused),
            "resumed a fiber that is {:?}",
            fiber.state
        );
        // While the fiber runs, the runtime reaches both records through
        // these pointers, so derive them once and use nothing else until the
        // switch returns.
        let worker: *mut Worker = self;
        let fiber: *mut Fiber = fiber;
        // SAFETY: both pointers come from live exclusive references. The
        // switch saves this context on the system stack and continues the
        // fiber at its saved stack pointer, which `Fiber::new` or the routine
        // that suspended the fiber left pointing at a switch frame. It
        // returns when the fiber switches back.
        unsafe {
            let ctx = Arc::as_ptr(&(*fiber).ctx);
            (*ctx).fiber.store(fiber, Ordering::Relaxed);
            (*ctx).worker.store(worker, Ordering::Relaxed);
            (*fiber).state = FiberState::Running;

            switch(
                &raw mut (*worker).sp,
                (*ctx).saved_sp.load(Ordering::Relaxed),
            );

            (*ctx).worker.store(std::ptr::null_mut(), Ordering::Relaxed);
            (*ctx).fiber.store(std::ptr::null_mut(), Ordering::Relaxed);
            if (*ctx).status.load(Ordering::Relaxed) == STATUS_FINISHED {
                (*fiber).state = FiberState::Finished;
            }
            (*fiber).state
        }
    }

    /// Adds a fiber to the run queue.
    pub fn spawn(&mut self, fiber: Box<Fiber>) {
        self.queue.push_back(fiber);
    }

    /// The run loop: resumes queued fibers in turn until none is runnable. A
    /// preempted fiber goes to the back of the queue. Returns the fibers that
    /// finished or paused, in that order.
    pub fn run(&mut self) -> Vec<Box<Fiber>> {
        let mut stopped = Vec::new();
        while let Some(mut fiber) = self.queue.pop_front() {
            match self.resume(&mut fiber) {
                FiberState::Runnable => self.queue.push_back(fiber),
                _ => stopped.push(fiber),
            }
        }
        stopped
    }
}

/// The context switch. Saves the callee-saved registers on the current
/// stack, stores the stack pointer to `*save_sp`, continues on the stack at
/// `to_sp` by popping the same registers and returning.
///
/// The caller-saved registers need no saving: this is an ordinary call for
/// the compiler, which already assumes they are lost.
///
/// # Safety
///
/// `to_sp` must point at a frame of six register values and a return
/// address, on a stack nothing else is running on.
#[unsafe(naked)]
unsafe extern "C" fn switch(save_sp: *mut usize, to_sp: usize) {
    std::arch::naked_asm!(
        "push rbp",
        "push rbx",
        "push r12",
        "push r13",
        "push r14",
        "push r15",
        "mov [rdi], rsp",
        "mov rsp, rsi",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
    )
}

/// Where a new fiber starts: the first switch "returns" here. Calls the
/// entry stub with the values `Fiber::new` placed in callee-saved registers.
/// When the stub returns, marks the fiber finished and switches to the
/// worker for the last time.
#[unsafe(naked)]
unsafe extern "C" fn fiber_start() {
    std::arch::naked_asm!(
        "mov rdi, r13",
        "mov rsi, r14",
        "mov rdx, r15",
        "mov rcx, rbx",
        "call r12",
        "mov qword ptr [r13 + {status}], {finished}",
        // Load the worker's stack pointer and pop what its `switch` pushed.
        "mov rax, [r13 + {worker}]",
        "mov rsp, [rax]",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
        status = const offset_of!(TaskContext, status),
        worker = const offset_of!(TaskContext, worker),
        finished = const STATUS_FINISHED,
    )
}
