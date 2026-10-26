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

//! Scopes (Plan §11.7.3): the tasks a combinator or group starts, which
//! never outlive it (Specification Chapter 10).
//!
//! A scope belongs to the fiber that creates it, its parent. Its tasks are
//! fibers that call a function value, started by the parent or by the
//! scope's own tasks, as a group's body starts them, and each knows its
//! scope and its index there. They go on the deque of the worker that
//! starts them. When a task stops, its worker hands it to the scope, which
//! keeps its results and wakes the parent if it waits. The parent takes the
//! tasks one at a time, in the order they finished, until none is left;
//! what a combinator does with each, keep it, give it back or cancel the
//! rest, is the generated code's to decide, since only it knows the types.
//!
//! A task that traps cancels the others, and once all are taken the parent
//! traps with its kind (§10.4). From its start to its end the parent is in
//! a region where cancellation waits: cancelling it cancels the scope's
//! tasks instead, and the parent stops at the scope's end (§11.7.4).
//!
//! With a limit, a task that would exceed it waits, with the fiber that
//! started it, until a running one finishes. A task started cancelled
//! never waits: it unwinds at its first check, which releases the function
//! value it was given.

use std::collections::VecDeque;
use std::sync::atomic::Ordering;
use std::sync::{Arc, Mutex};

use crag_abi::{SCOPE_DONE, START_EXEMPT, TASK_CANCELLED, TASK_RETURNED, TASK_TRAPPED, TrapKind};

use crate::cancel::{self, Waiting, leave_region, raise, stop_if_due, wait_for, waited};
use crate::die;
use crate::fiber::{Fiber, FiberConfig, FiberState, TaskContext, Worker};
use crate::io::Words;
use crate::sched::{FiberRef, Local, Shared, WaitReason, local_of, scheduler_of, suspend, wake};

/// The tasks one combinator or group started.
pub(crate) struct Scope {
    shared: Arc<Shared>,
    /// The parent's context, by address.
    parent: usize,
    /// The most counted tasks that run at once; zero for no limit.
    limit: usize,
    /// How the tasks' stacks start and grow: as the parent's.
    config: FiberConfig,
    /// The entry stubs of the image, by the number of results.
    entries: [usize; 3],
    state: Mutex<State>,
}

// SAFETY: the fibers the scope holds are queued tasks that have never
// run, and the lock hands them to one thread at a time; the starters are
// suspended fibers, which `FiberRef` lets any thread wake.
unsafe impl Send for Scope {}
unsafe impl Sync for Scope {}

struct State {
    /// Every task started, by index.
    tasks: Vec<Task>,
    /// Counted tasks that run.
    counted: usize,
    /// Tasks started and not finished, those waiting for a place included.
    unfinished: usize,
    /// Tasks that finished and that the parent has not taken, in the order
    /// they finished.
    done: VecDeque<usize>,
    /// The parent, while it waits for a task to finish.
    waiter: Option<FiberRef>,
    /// Tasks waiting for a place under the limit, oldest first.
    queued: VecDeque<Queued>,
    /// Set once the scope is cancelled: tasks started later are too.
    cancelled: bool,
    /// The kind and position of the first trap of a task.
    trap: Option<(TrapKind, Option<u32>)>,
}

struct Task {
    ctx: Arc<TaskContext>,
    /// Whether it holds, or waits for, a place under the limit.
    counted: bool,
    outcome: Outcome,
}

enum Outcome {
    /// Waiting for a place, queued or running.
    Running,
    /// Its results until the parent takes them.
    Returned(Option<[u64; 2]>),
    Cancelled,
    Trapped,
}

/// A task waiting for a place under the limit.
struct Queued {
    index: usize,
    fiber: Box<Fiber>,
    /// The fiber that started it, suspended until it runs.
    starter: FiberRef,
}

/// What makes a fiber a task: its scope and its index there.
pub(crate) struct Member {
    scope: Arc<Scope>,
    index: usize,
}

/// What a cancellation leaves to do once the scope's lock is released.
#[derive(Default)]
struct Cancelling {
    tasks: Vec<Arc<TaskContext>>,
    queued: Vec<Queued>,
}

impl Scope {
    /// The scope behind the word generated code holds, as a reference of
    /// its own.
    ///
    /// # Safety
    ///
    /// `ptr` comes from `rt_scope_new`, and its scope has not ended.
    unsafe fn borrowed(ptr: *const Scope) -> Arc<Scope> {
        // SAFETY: as the caller promises, the word holds a reference.
        unsafe {
            Arc::increment_strong_count(ptr);
            Arc::from_raw(ptr)
        }
    }

    pub(crate) fn is_parent(&self, ctx: &TaskContext) -> bool {
        std::ptr::from_ref(ctx) as usize == self.parent
    }

    /// Cancels every task that has not finished and every task started
    /// from now on.
    pub(crate) fn cancel(&self) {
        let cancelling = self.cancel_locked(&mut self.state.lock().unwrap());
        self.finish(cancelling);
    }

    /// Marks the scope cancelled and takes what is to cancel: the running
    /// tasks, and the queued ones, which no longer wait for a place.
    fn cancel_locked(&self, state: &mut State) -> Cancelling {
        if state.cancelled {
            return Cancelling::default();
        }
        state.cancelled = true;
        let tasks = state
            .tasks
            .iter()
            .filter(|t| matches!(t.outcome, Outcome::Running))
            .map(|t| t.ctx.clone())
            .collect();
        let queued: Vec<Queued> = state.queued.drain(..).collect();
        for q in &queued {
            state.tasks[q.index].counted = false;
        }
        Cancelling { tasks, queued }
    }

    /// Cancels the tasks, and starts the queued ones, cancelled, waking
    /// the fibers that started them.
    fn finish(&self, cancelling: Cancelling) {
        for ctx in &cancelling.tasks {
            cancel::cancel(ctx);
        }
        for q in cancelling.queued {
            self.shared.launch(q.fiber, None);
            wake(q.starter, [q.index as u64, 0]);
        }
    }

    /// Calls off the wait of the fiber that started the queued task at
    /// `index`: the task starts cancelled, and the fiber is given back.
    /// None when the task no longer waits.
    pub(crate) fn call_off_start(&self, index: usize) -> Option<FiberRef> {
        let mut state = self.state.lock().unwrap();
        let at = state.queued.iter().position(|q| q.index == index)?;
        let q = state.queued.remove(at).expect("found");
        state.tasks[index].counted = false;
        drop(state);
        cancel::cancel(&q.fiber.ctx);
        self.shared.launch(q.fiber, None);
        Some(q.starter)
    }
}

impl Outcome {
    fn status(&self) -> u64 {
        match self {
            Outcome::Running => die("gave a task that runs"),
            Outcome::Returned(_) => TASK_RETURNED,
            Outcome::Cancelled => TASK_CANCELLED,
            Outcome::Trapped => TASK_TRAPPED,
        }
    }
}

/// Takes a task that stopped from the worker that ran it: records how it
/// ended, gives its place to a queued task, and wakes the parent if it
/// waits. A trap cancels the other tasks.
pub(crate) fn finished(mut fiber: Box<Fiber>, local: &mut Local) {
    let Member { scope, index } = fiber.task.take().expect("a task");
    let cancelled = fiber.ctx.cancel.load(Ordering::SeqCst) != 0;
    let (outcome, trap) = match (fiber.state, fiber.trap()) {
        (FiberState::Finished, _) => (Outcome::Returned(fiber.results()), None),
        (_, Some(t)) if t.kind == TrapKind::Cancelled && cancelled => (Outcome::Cancelled, None),
        (_, t) => (
            Outcome::Trapped,
            Some(t.map_or((TrapKind::Error, None), |t| (t.kind, t.position))),
        ),
    };
    drop(fiber);

    let mut state = scope.state.lock().unwrap();
    let task = &mut state.tasks[index];
    task.outcome = outcome;
    let counted = task.counted;
    state.unfinished -= 1;
    let mut cancelling = Cancelling::default();
    if let Some(trap) = trap {
        state.trap.get_or_insert(trap);
        cancelling = scope.cancel_locked(&mut state);
    }
    let mut next = None;
    if counted {
        state.counted -= 1;
        if let Some(q) = state.queued.pop_front() {
            state.counted += 1;
            next = Some(q);
        }
    }
    state.done.push_back(index);
    let parent = state.waiter.take().map(|waiter| {
        let i = state.done.pop_front().expect("pushed");
        (waiter, [i as u64, state.tasks[i].outcome.status()])
    });
    drop(state);

    scope.finish(cancelling);
    if let Some(q) = next {
        scope.shared.launch(q.fiber, Some(local));
        wake(q.starter, [q.index as u64, 0]);
    }
    if let Some((waiter, words)) = parent {
        wake(waiter, words);
    }
}

suspending_fn! {
    /// `rt_scope_new(ctx, limit) -> scope`: see `crag_abi::RuntimeFn::ScopeNew`.
    fn rt_scope_new(ctx: *const TaskContext, limit: u64) -> u64 => new_entry
}

/// The Rust half of `rt_scope_new`. It never suspends.
///
/// # Safety
///
/// Called only by `rt_scope_new`.
unsafe extern "C" fn new_entry(ctx: *const TaskContext, limit: u64) -> u64 {
    // SAFETY: as the caller promises, a worker runs the fiber of `ctx`.
    unsafe {
        let ctx = &*ctx;
        if stop_if_due(ctx) {
            return 0;
        }
        let Some(shared) = scheduler_of(ctx) else {
            raise(ctx, TrapKind::Unsupported, None);
            return 0;
        };
        let worker: *mut Worker = ctx.worker.load(Ordering::Relaxed);
        let entries = Worker::code(worker)
            .task_entries()
            .unwrap_or_else(|| die("the image gave no entry stubs for tasks"));
        let config = (*ctx.fiber.load(Ordering::Relaxed)).config;
        ctx.no_cancel.fetch_add(1, Ordering::Relaxed);
        let scope = Scope {
            shared,
            parent: std::ptr::from_ref(ctx) as usize,
            limit: limit as usize,
            config,
            entries,
            state: Mutex::new(State {
                tasks: Vec::new(),
                counted: 0,
                unfinished: 0,
                done: VecDeque::new(),
                waiter: None,
                queued: VecDeque::new(),
                cancelled: false,
                trap: None,
            }),
        };
        Arc::into_raw(Arc::new(scope)) as u64
    }
}

suspending_fn! {
    /// `rt_scope_start(ctx, scope, code, env, flags) -> index`: see
    /// `crag_abi::RuntimeFn::ScopeStart`.
    fn rt_scope_start(ctx: *const TaskContext, scope: *const Scope, code: u64, env: u64, flags: u64) -> u64 => start_entry
}

/// The Rust half of `rt_scope_start`: suspends while the limit is reached.
///
/// # Safety
///
/// Called only by `rt_scope_start`, with a scope that has not ended and
/// the code and environment of a function value that takes one
/// parameter, its environment, and has as many results as `flags` says.
unsafe extern "C" fn start_entry(
    ctx: *const TaskContext,
    scope: *const Scope,
    code: u64,
    env: u64,
    flags: u64,
) -> u64 {
    // SAFETY: as the caller promises.
    unsafe {
        let ctx = &*ctx;
        let scope = Scope::borrowed(scope);
        let stub = scope.entries[(flags & 3) as usize];
        let mut fiber = Fiber::new(stub, code as usize, &[env], scope.config)
            .unwrap_or_else(|_| die("out of memory for a task's stack"));
        // A cancelled starter that must stop still starts the task, which
        // owns the function value, but cancelled.
        let starter_stops = cancel::due(ctx);

        let mut state = scope.state.lock().unwrap();
        let mut cancelling = Cancelling::default();
        if scope.is_parent(ctx) && ctx.cancel.load(Ordering::SeqCst) != 0 {
            cancelling = scope.cancel_locked(&mut state);
        }
        let index = state.tasks.len();
        let cancelled = state.cancelled || starter_stops;
        let counted = flags & START_EXEMPT == 0 && !cancelled && scope.limit != 0;
        state.tasks.push(Task {
            ctx: fiber.ctx.clone(),
            counted,
            outcome: Outcome::Running,
        });
        state.unfinished += 1;
        fiber.task = Some(Member {
            scope: scope.clone(),
            index,
        });
        if counted && state.counted >= scope.limit {
            let starter = suspend(ctx, WaitReason::Start);
            state.queued.push_back(Queued {
                index,
                fiber,
                starter,
            });
            drop(state);
            scope.finish(cancelling);
            wait_for(ctx, Waiting::Start { scope, index });
            // The wake gives the index.
            return 0;
        }
        if counted {
            state.counted += 1;
        }
        drop(state);
        scope.finish(cancelling);
        if cancelled {
            cancel::cancel(&fiber.ctx);
        }
        scope.shared.launch(fiber, local_of(ctx));
        if starter_stops {
            raise(ctx, TrapKind::Cancelled, None);
        }
        index as u64
    }
}

suspending_fn! {
    /// `rt_scope_next(ctx, scope) -> (index, status)`: see
    /// `crag_abi::RuntimeFn::ScopeNext`.
    fn rt_scope_next(ctx: *const TaskContext, scope: *const Scope) -> Words => next_entry
}

/// The Rust half of `rt_scope_next`: suspends until a task finishes.
///
/// # Safety
///
/// Called only by `rt_scope_next`, by the parent of a scope that has not
/// ended. When a task trapped, the scope ends with the last call.
unsafe extern "C" fn next_entry(ctx: *const TaskContext, ptr: *const Scope) -> Words {
    // SAFETY: as the caller promises.
    unsafe {
        let ctx = &*ctx;
        let scope = Scope::borrowed(ptr);
        let mut state = scope.state.lock().unwrap();
        let mut cancelling = Cancelling::default();
        if ctx.cancel.load(Ordering::SeqCst) != 0 {
            cancelling = scope.cancel_locked(&mut state);
        }
        let words = if let Some(i) = state.done.pop_front() {
            Some(Words(i as u64, state.tasks[i].outcome.status()))
        } else if state.unfinished == 0 {
            if let Some((kind, position)) = state.trap {
                // The parent never reaches the scope's end, so its
                // reference ends here.
                raise(ctx, kind, position);
                waited(ctx);
                Arc::decrement_strong_count(ptr);
            }
            Some(Words(SCOPE_DONE, 0))
        } else {
            state.waiter = Some(suspend(ctx, WaitReason::Tasks));
            None
        };
        drop(state);
        scope.finish(cancelling);
        words.unwrap_or_else(|| {
            wait_for(ctx, Waiting::Tasks(scope));
            // The wake gives the task.
            Words(0, 0)
        })
    }
}

system_stack_fn! {
    /// `rt_scope_result(ctx, scope, index) -> (w0, w1)`: see
    /// `crag_abi::RuntimeFn::ScopeResult`.
    fn rt_scope_result(ctx: *const TaskContext, scope: *const Scope, index: u64) -> Words => result_entry
}

/// The Rust half of `rt_scope_result`.
///
/// # Safety
///
/// Called only by `rt_scope_result`, with a scope that has not ended and
/// the index of one of its tasks.
unsafe extern "C" fn result_entry(_: *const TaskContext, scope: *const Scope, index: u64) -> Words {
    // SAFETY: as the caller promises.
    let scope = unsafe { &*scope };
    let mut state = scope.state.lock().unwrap();
    match &mut state.tasks[index as usize].outcome {
        Outcome::Returned(results) => {
            let [a, b] = results
                .take()
                .unwrap_or_else(|| die("took a task's results twice"));
            Words(a, b)
        }
        _ => die("took the results of a task that did not return"),
    }
}

system_stack_fn! {
    /// `rt_scope_cancel(ctx, scope)`: see `crag_abi::RuntimeFn::ScopeCancel`.
    fn rt_scope_cancel(ctx: *const TaskContext, scope: *const Scope) => cancel_entry
}

/// The Rust half of `rt_scope_cancel`.
///
/// # Safety
///
/// Called only by `rt_scope_cancel`, with a scope that has not ended.
unsafe extern "C" fn cancel_entry(_: *const TaskContext, scope: *const Scope) {
    // SAFETY: as the caller promises.
    unsafe { (*scope).cancel() }
}

suspending_fn! {
    /// `rt_scope_end(ctx, scope)`: see `crag_abi::RuntimeFn::ScopeEnd`.
    fn rt_scope_end(ctx: *const TaskContext, scope: *const Scope) => end_entry
}

/// The Rust half of `rt_scope_end`. It never suspends.
///
/// # Safety
///
/// Called only by `rt_scope_end`, by the parent, with the scope its
/// `rt_scope_new` gave.
unsafe extern "C" fn end_entry(ctx: *const TaskContext, scope: *const Scope) {
    // SAFETY: as the caller promises; the parent's reference ends here.
    unsafe {
        let ctx = &*ctx;
        let scope = Arc::from_raw(scope);
        {
            let state = scope.state.lock().unwrap();
            if state.unfinished != 0 || !state.done.is_empty() {
                die("a scope ended before the parent took all its tasks");
            }
        }
        waited(ctx);
        drop(scope);
        leave_region(ctx);
    }
}
