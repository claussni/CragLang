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

//! Lazy cells (Plan §11.7.11, Specification §6.10): a value computed at
//! most once, by the first task that reads it, while the others wait.
//!
//! The runtime never calls Crag code, so it does not compute the value: a
//! read that finds the cell unstarted tells generated code to compute it
//! and to store it with `rt_lazy_set`. A read that finds it running
//! suspends until the value is stored, and one that finds it done gets the
//! value with references of its own.
//!
//! A task that stops while it computes a value leaves it to the others.
//! When it was cancelled, the computation is not the value's fault: the
//! task that waited longest computes it instead, or the next reader. When
//! it trapped, the cell keeps the trap, and every read traps alike
//! (§6.10). A task that reads a value it is computing itself would wait
//! forever: the read traps with `Cycle`, and so does the cell.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use crag_abi::{LAZY_DONE, LAZY_RUN, LAZY_TRAPPED, TrapKind};

use crate::cancel::{Waiting, raise, stop_if_due, wait_for};
use crate::fiber::TaskContext;
use crate::heap::Heap;
use crate::rc::{Types, release_value, retain_value};
use crate::sched::{FiberRef, WaitReason, scheduler_of, suspend, wake};
use crate::system::worker_of;

/// A lazy cell.
pub(crate) struct LazyCell {
    /// The list type whose elements the value is laid out as.
    list: u64,
    state: Mutex<State>,
}

// SAFETY: the places waiting reads write to belong to suspended fibers,
// and the lock hands them to one thread at a time.
unsafe impl Send for LazyCell {}
unsafe impl Sync for LazyCell {}

enum Phase {
    Unstarted,
    /// The task computing the value.
    Running(Arc<TaskContext>),
    Done([u64; 2]),
    Trapped(TrapKind),
}

struct State {
    phase: Phase,
    /// Reads waiting for the value, oldest first.
    waiters: VecDeque<Waiter>,
    next_token: u64,
}

struct Waiter {
    fiber: FiberRef,
    ctx: Arc<TaskContext>,
    /// Where the value, or the kind of the trap, goes.
    out: *mut u64,
    token: u64,
}

impl LazyCell {
    /// Writes the value, with references of its own, where a read asked
    /// for it.
    fn give(&self, types: &Types, out: *mut u64, words: [u64; 2]) {
        let mut words = words;
        // SAFETY: the cell holds the value's references; the place is the
        // reader's.
        unsafe {
            retain_value(words.as_mut_ptr().cast(), types.element_of(self.list));
            out.cast::<[u64; 2]>().write_unaligned(words);
        }
    }

    /// Calls off the wait with `token`, giving its fiber back; none when it
    /// no longer waits.
    pub(crate) fn call_off(&self, token: u64) -> Option<FiberRef> {
        let mut state = self.state.lock().unwrap();
        let at = state.waiters.iter().position(|w| w.token == token)?;
        state.waiters.remove(at).map(|w| w.fiber)
    }

    /// The computation of `ctx`'s task ended without a value: another
    /// computes it if the task was cancelled, else the cell keeps the trap.
    fn abandon(self: &Arc<LazyCell>, ctx: &TaskContext, kind: TrapKind) {
        let mut state = self.state.lock().unwrap();
        if !matches!(&state.phase, Phase::Running(runner) if std::ptr::eq(&**runner, ctx)) {
            return;
        }
        let mut wakes = Vec::new();
        if kind == TrapKind::Cancelled {
            state.phase = Phase::Unstarted;
            if let Some(next) = state.waiters.pop_front() {
                state.phase = Phase::Running(next.ctx.clone());
                next.ctx.lazy.lock().unwrap().push(self.clone());
                wakes.push((next.fiber, LAZY_RUN));
            }
        } else {
            state.phase = Phase::Trapped(kind);
            for w in state.waiters.drain(..) {
                // SAFETY: the place is the reader's.
                unsafe { w.out.write_unaligned(kind as u64) };
                wakes.push((w.fiber, LAZY_TRAPPED));
            }
        }
        drop(state);
        for (fiber, status) in wakes {
            wake(fiber, [status, 0]);
        }
    }
}

/// Leaves the values the task of `ctx` computes to the others, as it
/// stopped with a trap of `kind`, or finished without storing them.
pub(crate) fn stopped(ctx: &TaskContext, kind: Option<TrapKind>) {
    let cells = std::mem::take(&mut *ctx.lazy.lock().unwrap());
    for cell in cells {
        cell.abandon(ctx, kind.unwrap_or(TrapKind::Cancelled));
    }
}

/// The cell behind the word generated code holds, with a count of its
/// own.
///
/// # Safety
///
/// `lazy` came from `rt_lazy_new` and has not been freed.
unsafe fn share(lazy: *const LazyCell) -> Arc<LazyCell> {
    // SAFETY: as the caller promises.
    unsafe {
        Arc::increment_strong_count(lazy);
        Arc::from_raw(lazy)
    }
}

system_stack_fn! {
    /// `rt_lazy_new(ctx, list) -> lazy`: see `crag_abi::RuntimeFn::LazyNew`.
    fn rt_lazy_new(ctx: *const TaskContext, list: u64) -> u64 => new_entry
}

/// The Rust half of `rt_lazy_new`.
///
/// # Safety
///
/// Called only by `rt_lazy_new`.
unsafe extern "C" fn new_entry(_ctx: *const TaskContext, list: u64) -> u64 {
    let cell = LazyCell {
        list,
        state: Mutex::new(State {
            phase: Phase::Unstarted,
            waiters: VecDeque::new(),
            next_token: 0,
        }),
    };
    Arc::into_raw(Arc::new(cell)) as u64
}

suspending_fn! {
    /// `rt_lazy_get(ctx, lazy, out) -> status`: see
    /// `crag_abi::RuntimeFn::LazyGet`.
    fn rt_lazy_get(ctx: *const TaskContext, lazy: *const LazyCell, out: *mut u64) -> u64 => get_entry
}

/// The Rust half of `rt_lazy_get`: suspends while another task computes
/// the value.
///
/// # Safety
///
/// Called only by `rt_lazy_get`, with a cell that has not been freed and
/// room for two words at `out`.
unsafe extern "C" fn get_entry(
    ctx: *const TaskContext,
    lazy: *const LazyCell,
    out: *mut u64,
) -> u64 {
    // SAFETY: as the caller promises.
    let (ctx, cell, (_, types)) = unsafe { (&*ctx, share(lazy), worker_of(&*ctx)) };
    if stop_if_due(ctx) {
        return 0;
    }
    let mut state = cell.state.lock().unwrap();
    match &state.phase {
        Phase::Done(words) => {
            cell.give(types, out, *words);
            return LAZY_DONE;
        }
        Phase::Trapped(kind) => {
            // SAFETY: as the caller promises.
            unsafe { out.write_unaligned(*kind as u64) };
            return LAZY_TRAPPED;
        }
        Phase::Unstarted => {
            // SAFETY: a worker runs the fiber.
            let me = unsafe {
                (*ctx.fiber.load(std::sync::atomic::Ordering::Relaxed))
                    .ctx
                    .clone()
            };
            state.phase = Phase::Running(me);
            drop(state);
            ctx.lazy.lock().unwrap().push(cell);
            return LAZY_RUN;
        }
        Phase::Running(runner) if std::ptr::eq(&**runner, ctx) => {
            // SAFETY: as the caller promises.
            unsafe { out.write_unaligned(TrapKind::Cycle as u64) };
            return LAZY_TRAPPED;
        }
        Phase::Running(_) => {}
    }
    // SAFETY: as the caller promises.
    if unsafe { scheduler_of(ctx) }.is_none() {
        raise(ctx, TrapKind::Unsupported, None);
        return 0;
    }
    let token = state.next_token;
    state.next_token += 1;
    // SAFETY: a worker runs the fiber.
    let me = unsafe {
        (*ctx.fiber.load(std::sync::atomic::Ordering::Relaxed))
            .ctx
            .clone()
    };
    // SAFETY: as the caller promises.
    let fiber = unsafe { suspend(ctx, WaitReason::Lazy) };
    state.waiters.push_back(Waiter {
        fiber,
        ctx: me,
        out,
        token,
    });
    drop(state);
    wait_for(ctx, Waiting::Lazy { cell, token });
    0
}

system_stack_fn! {
    /// `rt_lazy_set(ctx, lazy, w0, w1)`: see `crag_abi::RuntimeFn::LazySet`.
    fn rt_lazy_set(ctx: *const TaskContext, lazy: *const LazyCell, w0: u64, w1: u64) => set_entry
}

/// The Rust half of `rt_lazy_set`.
///
/// # Safety
///
/// Called only by `rt_lazy_set`, by the task `rt_lazy_get` told to compute
/// the value, with the value's references.
unsafe extern "C" fn set_entry(ctx: *const TaskContext, lazy: *const LazyCell, w0: u64, w1: u64) {
    // SAFETY: as the caller promises.
    let (ctx, cell, (_, types)) = unsafe { (&*ctx, &*lazy, worker_of(&*ctx)) };
    ctx.lazy
        .lock()
        .unwrap()
        .retain(|c| !std::ptr::eq(&**c, cell));
    let words = [w0, w1];
    let mut state = cell.state.lock().unwrap();
    state.phase = Phase::Done(words);
    let waiters: Vec<Waiter> = state.waiters.drain(..).collect();
    for w in &waiters {
        cell.give(types, w.out, words);
    }
    drop(state);
    for w in waiters {
        wake(w.fiber, [LAZY_DONE, 0]);
    }
}

system_stack_fn! {
    /// `rt_lazy_free(ctx, lazy)`: see `crag_abi::RuntimeFn::LazyFree`.
    fn rt_lazy_free(ctx: *const TaskContext, lazy: *const LazyCell) => free_entry
}

/// The Rust half of `rt_lazy_free`.
///
/// # Safety
///
/// Called only by `rt_lazy_free`, once, with a cell no task reads or
/// computes any more.
/// Frees the cell of a lazy value's box being freed, with its value.
///
/// # Safety
///
/// `lazy` came from `rt_lazy_new`, no task reads or computes it any more,
/// and it is freed once.
pub(crate) unsafe fn free(lazy: u64, heap: &mut Heap, types: &Types) {
    // SAFETY: as the caller promises.
    let cell = unsafe { Arc::from_raw(lazy as *const LazyCell) };
    let phase = std::mem::replace(&mut cell.state.lock().unwrap().phase, Phase::Unstarted);
    if let Phase::Done(words) = phase {
        release(heap, types, cell.list, words);
    }
}

unsafe extern "C" fn free_entry(ctx: *const TaskContext, lazy: *const LazyCell) {
    // SAFETY: as the caller promises.
    let (cell, (heap, types)) = unsafe { (Arc::from_raw(lazy), worker_of(&*ctx)) };
    let phase = std::mem::replace(&mut cell.state.lock().unwrap().phase, Phase::Unstarted);
    if let Phase::Done(words) = phase {
        release(heap, types, cell.list, words);
    }
}

fn release(heap: &mut Heap, types: &Types, list: u64, mut words: [u64; 2]) {
    // SAFETY: the cell owned the value's references.
    unsafe {
        release_value(
            heap,
            types,
            words.as_mut_ptr().cast(),
            types.element_of(list),
        )
    };
}
