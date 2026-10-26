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

//! Cancellation (Plan §11.7.4): a cancelled task stops soon, even if it
//! never waits.
//!
//! [`cancel`] sets the context's flag and the sentinel (§11.3.4), so the
//! next stack check, at a function entry or loop back-edge, unwinds the
//! task with a `Cancelled` trap. A task that waits stops at once: what it
//! waits for is called off and the fiber woken, and the suspending runtime
//! function traps instead of returning. Each such function also traps when
//! it is called on a cancelled task, so every suspension point is a stop:
//! sleeps, I/O, starts under a scope's limit, puts and takes of streams
//! (§11.7.5), the locks of `ext` (§11.7.9) and lazy values (§11.7.11).
//!
//! Inside a region where cancellation waits, `no_cancel` counts the depth,
//! and the stack checks and waits go on; leaving the last region traps.
//! A scope's parent is in such a region from the scope's start to its end,
//! since it must see every task finish: its cancellation passes to the
//! scope's tasks instead (§11.7.3). A wait that registers nothing to call
//! off is not cancelled either, as the commit of a `dur` will be
//! (§11.11.4): the task stops at the next check after it.

use std::os::fd::RawFd;
use std::sync::Arc;
use std::sync::atomic::Ordering;

use crag_abi::{NO_POSITION, TrapKind};

use crate::ext::ExtLock;
use crate::fiber::{Fiber, TaskContext};
use crate::lazy::LazyCell;
use crate::sched::{Shared, wake};
use crate::scope::Scope;
use crate::sentinel::{StopReason, request};
use crate::stream::Channel;
use crate::timer::TimerId;

/// What a suspended fiber waits for, as a cancellation sees it.
pub(crate) enum Waiting {
    /// A timer of the reactor.
    Timer { shared: Arc<Shared>, id: TimerId },
    /// An I/O operation in the reactor, told from the others on its file
    /// descriptor by its token.
    Io {
        shared: Arc<Shared>,
        fd: RawFd,
        token: u64,
    },
    /// A free place under a scope's limit, for the task at `index`.
    Start { scope: Arc<Scope>, index: usize },
    /// The tasks of a scope the fiber is the parent of: not called off,
    /// but cancelled in turn.
    Tasks(Arc<Scope>),
    /// A put or a take of a stream or a hub, told from the others by its
    /// token.
    Stream { chan: Arc<Channel>, token: u64 },
    /// The lock of an `ext`, told from the other waits by its token.
    Ext { lock: Arc<ExtLock>, token: u64 },
    /// A lazy value another task computes, told from the other reads by
    /// its token.
    Lazy { cell: Arc<LazyCell>, token: u64 },
}

/// Cancels a task from any thread.
#[derive(Clone)]
pub struct CancelHandle(Arc<TaskContext>);

impl CancelHandle {
    pub fn cancel(&self) {
        cancel(&self.0);
    }
}

impl Fiber {
    pub fn cancel_handle(&self) -> CancelHandle {
        CancelHandle(self.ctx.clone())
    }
}

/// Cancels the task of `ctx`; a second cancellation does nothing.
pub(crate) fn cancel(ctx: &TaskContext) {
    if ctx.cancel.swap(1, Ordering::SeqCst) != 0 {
        return;
    }
    request(ctx, StopReason::Cancel);
    call_off(ctx);
}

/// Whether the task of `ctx` is cancelled outside every region where
/// cancellation waits, so that it must stop now.
pub(crate) fn due(ctx: &TaskContext) -> bool {
    ctx.cancel.load(Ordering::SeqCst) != 0 && ctx.no_cancel.load(Ordering::Relaxed) == 0
}

/// Makes the suspending runtime function running for `ctx`, or the one the
/// fiber will continue in, trap with `kind` instead of returning.
pub(crate) fn raise(ctx: &TaskContext, kind: TrapKind, position: Option<u32>) {
    let position = position.map_or(NO_POSITION, u64::from);
    ctx.raise_position.store(position, Ordering::Relaxed);
    ctx.raise.store(kind as u64 + 1, Ordering::SeqCst);
}

/// Traps the calling runtime function with `Cancelled` if the task must
/// stop now; whether it did.
pub(crate) fn stop_if_due(ctx: &TaskContext) -> bool {
    crate::stress::jitter();
    let due = due(ctx);
    if due {
        raise(ctx, TrapKind::Cancelled, None);
    }
    due
}

/// Records what the fiber of `ctx`, which is suspending, waits for. A
/// cancellation that came before the record is acted on now.
pub(crate) fn wait_for(ctx: &TaskContext, waiting: Waiting) {
    *ctx.waiting.lock().unwrap() = Some(waiting);
    if ctx.cancel.load(Ordering::SeqCst) != 0 {
        call_off(ctx);
    }
}

/// Forgets what the fiber waited for, once it waits no more.
pub(crate) fn waited(ctx: &TaskContext) {
    ctx.waiting.lock().unwrap().take();
}

/// Acts on the cancellation of a fiber that may wait: passes it on to the
/// tasks of the scope it waits for, or calls off its wait and wakes it to
/// trap, unless it is in a region where cancellation waits. A wait that
/// already ended is gone from where it waited, and nothing happens.
fn call_off(ctx: &TaskContext) {
    let waiting = {
        let mut waiting = ctx.waiting.lock().unwrap();
        match &*waiting {
            // A parent passes its cancellation on to its scope's tasks,
            // whether it waits for them or for a place to start one.
            Some(Waiting::Tasks(scope) | Waiting::Start { scope, .. }) if scope.is_parent(ctx) => {
                let scope = scope.clone();
                drop(waiting);
                scope.cancel();
                return;
            }
            Some(_) if ctx.no_cancel.load(Ordering::Relaxed) == 0 => waiting.take(),
            _ => None,
        }
    };
    let fiber = match waiting {
        Some(Waiting::Timer { shared, id }) => shared.reactor.cancel_sleep(id),
        Some(Waiting::Io { shared, fd, token }) => shared.reactor.cancel_io(fd, token),
        Some(Waiting::Start { scope, index }) => scope.call_off_start(index),
        Some(Waiting::Stream { chan, token }) => chan.call_off(token),
        Some(Waiting::Ext { lock, token }) => lock.call_off(token),
        Some(Waiting::Lazy { cell, token }) => cell.call_off(token),
        Some(Waiting::Tasks(_)) | None => None,
    };
    if let Some(fiber) = fiber {
        raise(ctx, TrapKind::Cancelled, None);
        wake(fiber, [0, 0]);
    }
}

system_stack_fn! {
    /// `rt_enter_no_cancel(ctx)`: see `crag_abi::RuntimeFn::EnterNoCancel`.
    fn rt_enter_no_cancel(ctx: *const TaskContext) => enter_entry
}

/// The Rust half of `rt_enter_no_cancel`.
///
/// # Safety
///
/// Called only by `rt_enter_no_cancel`.
unsafe extern "C" fn enter_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    let ctx = unsafe { &*ctx };
    ctx.no_cancel.fetch_add(1, Ordering::Relaxed);
}

suspending_fn! {
    /// `rt_exit_no_cancel(ctx)`: see `crag_abi::RuntimeFn::ExitNoCancel`.
    fn rt_exit_no_cancel(ctx: *const TaskContext) => exit_entry
}

/// The Rust half of `rt_exit_no_cancel`. It never suspends.
///
/// # Safety
///
/// Called only by `rt_exit_no_cancel`.
unsafe extern "C" fn exit_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    let ctx = unsafe { &*ctx };
    leave_region(ctx);
}

/// Leaves a region where cancellation waits, trapping the calling runtime
/// function if the task was cancelled meanwhile and this was the last.
pub(crate) fn leave_region(ctx: &TaskContext) {
    let depth = ctx.no_cancel.load(Ordering::Relaxed);
    if depth == 0 {
        crate::die("left a region where cancellation waits that was never entered");
    }
    ctx.no_cancel.store(depth - 1, Ordering::Relaxed);
    stop_if_due(ctx);
}
