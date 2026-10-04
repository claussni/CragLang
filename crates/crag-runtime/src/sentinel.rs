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

//! Stop requests through the stack-limit sentinel (Plan §11.3.4).
//!
//! To stop a running fiber at its next safe point, the runtime records why
//! and stores the sentinel in the fiber's stack limit. No stack pointer
//! passes a check against the sentinel, so the next function entry or loop
//! back-edge calls `rt_morestack`, which finds the request, restores the real
//! limit and acts.

use std::sync::Arc;
use std::sync::atomic::Ordering;

use crag_abi::STACK_LIMIT_SENTINEL;

use crate::fiber::{Fiber, TaskContext};

/// Why a fiber should stop at its next check.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum StopReason {
    /// Give other fibers a turn; the fiber stays runnable.
    Preempt = 1,
    /// Stop until resumed explicitly, as the debugger does.
    Pause = 2,
}

/// Requests a stop. May be called while the fiber runs.
pub fn request_stop(fiber: &Fiber, reason: StopReason) {
    request(&fiber.ctx, reason);
}

/// Requests stops from other threads, which cannot hold the fiber itself.
#[derive(Clone)]
pub struct StopHandle(Arc<TaskContext>);

impl StopHandle {
    pub fn request_stop(&self, reason: StopReason) {
        request(&self.0, reason);
    }
}

impl Fiber {
    pub fn stop_handle(&self) -> StopHandle {
        StopHandle(self.ctx.clone())
    }
}

fn request(ctx: &TaskContext, reason: StopReason) {
    // The reason first, then the sentinel: `finish_check` relies on this
    // order to never lose a request.
    ctx.pending.fetch_or(reason as usize, Ordering::SeqCst);
    ctx.stack_limit
        .store(STACK_LIMIT_SENTINEL, Ordering::SeqCst);
}

/// Takes the pending stop reasons. Called from `rt_morestack`.
pub(crate) fn take_pending(ctx: &TaskContext) -> usize {
    ctx.pending.swap(0, Ordering::SeqCst)
}

/// Publishes the real limit when `rt_morestack` is done, replacing the
/// sentinel. A request that arrived after `take_pending` must not be lost:
/// if its reason is already recorded, the sentinel goes back in; if not, the
/// requester's own sentinel store is still to come and lands after ours.
pub(crate) fn finish_check(ctx: &TaskContext, limit: usize) {
    ctx.stack_limit.store(limit, Ordering::SeqCst);
    if ctx.pending.load(Ordering::SeqCst) != 0 {
        ctx.stack_limit
            .store(STACK_LIMIT_SENTINEL, Ordering::SeqCst);
    }
}
