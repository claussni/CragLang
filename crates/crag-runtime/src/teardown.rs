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

//! Deferred teardown (Plan §11.7.12, Specification §13.5): dropping a
//! large structure does not stall the task that drops it.
//!
//! Generated code releases a value whose type is not `Immediate` with
//! `rt_release_deferred` instead of `rt_release`. It frees up to
//! [`BUDGET`] boxes at once, running the dispose handlers it meets through
//! the task's queue of disposals as `rt_release` does; the rest of the
//! structure goes to the scheduler's teardown queue. Workers free the
//! queued structures in batches between fibers.
//!
//! The runtime never calls Crag code, so a `Deferred` dispose handler met
//! in a queued structure runs in a task of its own, started through the
//! image's entry stub for one argument, as the tasks of scopes are. No one
//! waits for it: when it traps, the trap becomes a signal only (§8.3),
//! which the runtime reports on stderr until signals reach their handlers.
//! A type that holds an `Immediate` value is itself `Immediate` (§13.3),
//! so a queued structure holds none.

use crate::die;
use crate::fiber::{Fiber, FiberConfig, TaskContext, Worker};
use crate::rc::{free_chain, release_box, start_chain, take_dispose_code};
use crate::sched::{Local, Shared, scheduler_of};
use crate::system::worker_of;

/// The boxes a drop frees before it queues the rest, and a worker frees
/// at a time.
pub const BUDGET: usize = 1024;

system_stack_fn! {
    /// `rt_release_deferred(ctx, ptr)`: see
    /// `crag_abi::RuntimeFn::ReleaseDeferred`.
    fn rt_release_deferred(ctx: *const TaskContext, ptr: *mut u8) => release_entry
}

/// The Rust half of `rt_release_deferred`.
///
/// # Safety
///
/// Called only by `rt_release_deferred`, for a box whose count generated
/// code has just taken to zero.
unsafe extern "C" fn release_entry(ctx: *const TaskContext, ptr: *mut u8) {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        let Some(shared) = scheduler_of(&*ctx) else {
            // No one to hand the rest to.
            release_box(heap, types, ptr);
            return;
        };
        let mut pending = start_chain(ptr);
        free_chain(heap, types, &mut pending, BUDGET, &mut |heap, ptr| {
            heap.queue_disposal(ptr)
        });
        if !pending.is_null() {
            shared.queue_teardown(pending);
        }
    }
}

/// Frees a batch of the queued structure at `head` on `worker`, starts
/// the dispose handlers it meets, and queues the rest again.
///
/// # Safety
///
/// `worker` is the worker running this, between fibers; `head` came from
/// the teardown queue.
pub(crate) unsafe fn batch(shared: &Shared, worker: *mut Worker, local: &mut Local, head: usize) {
    // SAFETY: as the caller promises.
    let (heap, types) = unsafe { Worker::heap_and_types(worker) };
    let mut handlers = Vec::new();
    let mut pending = head as *mut u8;
    // SAFETY: the queue holds dead boxes linked by their count words.
    unsafe {
        free_chain(heap, types, &mut pending, BUDGET, &mut |_, ptr| {
            handlers.push(ptr)
        })
    };
    for ptr in handlers {
        // SAFETY: as the caller promises.
        let entries = unsafe { Worker::code(worker) }
            .task_entries()
            .unwrap_or_else(|| die("the image gave no entry stubs for tasks"));
        // SAFETY: the box is live with the reference its handler takes.
        let code = unsafe { take_dispose_code(types, ptr) };
        // SAFETY: the stub calls a function of one argument and no
        // results, as dispose code is.
        let mut fiber = unsafe {
            Fiber::new(
                entries[0],
                code as usize,
                &[ptr as u64],
                FiberConfig::default(),
            )
        }
        .unwrap_or_else(|_| die("out of memory for a dispose handler's stack"));
        fiber.detached = true;
        shared.launch(fiber, Some(local));
    }
    if pending.is_null() {
        shared.retire();
    } else {
        shared.requeue_teardown(pending);
    }
}

/// Reports the trap of a deferred dispose handler, which no one waits for.
pub(crate) fn trapped(fiber: &Fiber) {
    let Some(trap) = fiber.trap() else {
        return;
    };
    let at = match trap.position {
        Some(p) => format!(" at byte {p}"),
        None => String::new(),
    };
    eprintln!(
        "crag: a deferred dispose handler trapped: {:?}{at}",
        trap.kind
    );
}
