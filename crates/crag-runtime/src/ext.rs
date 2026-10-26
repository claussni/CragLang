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

//! `ext` (Plan §11.7.9, Specification §9.6): a lock for state that cannot
//! be retried, held while an access closure runs once.
//!
//! The value stays where generated code keeps it, which only the holder
//! of the lock touches; the runtime keeps the lock. A fiber that finds it
//! held suspends instead of blocking its thread, and unlocking hands it to
//! the fiber that waited longest. Locks never nest (§9.6), so a fiber
//! holds or waits for at most one, which it records: a task that stops
//! while it holds the lock gives it up, and one cancelled while it waits
//! leaves the queue.

use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

use crag_abi::TrapKind;

use crate::cancel::{Waiting, raise, stop_if_due, wait_for};
use crate::fiber::{Fiber, TaskContext};
use crate::sched::{FiberRef, WaitReason, scheduler_of, suspend, wake};

/// The lock of an `ext`.
pub(crate) struct ExtLock {
    state: Mutex<State>,
}

#[derive(Default)]
struct State {
    /// The token of the lock call that holds it.
    holder: Option<u64>,
    /// The fibers waiting for it, oldest first, with their tokens.
    waiters: VecDeque<(FiberRef, u64)>,
    next_token: u64,
}

/// What a fiber holds or waits for: the lock and the token of its call.
pub(crate) type Held = (Arc<ExtLock>, u64);

impl ExtLock {
    /// Gives the lock to the next waiter, or frees it: the fiber to wake.
    fn pass(state: &mut State) -> Option<FiberRef> {
        let (fiber, token) = state.waiters.pop_front()?;
        state.holder = Some(token);
        Some(fiber)
    }

    /// Calls off the wait with `token`, giving its fiber back; none when it
    /// no longer waits.
    pub(crate) fn call_off(&self, token: u64) -> Option<FiberRef> {
        let mut state = self.state.lock().unwrap();
        let at = state.waiters.iter().position(|&(_, t)| t == token)?;
        state.waiters.remove(at).map(|(fiber, _)| fiber)
    }

    /// Ends the hold or the wait of the call with `token`.
    fn leave(&self, token: u64) {
        let mut state = self.state.lock().unwrap();
        let next = if state.holder == Some(token) {
            state.holder = None;
            ExtLock::pass(&mut state)
        } else {
            state.waiters.retain(|&(_, t)| t != token);
            None
        };
        drop(state);
        if let Some(fiber) = next {
            wake(fiber, [0, 0]);
        }
    }
}

/// The lock behind the word generated code holds, with a count of its own.
///
/// # Safety
///
/// `ext` came from `rt_ext_new` and has not been freed.
unsafe fn share(ext: *const ExtLock) -> Arc<ExtLock> {
    // SAFETY: as the caller promises.
    unsafe {
        Arc::increment_strong_count(ext);
        Arc::from_raw(ext)
    }
}

/// The fiber running on `ctx`.
///
/// # Safety
///
/// Called by the Rust half of a runtime function for the fiber of `ctx`.
unsafe fn fiber_of<'a>(ctx: &TaskContext) -> &'a mut Fiber {
    // SAFETY: as the caller promises.
    unsafe { &mut *ctx.fiber.load(std::sync::atomic::Ordering::Relaxed) }
}

/// Gives up the lock a task held or waited for when it stopped.
pub(crate) fn stopped(fiber: &mut Fiber) {
    if let Some((lock, token)) = fiber.ext.take() {
        lock.leave(token);
    }
}

system_stack_fn! {
    /// `rt_ext_new(ctx) -> ext`: see `crag_abi::RuntimeFn::ExtNew`.
    fn rt_ext_new(ctx: *const TaskContext) -> u64 => new_entry
}

/// The Rust half of `rt_ext_new`.
///
/// # Safety
///
/// Called only by `rt_ext_new`.
unsafe extern "C" fn new_entry(_ctx: *const TaskContext) -> u64 {
    let lock = ExtLock {
        state: Mutex::new(State::default()),
    };
    Arc::into_raw(Arc::new(lock)) as u64
}

suspending_fn! {
    /// `rt_ext_lock(ctx, ext)`: see `crag_abi::RuntimeFn::ExtLock`.
    fn rt_ext_lock(ctx: *const TaskContext, ext: *const ExtLock) => lock_entry
}

/// The Rust half of `rt_ext_lock`: suspends while another holds the lock.
///
/// # Safety
///
/// Called only by `rt_ext_lock`, with a lock that has not been freed and
/// that the fiber neither holds nor waits for.
unsafe extern "C" fn lock_entry(ctx: *const TaskContext, ext: *const ExtLock) {
    // SAFETY: as the caller promises.
    let (ctx, lock, fiber) = unsafe { (&*ctx, share(ext), fiber_of(&*ctx)) };
    if stop_if_due(ctx) {
        return;
    }
    let mut state = lock.state.lock().unwrap();
    let token = state.next_token;
    state.next_token += 1;
    if state.holder.is_none() {
        state.holder = Some(token);
        drop(state);
        fiber.ext = Some((lock, token));
        return;
    }
    // SAFETY: as the caller promises.
    if unsafe { scheduler_of(ctx) }.is_none() {
        raise(ctx, TrapKind::Unsupported, None);
        return;
    }
    // The hold the wake gives is the fiber's from the hand-over on.
    fiber.ext = Some((lock.clone(), token));
    // SAFETY: as the caller promises.
    let waiter = unsafe { suspend(ctx, WaitReason::Ext) };
    state.waiters.push_back((waiter, token));
    drop(state);
    wait_for(ctx, Waiting::Ext { lock, token });
}

system_stack_fn! {
    /// `rt_ext_unlock(ctx, ext)`: see `crag_abi::RuntimeFn::ExtUnlock`.
    fn rt_ext_unlock(ctx: *const TaskContext, ext: *const ExtLock) => unlock_entry
}

/// The Rust half of `rt_ext_unlock`.
///
/// # Safety
///
/// Called only by `rt_ext_unlock`, by the fiber that holds the lock.
unsafe extern "C" fn unlock_entry(ctx: *const TaskContext, _ext: *const ExtLock) {
    // SAFETY: as the caller promises.
    let fiber = unsafe { fiber_of(&*ctx) };
    match fiber.ext.take() {
        Some((lock, token)) => lock.leave(token),
        None => crate::die("unlocked an ext that was not locked"),
    }
}

system_stack_fn! {
    /// `rt_ext_free(ctx, ext)`: see `crag_abi::RuntimeFn::ExtFree`.
    fn rt_ext_free(ctx: *const TaskContext, ext: *const ExtLock) => free_entry
}

/// The Rust half of `rt_ext_free`.
///
/// # Safety
///
/// Called only by `rt_ext_free`, once, with a lock no fiber holds or
/// waits for.
unsafe extern "C" fn free_entry(_ctx: *const TaskContext, ext: *const ExtLock) {
    // SAFETY: as the caller promises.
    drop(unsafe { Arc::from_raw(ext) });
}
