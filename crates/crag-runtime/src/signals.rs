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

//! Signals emitted in `atomic` blocks and update closures (Plan §11.7.10,
//! Specification §11.2), held until the block's outcome decides which are
//! delivered.
//!
//! The runtime never calls Crag code, so it does not run handlers: it
//! keeps each fiber's emissions, and once an outcome makes some of them
//! deliverable it queues them, and generated code takes them with
//! `rt_signal_next` and calls the handlers. Each emission is tagged with
//! the depth of the block it came from:
//!
//! - an inner block that commits hands its emissions to the block around
//!   it, and the outermost one that commits delivers the unqualified and
//!   `ok` ones;
//! - a block that fails delivers its `fail` ones at once, also an inner
//!   one whose attempt is later rerun, and keeps its `retry` ones for the
//!   attempt;
//! - a conflict delivers the attempt's `retry` ones.
//!
//! What an outcome does not deliver is given up. A task that stops inside
//! a block, or before it took what was queued, gives everything up.
//!
//! Each fiber also keeps the handlers that `on` statements registered
//! (Plan §11.7.14): the handler's function value, the type indices of the
//! signal types it takes and how specific its own type is, and the block
//! it belongs to, by the number of handlers below it. Generated code looks
//! up the handler of a signal with `rt_signal_find`, which hides the
//! handler's block and everything above it while the handler runs, so that
//! an `emit` in it passes the signal on outward. A task starts with the
//! handlers its starter sees.

use std::collections::VecDeque;
use std::sync::atomic::Ordering;

use crag_abi::{
    SIGNAL_DELIVER, SIGNAL_FAIL, SIGNAL_HELD, SIGNAL_NONE, SIGNAL_OK, SIGNAL_PLAIN, SIGNAL_RETRY,
};

use crate::fiber::{Fiber, TaskContext};
use crate::heap::Heap;
use crate::rc::{Types, release_value};
use crate::system::worker_of;

/// A fiber's signals.
#[derive(Default)]
pub(crate) struct Signals {
    /// The blocks open around the code that runs: `atomic` blocks and
    /// update closures.
    depth: u32,
    /// Emissions whose outcome is still open.
    held: Vec<Held>,
    /// Emissions to deliver, oldest first, with their list types and
    /// type information.
    ready: VecDeque<(u64, [u64; 2], u64)>,
    /// The emission `rt_signal_next` gave last, which generated code
    /// borrows until the next call.
    taken: Option<(u64, [u64; 2])>,
    /// The handlers registered, innermost last.
    handlers: Vec<Handler>,
    /// Ranges of `handlers` hidden while a handler of the lowest one's
    /// block runs, innermost last.
    hidden: Vec<(usize, usize)>,
}

struct Held {
    depth: u32,
    qualifier: u64,
    list: u64,
    words: [u64; 2],
    /// What generated code knows of the signal's type (see
    /// `crag_abi::RuntimeFn::SignalEmit`).
    info: u64,
}

/// A handler an `on` statement registered.
#[derive(Clone, Copy)]
pub(crate) struct Handler {
    code: u64,
    env: u64,
    /// The type indices of the signal types it takes, sorted: a `u32`
    /// array in the code's static data.
    types: usize,
    count: usize,
    /// How many parent types its own type has.
    specificity: u32,
    /// The words of its parameter, zero or one.
    words: u64,
    /// Its block, by the number of handlers below it.
    base: usize,
}

impl Handler {
    fn takes(&self, index: u32) -> bool {
        // SAFETY: the array is static data of code that stays loaded.
        let types = unsafe { std::slice::from_raw_parts(self.types as *const u32, self.count) };
        types.binary_search(&index).is_ok()
    }
}

/// Gives up an emission's value.
fn release(heap: &mut Heap, types: &Types, list: u64, mut words: [u64; 2]) {
    // SAFETY: the emission owns the value's references.
    unsafe {
        release_value(
            heap,
            types,
            words.as_mut_ptr().cast(),
            types.element_of(list),
        )
    };
}

impl Signals {
    /// A block opens.
    pub(crate) fn open(&mut self) {
        self.depth += 1;
    }

    /// Keeps the emissions for which `keep` gives a depth, queues those
    /// for which `deliver` holds, and gives up the rest.
    fn settle(
        &mut self,
        from: usize,
        heap: &mut Heap,
        types: &Types,
        deliver: impl Fn(&Held) -> bool,
        keep: impl Fn(&Held) -> Option<u32>,
    ) {
        let mut kept = Vec::new();
        for mut held in self.held.drain(from..) {
            if deliver(&held) {
                self.ready.push_back((held.list, held.words, held.info));
            } else if let Some(depth) = keep(&held) {
                held.depth = depth;
                kept.push(held);
            } else {
                release(heap, types, held.list, held.words);
            }
        }
        self.held.extend(kept);
    }

    /// Where the emissions of the innermost block start.
    fn innermost(&self) -> usize {
        self.held.partition_point(|h| h.depth < self.depth)
    }

    /// The innermost block commits.
    pub(crate) fn commit(&mut self, heap: &mut Heap, types: &Types) {
        let depth = self.depth;
        let from = self.innermost();
        if depth > 1 {
            self.settle(from, heap, types, |_| false, |_| Some(depth - 1));
        } else {
            self.settle(
                0,
                heap,
                types,
                |h| matches!(h.qualifier, SIGNAL_PLAIN | SIGNAL_OK),
                |_| None,
            );
        }
        self.depth = self.depth.saturating_sub(1);
    }

    /// The innermost block fails.
    pub(crate) fn fail(&mut self, heap: &mut Heap, types: &Types) {
        let depth = self.depth;
        let from = self.innermost();
        self.settle(
            from,
            heap,
            types,
            |h| h.qualifier == SIGNAL_FAIL,
            |h| (h.qualifier == SIGNAL_RETRY && depth > 1).then_some(depth - 1),
        );
        self.depth = self.depth.saturating_sub(1);
    }

    /// The attempt of the outermost block is discarded: it reruns if
    /// `rerun`, with its block open again, as a transaction's does.
    pub(crate) fn conflict(&mut self, rerun: bool, heap: &mut Heap, types: &Types) {
        self.settle(0, heap, types, |h| h.qualifier == SIGNAL_RETRY, |_| None);
        self.depth = u32::from(rerun);
    }

    /// Gives up everything, as a task that stops does.
    pub(crate) fn clear(&mut self, heap: &mut Heap, types: &Types) {
        self.settle(0, heap, types, |_| false, |_| None);
        for (list, words, _) in self.ready.drain(..) {
            release(heap, types, list, words);
        }
        if let Some((list, words)) = self.taken.take() {
            release(heap, types, list, words);
        }
        self.depth = 0;
        self.handlers.clear();
        self.hidden.clear();
    }

    /// The handlers a task started now begins with: those the starter
    /// sees.
    pub(crate) fn inherited(&self) -> Vec<Handler> {
        let mut out = Vec::new();
        for (k, handler) in self.handlers.iter().enumerate() {
            if !self.is_hidden(k) {
                // A block's base counts the handlers below it that stay.
                let base = (0..handler.base).filter(|&j| !self.is_hidden(j)).count();
                out.push(Handler { base, ..*handler });
            }
        }
        out
    }

    /// Starts a task's handlers.
    pub(crate) fn inherit(&mut self, handlers: Vec<Handler>) {
        self.handlers = handlers;
        self.hidden.clear();
    }

    fn is_hidden(&self, k: usize) -> bool {
        self.hidden.iter().any(|&(lo, hi)| (lo..hi).contains(&k))
    }
}

/// The signals of the fiber running on `ctx`.
///
/// # Safety
///
/// Called by the Rust half of a runtime function for the fiber of `ctx`.
pub(crate) unsafe fn signals_of<'a>(ctx: &TaskContext) -> &'a mut Signals {
    // SAFETY: as the caller promises, a worker runs the fiber.
    unsafe { &mut (*ctx.fiber.load(Ordering::Relaxed)).signals }
}

/// Gives up the signals of a task that stopped.
pub(crate) fn stopped(fiber: &mut Fiber, heap: &mut Heap, types: &Types) {
    fiber.signals.clear(heap, types);
}

system_stack_fn! {
    /// `rt_signal_emit(ctx, qualifier, list, w0, w1, info) -> status`: see
    /// `crag_abi::RuntimeFn::SignalEmit`.
    fn rt_signal_emit(ctx: *const TaskContext, qualifier: u64, list: u64, w0: u64, w1: u64, info: u64) -> u64 => emit_entry
}

/// The Rust half of `rt_signal_emit`.
///
/// # Safety
///
/// Called only by `rt_signal_emit`, in a block, with a signal laid out as
/// the elements of list type `list` whose references the caller owns.
unsafe extern "C" fn emit_entry(
    ctx: *const TaskContext,
    qualifier: u64,
    list: u64,
    w0: u64,
    w1: u64,
    info: u64,
) -> u64 {
    // SAFETY: as the caller promises.
    let signals = unsafe { signals_of(&*ctx) };
    if signals.depth == 0 {
        return SIGNAL_DELIVER;
    }
    signals.held.push(Held {
        depth: signals.depth,
        qualifier,
        list,
        words: [w0, w1],
        info,
    });
    SIGNAL_HELD
}

system_stack_fn! {
    /// `rt_signal_next(ctx, out) -> list`: see
    /// `crag_abi::RuntimeFn::SignalNext`.
    fn rt_signal_next(ctx: *const TaskContext, out: *mut u64) -> u64 => next_entry
}

/// The Rust half of `rt_signal_next`.
///
/// # Safety
///
/// Called only by `rt_signal_next`, with room for two words at `out`.
unsafe extern "C" fn next_entry(ctx: *const TaskContext, out: *mut u64) -> u64 {
    // SAFETY: as the caller promises.
    let (signals, (heap, types)) = unsafe { (signals_of(&*ctx), worker_of(ctx)) };
    if let Some((list, words)) = signals.taken.take() {
        release(heap, types, list, words);
    }
    match signals.ready.pop_front() {
        Some((list, words, info)) => {
            // SAFETY: as the caller promises.
            unsafe {
                out.cast::<[u64; 3]>()
                    .write_unaligned([words[0], words[1], info])
            };
            signals.taken = Some((list, words));
            list
        }
        None => SIGNAL_NONE,
    }
}

system_stack_fn! {
    /// `rt_signal_mark(ctx) -> mark`: see `crag_abi::RuntimeFn::SignalMark`.
    fn rt_signal_mark(ctx: *const TaskContext) -> u64 => mark_entry
}

/// The Rust half of `rt_signal_mark`.
///
/// # Safety
///
/// Called only by `rt_signal_mark`.
unsafe extern "C" fn mark_entry(ctx: *const TaskContext) -> u64 {
    // SAFETY: as the caller promises.
    unsafe { signals_of(&*ctx) }.handlers.len() as u64
}

system_stack_fn! {
    /// `rt_signal_reset(ctx, mark)`: see `crag_abi::RuntimeFn::SignalReset`.
    fn rt_signal_reset(ctx: *const TaskContext, mark: u64) => reset_entry
}

/// The Rust half of `rt_signal_reset`.
///
/// # Safety
///
/// Called only by `rt_signal_reset`, with a mark of the fiber.
unsafe extern "C" fn reset_entry(ctx: *const TaskContext, mark: u64) {
    // SAFETY: as the caller promises.
    let signals = unsafe { signals_of(&*ctx) };
    signals.handlers.truncate(mark as usize);
}

system_stack_fn! {
    /// `rt_signal_on(ctx, code, env, types, packed, base)`: see
    /// `crag_abi::RuntimeFn::SignalOn`.
    fn rt_signal_on(ctx: *const TaskContext, code: u64, env: u64, types: u64, packed: u64, base: u64) => on_entry
}

/// The Rust half of `rt_signal_on`.
///
/// # Safety
///
/// Called only by `rt_signal_on`, with a function value the caller keeps
/// until it resets the fiber's handlers to `base`, and a sorted array of
/// type indices in static data.
unsafe extern "C" fn on_entry(
    ctx: *const TaskContext,
    code: u64,
    env: u64,
    types: u64,
    packed: u64,
    base: u64,
) {
    // SAFETY: as the caller promises.
    let signals = unsafe { signals_of(&*ctx) };
    signals.handlers.push(Handler {
        code,
        env,
        types: types as usize,
        count: (packed >> 32) as usize,
        specificity: ((packed >> 8) & 0xff_ffff) as u32,
        words: packed & 0xff,
        base: base as usize,
    });
}

system_stack_fn! {
    /// `rt_signal_find(ctx, index, out) -> found`: see
    /// `crag_abi::RuntimeFn::SignalFind`.
    fn rt_signal_find(ctx: *const TaskContext, index: u64, out: *mut u64) -> u64 => find_entry
}

/// The Rust half of `rt_signal_find`.
///
/// # Safety
///
/// Called only by `rt_signal_find`, with room for three words at `out`.
unsafe extern "C" fn find_entry(ctx: *const TaskContext, index: u64, out: *mut u64) -> u64 {
    // SAFETY: as the caller promises.
    let signals = unsafe { signals_of(&*ctx) };
    let index = index as u32;
    let visible = |k: usize| !signals.is_hidden(k);
    let Some(innermost) = (0..signals.handlers.len())
        .rev()
        .find(|&k| visible(k) && signals.handlers[k].takes(index))
    else {
        return 0;
    };
    // The most specific of the block's handlers that take it.
    let base = signals.handlers[innermost].base;
    let chosen = (base..signals.handlers.len())
        .filter(|&k| {
            visible(k) && signals.handlers[k].base == base && signals.handlers[k].takes(index)
        })
        .max_by_key(|&k| (signals.handlers[k].specificity, k))
        .unwrap_or(innermost);
    let handler = signals.handlers[chosen];
    signals.hidden.push((base, signals.handlers.len()));
    // SAFETY: as the caller promises.
    unsafe {
        out.cast::<[u64; 3]>()
            .write_unaligned([handler.code, handler.env, handler.words])
    };
    1
}

system_stack_fn! {
    /// `rt_signal_leave(ctx)`: see `crag_abi::RuntimeFn::SignalLeave`.
    fn rt_signal_leave(ctx: *const TaskContext) => leave_entry
}

/// The Rust half of `rt_signal_leave`.
///
/// # Safety
///
/// Called only by `rt_signal_leave`.
unsafe extern "C" fn leave_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    unsafe { signals_of(&*ctx) }.hidden.pop();
}

system_stack_fn! {
    /// `rt_signal_default(ctx, name, len)`: see
    /// `crag_abi::RuntimeFn::SignalDefault`.
    fn rt_signal_default(ctx: *const TaskContext, name: *const u8, len: u64) => default_entry
}

/// The Rust half of `rt_signal_default`: the root's handler.
///
/// # Safety
///
/// Called only by `rt_signal_default`, with `len` bytes of UTF-8 at
/// `name`.
unsafe extern "C" fn default_entry(_ctx: *const TaskContext, name: *const u8, len: u64) {
    // SAFETY: as the caller promises.
    let name = unsafe { std::slice::from_raw_parts(name, len as usize) };
    eprintln!("signal: {}", String::from_utf8_lossy(name));
}
