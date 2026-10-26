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

use std::collections::VecDeque;
use std::sync::atomic::Ordering;

use crag_abi::{SIGNAL_FAIL, SIGNAL_NONE, SIGNAL_OK, SIGNAL_PLAIN, SIGNAL_RETRY};

use crate::fiber::{Fiber, TaskContext};
use crate::heap::Heap;
use crate::rc::{Types, release_value};

/// A fiber's signals.
#[derive(Default)]
pub(crate) struct Signals {
    /// The blocks open around the code that runs: `atomic` blocks and
    /// update closures.
    depth: u32,
    /// Emissions whose outcome is still open.
    held: Vec<Held>,
    /// Emissions to deliver, oldest first, with their list types.
    ready: VecDeque<(u64, [u64; 2])>,
}

struct Held {
    depth: u32,
    qualifier: u64,
    list: u64,
    words: [u64; 2],
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
                self.ready.push_back((held.list, held.words));
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
        for (list, words) in self.ready.drain(..) {
            release(heap, types, list, words);
        }
        self.depth = 0;
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
    /// `rt_signal_emit(ctx, qualifier, list, w0, w1)`: see
    /// `crag_abi::RuntimeFn::SignalEmit`.
    fn rt_signal_emit(ctx: *const TaskContext, qualifier: u64, list: u64, w0: u64, w1: u64) => emit_entry
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
) {
    // SAFETY: as the caller promises.
    let signals = unsafe { signals_of(&*ctx) };
    if signals.depth == 0 {
        crate::die("emitted a signal outside a block");
    }
    signals.held.push(Held {
        depth: signals.depth,
        qualifier,
        list,
        words: [w0, w1],
    });
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
    let signals = unsafe { signals_of(&*ctx) };
    match signals.ready.pop_front() {
        Some((list, words)) => {
            // SAFETY: as the caller promises.
            unsafe { out.cast::<[u64; 2]>().write_unaligned(words) };
            list
        }
        None => SIGNAL_NONE,
    }
}
