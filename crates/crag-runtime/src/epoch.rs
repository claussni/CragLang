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

//! Deferred release of the values ref writes replace (Plan §11.7.6), by
//! epochs, after [crossbeam-epoch](https://docs.rs/crossbeam-epoch).
//!
//! A task that reads a ref borrows its value without counting it, so the
//! reference the cell held must outlive every such read. The read pins the
//! task to the current epoch, and the write that replaces the value
//! retires the cell's reference instead of releasing it: the release waits
//! until no task is pinned to the epoch of the retirement or an earlier
//! one. The pin belongs to the task, not to its worker: a task may be
//! preempted while it holds a borrowed value, and resumed elsewhere.
//!
//! The epoch advances by one once no task is pinned to the one before it,
//! so pins are only ever to the current epoch or the one before, and three
//! counters, one per epoch modulo three, hold them all. A value retired in
//! epoch `e` is released once the epoch is `e + 2`.
//!
//! The epoch, like the version clock, is the process's: the values are
//! released with the type descriptors they were retired with.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use crate::fiber::TaskContext;
use crate::heap::Heap;
use crate::rc::{Types, release_value};

struct Epoch {
    now: AtomicU64,
    /// The tasks pinned to each epoch modulo three.
    pins: [AtomicUsize; 3],
    retired: Mutex<VecDeque<Retired>>,
    /// How many values wait in `retired`.
    pending: AtomicUsize,
}

/// A value whose cell's reference is yet to be released.
struct Retired {
    epoch: u64,
    words: [u64; 2],
    list: u64,
    types: Arc<Types>,
}

static EPOCH: Epoch = Epoch {
    now: AtomicU64::new(0),
    pins: [const { AtomicUsize::new(0) }; 3],
    retired: Mutex::new(VecDeque::new()),
    pending: AtomicUsize::new(0),
};

/// Pins the task of `ctx` to the current epoch, unless it is pinned.
pub(crate) fn pin(ctx: &TaskContext) {
    if ctx.pinned.load(Ordering::Relaxed) != 0 {
        return;
    }
    loop {
        let e = EPOCH.now.load(Ordering::SeqCst);
        let pins = &EPOCH.pins[(e % 3) as usize];
        pins.fetch_add(1, Ordering::SeqCst);
        // An epoch that moved on meanwhile may not have seen the pin.
        if EPOCH.now.load(Ordering::SeqCst) == e {
            ctx.pinned.store(e + 1, Ordering::Relaxed);
            return;
        }
        pins.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Unpins the task of `ctx`, if it is pinned, and releases what may be
/// released now.
pub(crate) fn unpin(ctx: &TaskContext, heap: &mut Heap) {
    // Only the task's worker changes the pin.
    let pinned = ctx.pinned.load(Ordering::Relaxed);
    if pinned == 0 {
        return;
    }
    ctx.pinned.store(0, Ordering::Relaxed);
    EPOCH.pins[((pinned - 1) % 3) as usize].fetch_sub(1, Ordering::SeqCst);
    if EPOCH.pending.load(Ordering::Relaxed) != 0 {
        collect(heap);
    }
}

/// Retires the cell's reference to a value of the elements of list type
/// `list` that a write replaced.
pub(crate) fn retire(heap: &mut Heap, types: &Arc<Types>, words: [u64; 2], list: u64) {
    if types.cell_of(list).counted.is_empty() {
        return;
    }
    let epoch = EPOCH.now.load(Ordering::SeqCst);
    EPOCH.retired.lock().unwrap().push_back(Retired {
        epoch,
        words,
        list,
        types: types.clone(),
    });
    EPOCH.pending.fetch_add(1, Ordering::Relaxed);
    collect(heap);
}

/// Advances the epoch as far as the pins allow, at most twice, and
/// releases the values retired long enough ago. Another thread collecting
/// does it for this one.
fn collect(heap: &mut Heap) {
    let Ok(mut retired) = EPOCH.retired.try_lock() else {
        return;
    };
    for _ in 0..2 {
        if !advance() {
            break;
        }
    }
    let now = EPOCH.now.load(Ordering::SeqCst);
    let mut due = Vec::new();
    while retired.front().is_some_and(|r| r.epoch + 2 <= now) {
        due.push(retired.pop_front().expect("a front"));
    }
    drop(retired);
    EPOCH.pending.fetch_sub(due.len(), Ordering::Relaxed);
    for mut r in due {
        let element = r.types.cell_of(r.list);
        // SAFETY: the cell's reference came with the value, and no task
        // pinned when it could still read it is pinned any more.
        unsafe { release_value(heap, &r.types, r.words.as_mut_ptr().cast(), element) }
    }
}

/// Moves the epoch on by one if no task is pinned to the one before it.
fn advance() -> bool {
    let e = EPOCH.now.load(Ordering::SeqCst);
    if EPOCH.pins[((e + 2) % 3) as usize].load(Ordering::SeqCst) != 0 {
        return false;
    }
    EPOCH
        .now
        .compare_exchange(e, e + 1, Ordering::SeqCst, Ordering::SeqCst)
        .is_ok()
}
