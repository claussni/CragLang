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

//! Refs (Plan §11.7.6, Specification Chapter 9): cells that tasks share,
//! changed by optimistic updates.
//!
//! A cell is a version word and the value's two words, on the side stack
//! of the task that binds the ref; the tasks that use it end before it
//! does (§10.1). The lowest bit of the version is a lock, which a write
//! holds only while it stores the value. A reader loads the version, the
//! value and the version again, and tries again when they differ or the
//! lock was held, as a seqlock reader does.
//!
//! An update is driven by generated code: `rt_ref_read`, the closure, then
//! `rt_ref_commit`, which writes when the version is still the one read
//! and else asks for a rerun. The runtime never calls Crag code. The read
//! borrows the value without counting it, so the value a write replaces
//! keeps the cell's reference until no task can still read it, which the
//! epochs decide (`epoch`).
//!
//! A write takes its version from a clock the whole process shares, so the
//! versions of all cells are ordered, as transactions will need (§11.7.7).

use std::sync::Arc;
use std::sync::atomic::{AtomicU64, Ordering, fence};

use crag_abi::REF_CELL_SIZE;

use crate::epoch::{pin, retire, unpin};
use crate::fiber::{TaskContext, Worker};
use crate::heap::Heap;
use crate::io::Words;
use crate::rc::{Types, release_value, retain_value};

/// A ref cell, as generated code lays it out.
#[repr(C)]
pub(crate) struct Cell {
    version: AtomicU64,
    value: [AtomicU64; 2],
}

const _: () = assert!(size_of::<Cell>() == REF_CELL_SIZE as usize);

/// The last version a write gave a cell.
static CLOCK: AtomicU64 = AtomicU64::new(0);

/// Waits a little longer each time a cell is locked.
fn back_off(spins: &mut u32) {
    if *spins < 64 {
        *spins += 1;
        std::hint::spin_loop();
    } else {
        std::thread::yield_now();
    }
}

impl Cell {
    /// The version and the value, once no write is under way.
    fn read(&self) -> (u64, [u64; 2]) {
        let mut spins = 0;
        loop {
            let version = self.version.load(Ordering::Acquire);
            if version & 1 == 0 {
                let words = self.value.each_ref().map(|w| w.load(Ordering::Relaxed));
                fence(Ordering::Acquire);
                if self.version.load(Ordering::Relaxed) == version {
                    return (version, words);
                }
            }
            back_off(&mut spins);
        }
    }

    /// Locks the cell if it still holds `version`.
    fn lock(&self, version: u64) -> bool {
        let locked = self
            .version
            .compare_exchange(version, version | 1, Ordering::Acquire, Ordering::Relaxed)
            .is_ok();
        // Readers that see the stores to come see the lock too.
        fence(Ordering::Release);
        locked
    }

    /// Locks the cell whatever it holds: its version.
    fn lock_any(&self) -> u64 {
        let mut spins = 0;
        loop {
            let version = self.version.load(Ordering::Relaxed);
            if version & 1 == 0 && self.lock(version) {
                return version;
            }
            back_off(&mut spins);
        }
    }

    /// Replaces the value of the locked cell and unlocks it with a new
    /// version: the old value.
    fn replace(&self, words: [u64; 2]) -> [u64; 2] {
        let old = self.value.each_ref().map(|w| w.load(Ordering::Relaxed));
        for (w, word) in self.value.iter().zip(words) {
            w.store(word, Ordering::Relaxed);
        }
        let version = CLOCK.fetch_add(2, Ordering::SeqCst) + 2;
        self.version.store(version, Ordering::Release);
        old
    }
}

/// The heap and the shared type descriptors of the worker running the
/// fiber of `ctx`.
///
/// # Safety
///
/// As for `system::worker_of`.
unsafe fn parts<'a>(ctx: &TaskContext) -> (&'a mut Heap, &'a Arc<Types>) {
    // SAFETY: as the caller promises.
    unsafe { Worker::heap_and_shared_types(ctx.worker.load(Ordering::Relaxed)) }
}

system_stack_fn! {
    /// `rt_ref_read(ctx, cell, out) -> version`: see
    /// `crag_abi::RuntimeFn::RefRead`.
    fn rt_ref_read(ctx: *const TaskContext, cell: *const Cell, out: *mut u64) -> u64 => read_entry
}

/// The Rust half of `rt_ref_read`.
///
/// # Safety
///
/// Called only by `rt_ref_read`, with a live cell and room for two words
/// at `out`.
unsafe extern "C" fn read_entry(ctx: *const TaskContext, cell: *const Cell, out: *mut u64) -> u64 {
    // SAFETY: as the caller promises.
    unsafe {
        pin(&*ctx);
        let (version, words) = (*cell).read();
        out.cast::<[u64; 2]>().write_unaligned(words);
        version
    }
}

system_stack_fn! {
    /// `rt_ref_commit(ctx, cell, version, list, w0, w1) -> status`: see
    /// `crag_abi::RuntimeFn::RefCommit`.
    fn rt_ref_commit(ctx: *const TaskContext, cell: *const Cell, version: u64, list: u64, w0: u64, w1: u64) -> u64 => commit_entry
}

/// The Rust half of `rt_ref_commit`.
///
/// # Safety
///
/// Called only by `rt_ref_commit`, with a live cell, after `rt_ref_read`
/// of it gave `version`, and with a value of the elements of list type
/// `list` whose references the caller owns.
unsafe extern "C" fn commit_entry(
    ctx: *const TaskContext,
    cell: *const Cell,
    version: u64,
    list: u64,
    w0: u64,
    w1: u64,
) -> u64 {
    // SAFETY: as the caller promises.
    let (ctx, cell, (heap, types)) = unsafe { (&*ctx, &*cell, parts(&*ctx)) };
    let mut words = [w0, w1];
    let status = if cell.read() == (version, words) {
        // The value read, unchanged: nothing is written, and the cell
        // still holds a reference besides the caller's.
        // SAFETY: as the caller promises.
        unsafe {
            release_value(
                heap,
                types,
                words.as_mut_ptr().cast(),
                types.element_of(list),
            );
        }
        crag_abi::REF_COMMITTED
    } else if cell.lock(version) {
        let old = cell.replace(words);
        retire(heap, types, old, list);
        crag_abi::REF_COMMITTED
    } else {
        crag_abi::REF_CONFLICT
    };
    unpin(ctx, heap);
    status
}

system_stack_fn! {
    /// `rt_ref_done(ctx)`: see `crag_abi::RuntimeFn::RefDone`.
    fn rt_ref_done(ctx: *const TaskContext) => done_entry
}

/// The Rust half of `rt_ref_done`.
///
/// # Safety
///
/// Called only by `rt_ref_done`.
unsafe extern "C" fn done_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    unsafe { unpin(&*ctx, parts(&*ctx).0) }
}

system_stack_fn! {
    /// `rt_ref_swap(ctx, cell, list, w0, w1) -> (w0, w1)`: see
    /// `crag_abi::RuntimeFn::RefSwap`.
    fn rt_ref_swap(ctx: *const TaskContext, cell: *const Cell, list: u64, w0: u64, w1: u64) -> Words => swap_entry
}

/// The Rust half of `rt_ref_swap`.
///
/// # Safety
///
/// Called only by `rt_ref_swap`, with a live cell and a value of the
/// elements of list type `list` whose references the caller owns.
unsafe extern "C" fn swap_entry(
    ctx: *const TaskContext,
    cell: *const Cell,
    list: u64,
    w0: u64,
    w1: u64,
) -> Words {
    // SAFETY: as the caller promises.
    let (cell, (heap, types)) = unsafe { (&*cell, parts(&*ctx)) };
    cell.lock_any();
    let mut old = cell.replace([w0, w1]);
    // The caller gets references of its own: the cell's go when no
    // borrowed read can still hold the value.
    // SAFETY: the cell's reference keeps the value alive until retired.
    unsafe { retain_value(old.as_mut_ptr().cast(), types.element_of(list)) };
    retire(heap, types, old, list);
    Words(old[0], old[1])
}
