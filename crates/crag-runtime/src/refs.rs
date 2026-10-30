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
//! versions of all cells are ordered, as transactions need (§11.7.7). It
//! takes it while it holds the lock and before it stores, so that a write
//! that finds a transaction running alone can back out unseen.
//!
//! An update whose closure is `v ⊕ k` on an integer, as a counter's, gives
//! the same result in any order, so `rt_ref_apply` does it under the lock
//! instead of reading and committing, and it never reruns (§11.7.8).

use std::sync::Arc;
use std::sync::atomic::Ordering;

use crate::sync::{AtomicU64, fence};

use crate::epoch::{pin, retire, unpin};
use crate::fiber::{TaskContext, Worker};
use crate::heap::Heap;
use crate::io::Words;
use crate::rc::{Types, release_value, retain_value};
use crate::signals::signals_of;
use crate::stm::{conflicted, running};

/// A ref cell, as generated code lays it out.
#[repr(C)]
pub(crate) struct Cell {
    version: AtomicU64,
    value: [AtomicU64; 2],
}

#[cfg(not(loom))]
const _: () = assert!(size_of::<Cell>() == crag_abi::REF_CELL_SIZE as usize);

/// The last version a write gave a cell, with [`ALONE`] while a task
/// runs alone.
#[cfg(not(loom))]
static CLOCK: AtomicU64 = AtomicU64::new(0);

#[cfg(loom)]
loom::lazy_static! {
    static ref CLOCK: AtomicU64 = AtomicU64::new(0);
}

/// The bit of the clock that is set while a transaction runs alone
/// (§11.7.7): every other write backs out until it is clear.
const ALONE: u64 = 1 << 63;

/// The clock, as a transaction reads it when it starts.
pub(crate) fn clock() -> u64 {
    CLOCK.load(Ordering::SeqCst) & !ALONE
}

/// Takes a new version for a write, which holds its cells' locks: none
/// while another task runs alone.
pub(crate) fn tick() -> Option<u64> {
    let before = CLOCK.fetch_add(2, Ordering::SeqCst);
    (before & ALONE == 0).then_some(before + 2)
}

/// Takes a new version for the write of the task that runs alone.
pub(crate) fn tick_alone() -> u64 {
    (CLOCK.fetch_add(2, Ordering::SeqCst) & !ALONE) + 2
}

/// Waits until no task runs alone. The task that does is never preempted
/// or suspended, so it is running on some worker and ends soon.
pub(crate) fn wait_alone() {
    let mut spins = 0;
    while CLOCK.load(Ordering::SeqCst) & ALONE != 0 {
        back_off(&mut spins);
    }
}

/// Makes the calling task the one that runs alone, once no other does.
pub(crate) fn enter_alone() {
    loop {
        wait_alone();
        if CLOCK.fetch_or(ALONE, Ordering::SeqCst) & ALONE == 0 {
            return;
        }
    }
}

pub(crate) fn leave_alone() {
    CLOCK.fetch_and(!ALONE, Ordering::SeqCst);
}

/// Waits a little longer each time a cell is locked.
pub(crate) fn back_off(spins: &mut u32) {
    if *spins < 64 {
        *spins += 1;
        std::hint::spin_loop();
    } else {
        std::thread::yield_now();
    }
}

impl Cell {
    /// A cell holding `words`, at version 0, as generated code makes one.
    #[cfg(all(test, loom))]
    pub(crate) fn new(words: [u64; 2]) -> Cell {
        Cell {
            version: AtomicU64::new(0),
            value: words.map(AtomicU64::new),
        }
    }

    /// The version and the value, once no write is under way.
    pub(crate) fn read(&self) -> (u64, [u64; 2]) {
        let mut spins = 0;
        loop {
            if let Some(read) = self.try_read() {
                return read;
            }
            back_off(&mut spins);
        }
    }

    /// The version and the value, unless a write is under way.
    pub(crate) fn try_read(&self) -> Option<(u64, [u64; 2])> {
        let version = self.version.load(Ordering::Acquire);
        if version & 1 != 0 {
            return None;
        }
        let words = self.value.each_ref().map(|w| w.load(Ordering::Relaxed));
        fence(Ordering::Acquire);
        (self.version.load(Ordering::Relaxed) == version).then_some((version, words))
    }

    /// The version, with the lock bit.
    pub(crate) fn version(&self) -> u64 {
        self.version.load(Ordering::Acquire)
    }

    /// Locks the cell if it still holds `version`.
    pub(crate) fn lock(&self, version: u64) -> bool {
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

    /// Stores a value in the locked cell: the old one.
    pub(crate) fn store(&self, words: [u64; 2]) -> [u64; 2] {
        let old = self.value.each_ref().map(|w| w.load(Ordering::Relaxed));
        for (w, word) in self.value.iter().zip(words) {
            w.store(word, Ordering::Relaxed);
        }
        old
    }

    /// Unlocks the cell with `version`.
    pub(crate) fn unlock(&self, version: u64) {
        self.version.store(version, Ordering::Release);
    }

    /// Replaces the value of the cell, locked from `version`, and unlocks
    /// it with a new version: the old value. While another task runs
    /// alone, nothing changes and the cell is unlocked as it was.
    fn replace(&self, version: u64, words: [u64; 2]) -> Option<[u64; 2]> {
        let Some(new) = tick() else {
            self.unlock(version);
            return None;
        };
        let old = self.store(words);
        self.unlock(new);
        Some(old)
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
    if let Some(log) = unsafe { running(&*ctx) } {
        // SAFETY: as the caller promises.
        let words = unsafe { log.read(cell) }.unwrap_or_else(|| {
            conflicted(unsafe { &*ctx });
            [0, 0]
        });
        // SAFETY: as the caller promises.
        unsafe { out.cast::<[u64; 2]>().write_unaligned(words) };
        return 0;
    }
    // SAFETY: as the caller promises.
    unsafe {
        pin(&*ctx);
        signals_of(&*ctx).open();
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
    // SAFETY: as the caller promises.
    if let Some(log) = unsafe { running(ctx) } {
        // SAFETY: as the caller promises.
        if !unsafe { log.write(cell, words, list) } {
            // SAFETY: the cell or the log holds a reference besides the
            // caller's.
            unsafe { release_value(heap, types, words.as_mut_ptr().cast(), types.cell_of(list)) };
        }
        return crag_abi::REF_COMMITTED;
    }
    let status = if cell.read() == (version, words) {
        // The value read, unchanged: nothing is written, and the cell
        // still holds a reference besides the caller's.
        // SAFETY: as the caller promises.
        unsafe {
            release_value(heap, types, words.as_mut_ptr().cast(), types.cell_of(list));
        }
        crag_abi::REF_COMMITTED
    } else {
        loop {
            if !cell.lock(version) {
                // The update reruns with a value of its own.
                // SAFETY: as the caller promises.
                unsafe {
                    release_value(heap, types, words.as_mut_ptr().cast(), types.cell_of(list));
                }
                break crag_abi::REF_CONFLICT;
            }
            if let Some(old) = cell.replace(version, words) {
                retire(heap, types, old, list);
                break crag_abi::REF_COMMITTED;
            }
            wait_alone();
        }
    };
    // SAFETY: as the caller promises.
    let signals = unsafe { signals_of(ctx) };
    if status == crag_abi::REF_COMMITTED {
        signals.commit(heap, types);
    } else {
        signals.conflict(false, heap, types);
    }
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
    // A transaction's reads end with it.
    // SAFETY: as the caller promises.
    if unsafe { running(&*ctx) }.is_some() {
        return;
    }
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = parts(&*ctx);
        signals_of(&*ctx).fail(heap, types);
        unpin(&*ctx, heap);
    }
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
    // SAFETY: as the caller promises.
    if let Some(log) = unsafe { running(&*ctx) } {
        let mut new = [w0, w1];
        // SAFETY: as the caller promises.
        let Some(mut old) = (unsafe { log.read(cell) }) else {
            conflicted(unsafe { &*ctx });
            // SAFETY: the caller's references to the new value.
            unsafe { release_value(heap, types, new.as_mut_ptr().cast(), types.cell_of(list)) };
            return Words(0, 0);
        };
        // SAFETY: the cell or the log holds the old value until the
        // attempt ends, and the caller gets references of its own.
        unsafe {
            retain_value(old.as_mut_ptr().cast(), types.cell_of(list));
            if !log.write(cell, new, list) {
                release_value(heap, types, new.as_mut_ptr().cast(), types.cell_of(list));
            }
        }
        return Words(old[0], old[1]);
    }
    let mut old = loop {
        let version = cell.lock_any();
        if let Some(old) = cell.replace(version, [w0, w1]) {
            break old;
        }
        wait_alone();
    };
    // The caller gets references of its own: the cell's go when no
    // borrowed read can still hold the value.
    // SAFETY: the cell's reference keeps the value alive until retired.
    unsafe { retain_value(old.as_mut_ptr().cast(), types.cell_of(list)) };
    retire(heap, types, old, list);
    Words(old[0], old[1])
}

/// `v ⊕ k` for an integer of type `ty` (see `crag_abi::RuntimeFn::RefApply`),
/// or `None` when it is outside the type.
fn apply(op: u64, ty: u64, v: u64, k: u64) -> Option<u64> {
    let unsigned = ty & crag_abi::REF_UNSIGNED != 0;
    let bits = ty & !crag_abi::REF_UNSIGNED;
    // A value is kept in 64 bits, sign- or zero-extended from its width.
    let widen = |x: u64| -> i128 {
        if unsigned {
            x.into()
        } else {
            (x as i64).into()
        }
    };
    let (a, b) = (widen(v), widen(k));
    let result = match op {
        crag_abi::REF_ADD => a + b,
        crag_abi::REF_SUB => a - b,
        crag_abi::REF_MUL => a.checked_mul(b)?,
        crag_abi::REF_AND => a & b,
        crag_abi::REF_OR => a | b,
        crag_abi::REF_XOR => a ^ b,
        crag_abi::REF_MIN => a.min(b),
        crag_abi::REF_MAX => a.max(b),
        _ => unreachable!("no operation {op}"),
    };
    let (least, greatest) = if unsigned {
        (0, (1i128 << bits) - 1)
    } else {
        (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
    };
    (least..=greatest)
        .contains(&result)
        .then_some(result as u64)
}

system_stack_fn! {
    /// `rt_ref_apply(ctx, cell, op, ty, k, list) -> status`: see
    /// `crag_abi::RuntimeFn::RefApply`.
    fn rt_ref_apply(ctx: *const TaskContext, cell: *const Cell, op: u64, ty: u64, k: u64, list: u64) -> u64 => apply_entry
}

/// The Rust half of `rt_ref_apply`.
///
/// # Safety
///
/// Called only by `rt_ref_apply`, with a live cell holding an integer of
/// type `ty`.
unsafe extern "C" fn apply_entry(
    ctx: *const TaskContext,
    cell: *const Cell,
    op: u64,
    ty: u64,
    k: u64,
    list: u64,
) -> u64 {
    // In a transaction the update is a read and a write of the log, which
    // the commit checks with the others.
    // SAFETY: as the caller promises.
    if let Some(log) = unsafe { running(&*ctx) } {
        // SAFETY: as the caller promises.
        let Some(words) = (unsafe { log.read(cell) }) else {
            conflicted(unsafe { &*ctx });
            return crag_abi::REF_COMMITTED;
        };
        let Some(result) = apply(op, ty, words[0], k) else {
            return crag_abi::REF_OVERFLOW;
        };
        // SAFETY: an integer holds no references.
        unsafe { log.write(cell, [result, words[1]], list) };
        return crag_abi::REF_COMMITTED;
    }
    // SAFETY: as the caller promises.
    let cell = unsafe { &*cell };
    loop {
        // An integer holds no references, so nothing is borrowed or
        // retired, and no task needs to be pinned.
        let version = cell.lock_any();
        let words = cell.value.each_ref().map(|w| w.load(Ordering::Relaxed));
        let Some(result) = apply(op, ty, words[0], k) else {
            cell.unlock(version);
            return crag_abi::REF_OVERFLOW;
        };
        if cell.replace(version, [result, words[1]]).is_some() {
            return crag_abi::REF_COMMITTED;
        }
        wait_alone();
    }
}

/// Loom model (Plan §11.7.13): a reader of a cell that a writer replaces
/// twice never sees a torn value or a version going back.
#[cfg(all(test, loom))]
mod loom_models {
    use super::*;
    use crate::sync::Arc;

    #[test]
    fn loom_model_ref_cell() {
        crate::sync::model(|| {
            let cell = Arc::new(Cell::new([0, 0]));
            let writer = {
                let cell = cell.clone();
                loom::thread::spawn(move || {
                    for n in 1..=2 {
                        let version = cell.lock_any();
                        assert!(cell.replace(version, [n, n]).is_some());
                    }
                })
            };
            // The reader reads until it sees the last write, yielding so
            // that loom runs the writer in between.
            let mut last = 0;
            while last < 4 {
                if let Some((version, [a, b])) = cell.try_read() {
                    assert_eq!(a, b, "a torn value");
                    assert!(version >= last && version % 2 == 0);
                    last = version;
                }
                loom::thread::yield_now();
            }
            writer.join().unwrap();
            let (version, words) = cell.read();
            assert_eq!(words, [2, 2]);
            assert_eq!(version, 4);
        });
    }
}
