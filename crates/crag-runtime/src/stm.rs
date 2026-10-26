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

//! Transactions: `atomic` blocks (Plan §11.7.7, Specification §9.5), by
//! [TL2](https://doi.org/10.1007/11861201_14).
//!
//! Generated code drives a block: `rt_tx_begin`, the block's reads and
//! writes through `rt_tx_read` and `rt_tx_write`, then `rt_tx_commit`. An
//! attempt starts by reading the version clock that ref writes tick
//! (`refs`). Each read checks that its cell is unlocked and not newer than
//! that, so an attempt only ever sees a consistent state; writes go to the
//! log. The commit locks the written cells in address order, ticks the
//! clock, checks the reads again and stores the writes. A read or a commit
//! that finds a conflict makes generated code leave the block's attempt
//! and call `rt_tx_retry`, which backs off and starts another.
//!
//! An inner `atomic` block takes a savepoint; when it ends in an error,
//! `rt_tx_abort` drops the writes since. A conflict anywhere reruns the
//! outermost block.
//!
//! After [`ALONE_AFTER`] reruns, a block runs alone: it sets a bit of the
//! clock, and every other write backs out at its tick until the block is
//! done, so the next attempt cannot fail but for writes already under
//! way. The task is not preempted meanwhile, and a pause waits for the
//! block's end: the writes that wait spin on their threads, so the task
//! they wait for must keep its worker.
//!
//! The log belongs to the fiber and is kept between blocks, so a block
//! allocates only when its log outgrows earlier ones. The values a block
//! reads are borrowed, under the epoch's pin (§11.7.6); the values it
//! writes are owned by the log until the commit hands them to the cells.

use std::sync::Arc;
use std::sync::atomic::Ordering;

use crag_abi::{TX_CONFLICT, TX_OK};

use crate::epoch::{pin, retire, unpin};
use crate::fiber::{Fiber, TaskContext, Worker};
use crate::heap::Heap;
use crate::rc::{Types, release_value};
use crate::refs::{Cell, back_off, clock, enter_alone, leave_alone, tick, tick_alone, wait_alone};
use crate::sentinel::{StopReason, request};
use crate::signals::signals_of;

/// The reruns after which a block runs alone.
pub(crate) const ALONE_AFTER: u32 = 8;

/// The transaction of a fiber.
#[derive(Default)]
pub(crate) struct TxLog {
    /// How many blocks are open, the outermost first.
    depth: u32,
    /// The clock when the attempt started.
    read_version: u64,
    /// The cells read, with the versions read.
    reads: Vec<(*const Cell, u64)>,
    /// The values written, the latest last, with their list types.
    writes: Vec<Write>,
    /// The length of `writes` when each inner block began.
    savepoints: Vec<usize>,
    /// The reruns of the outermost block.
    attempts: u32,
    /// Whether the block runs alone.
    alone: bool,
    /// A pause that came while the block ran alone.
    paused: bool,
    /// The state of the random backoff.
    seed: u64,
}

struct Write {
    cell: *const Cell,
    words: [u64; 2],
    list: u64,
}

// SAFETY: the cells outlive the blocks that use them, and a log is used
// by its fiber's worker only.
unsafe impl Send for TxLog {}

impl TxLog {
    /// The latest value the attempt wrote to `cell`.
    fn written(&self, cell: *const Cell) -> Option<&Write> {
        self.writes.iter().rev().find(|w| w.cell == cell)
    }

    /// Gives up the values written since the `from`th.
    fn drop_writes(&mut self, from: usize, heap: &mut Heap, types: &Types) {
        for mut w in self.writes.drain(from..) {
            // SAFETY: the log owns the values it holds, which no cell has.
            unsafe {
                release_value(
                    heap,
                    types,
                    w.words.as_mut_ptr().cast(),
                    types.element_of(w.list),
                )
            };
        }
    }

    /// Starts an attempt of the outermost block.
    fn start(&mut self, ctx: &TaskContext) {
        if !self.alone {
            wait_alone();
        }
        pin(ctx);
        self.depth = 1;
        self.read_version = clock();
    }

    /// Forgets the attempt: its writes are given up and the task is
    /// unpinned. A task that ran alone no longer does.
    fn clear(&mut self, ctx: &TaskContext, heap: &mut Heap, types: &Types) {
        self.drop_writes(0, heap, types);
        self.reads.clear();
        self.savepoints.clear();
        self.depth = 0;
        unpin(ctx, heap);
    }

    /// Ends the outermost block, committed or not.
    fn finish(&mut self, ctx: &TaskContext, heap: &mut Heap, types: &Types) {
        self.clear(ctx, heap, types);
        self.attempts = 0;
        if self.alone {
            self.alone = false;
            leave_alone();
            if std::mem::take(&mut self.paused) {
                request(ctx, StopReason::Pause);
            }
        }
    }

    /// A random number below `2^bits`, by xorshift.
    fn random(&mut self, bits: u32) -> u64 {
        let mut x = self.seed;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.seed = x;
        x & ((1 << bits) - 1)
    }
}

/// Becomes the task that runs alone, unless it already is.
fn enter_alone_once(log: &mut TxLog) {
    if !log.alone {
        enter_alone();
        log.alone = true;
    }
}

/// The fiber running on `ctx` and its log, made on first use.
///
/// # Safety
///
/// Called by the Rust half of a runtime function for the fiber of `ctx`.
unsafe fn log_of<'a>(ctx: &TaskContext) -> &'a mut TxLog {
    // SAFETY: as the caller promises, a worker runs the fiber.
    let fiber = unsafe { &mut *ctx.fiber.load(Ordering::Relaxed) };
    fiber.tx.get_or_insert_with(|| {
        Box::new(TxLog {
            seed: ctx as *const TaskContext as u64 | 1,
            ..TxLog::default()
        })
    })
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

/// Whether the fiber runs a block alone, so that it is not preempted.
pub(crate) fn runs_alone(fiber: &Fiber) -> bool {
    fiber.tx.as_ref().is_some_and(|log| log.alone)
}

/// Keeps a pause of a fiber that runs alone for the block's end.
pub(crate) fn defer_pause(fiber: &mut Fiber) {
    if let Some(log) = &mut fiber.tx {
        log.paused = true;
    }
}

/// Ends the block of a fiber that stopped in it: its writes are given up
/// and it no longer runs alone.
pub(crate) fn stopped(fiber: &mut Fiber, ctx: &TaskContext, heap: &mut Heap, types: &Types) {
    if let Some(log) = &mut fiber.tx
        && (log.depth > 0 || log.alone)
    {
        log.finish(ctx, heap, types);
    }
}

system_stack_fn! {
    /// `rt_tx_begin(ctx)`: see `crag_abi::RuntimeFn::TxBegin`.
    fn rt_tx_begin(ctx: *const TaskContext) => begin_entry
}

/// The Rust half of `rt_tx_begin`.
///
/// # Safety
///
/// Called only by `rt_tx_begin`.
unsafe extern "C" fn begin_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    let (ctx, log, signals) = unsafe { (&*ctx, log_of(&*ctx), signals_of(&*ctx)) };
    signals.open();
    if log.depth == 0 {
        log.start(ctx);
    } else {
        log.savepoints.push(log.writes.len());
        log.depth += 1;
    }
}

system_stack_fn! {
    /// `rt_tx_read(ctx, cell, out) -> status`: see
    /// `crag_abi::RuntimeFn::TxRead`.
    fn rt_tx_read(ctx: *const TaskContext, cell: *const Cell, out: *mut u64) -> u64 => read_entry
}

/// The Rust half of `rt_tx_read`.
///
/// # Safety
///
/// Called only by `rt_tx_read`, in a block, with a live cell and room for
/// two words at `out`.
unsafe extern "C" fn read_entry(ctx: *const TaskContext, cell: *const Cell, out: *mut u64) -> u64 {
    // SAFETY: as the caller promises.
    let log = unsafe { log_of(&*ctx) };
    // SAFETY: as the caller promises.
    match unsafe { log.read(cell) } {
        Some(words) => {
            // SAFETY: as the caller promises.
            unsafe { out.cast::<[u64; 2]>().write_unaligned(words) };
            TX_OK
        }
        None => TX_CONFLICT,
    }
}

system_stack_fn! {
    /// `rt_tx_write(ctx, cell, list, w0, w1)`: see
    /// `crag_abi::RuntimeFn::TxWrite`.
    fn rt_tx_write(ctx: *const TaskContext, cell: *const Cell, list: u64, w0: u64, w1: u64) => write_entry
}

/// The Rust half of `rt_tx_write`.
///
/// # Safety
///
/// Called only by `rt_tx_write`, in a block, with a live cell and a value
/// of the elements of list type `list` whose references the caller owns.
unsafe extern "C" fn write_entry(
    ctx: *const TaskContext,
    cell: *const Cell,
    list: u64,
    w0: u64,
    w1: u64,
) {
    // SAFETY: as the caller promises.
    let (log, (heap, types)) = unsafe { (log_of(&*ctx), parts(&*ctx)) };
    let mut words = [w0, w1];
    // SAFETY: as the caller promises.
    if !unsafe { log.write(cell, words, list) } {
        // SAFETY: the cell or the log holds a reference besides the
        // caller's, and the pin keeps the cell's.
        unsafe {
            release_value(
                heap,
                types,
                words.as_mut_ptr().cast(),
                types.element_of(list),
            )
        };
    }
}

system_stack_fn! {
    /// `rt_tx_commit(ctx) -> status`: see `crag_abi::RuntimeFn::TxCommit`.
    fn rt_tx_commit(ctx: *const TaskContext) -> u64 => commit_entry
}

/// The Rust half of `rt_tx_commit`.
///
/// # Safety
///
/// Called only by `rt_tx_commit`, in a block.
unsafe extern "C" fn commit_entry(ctx: *const TaskContext) -> u64 {
    // SAFETY: as the caller promises.
    let (ctx, log, (heap, types)) = unsafe { (&*ctx, log_of(&*ctx), parts(&*ctx)) };
    let status = commit(ctx, log, heap, types);
    if status == TX_OK {
        // SAFETY: as the caller promises.
        unsafe { signals_of(ctx) }.commit(heap, types);
    }
    status
}

/// Commits the innermost block.
fn commit(ctx: &TaskContext, log: &mut TxLog, heap: &mut Heap, types: &Arc<Types>) -> u64 {
    if log.depth > 1 {
        log.savepoints.pop();
        log.depth -= 1;
        return TX_OK;
    }
    if log.writes.is_empty() {
        // Every read was checked against the start: nothing to do.
        log.finish(ctx, heap, types);
        return TX_OK;
    }
    // SAFETY: as the caller promises, the cells are live.
    let Some(old) = (unsafe { log.store() }) else {
        return TX_CONFLICT;
    };
    for (words, list) in old {
        retire(heap, types, words, list);
    }
    log.finish(ctx, heap, types);
    TX_OK
}

impl TxLog {
    /// Reads `cell` in the attempt: what it wrote there, or the cell's
    /// value, logged with its version; none on a conflict.
    ///
    /// # Safety
    ///
    /// The cell is live.
    unsafe fn read(&mut self, cell: *const Cell) -> Option<[u64; 2]> {
        if let Some(w) = self.written(cell) {
            return Some(w.words);
        }
        // SAFETY: as the caller promises.
        let c = unsafe { &*cell };
        let mut spins = 0;
        let (version, words) = loop {
            match c.try_read() {
                Some(read) => break read,
                // Writes under way end soon; they make the others
                // conflict.
                None if self.alone => back_off(&mut spins),
                None => return None,
            }
        };
        if version > self.read_version {
            return None;
        }
        self.reads.push((cell, version));
        Some(words)
    }

    /// Logs a write of `words` to `cell`; not when the attempt sees that
    /// value there already, and then the caller keeps its references.
    ///
    /// # Safety
    ///
    /// The cell is live.
    unsafe fn write(&mut self, cell: *const Cell, words: [u64; 2], list: u64) -> bool {
        let seen = match self.written(cell) {
            Some(w) => Some(w.words),
            // SAFETY: as the caller promises.
            None => unsafe { &*cell }
                .try_read()
                .filter(|(v, _)| self.reads.iter().any(|&(c, r)| c == cell && r == *v))
                .map(|(_, w)| w),
        };
        if seen == Some(words) {
            return false;
        }
        self.writes.push(Write { cell, words, list });
        true
    }

    /// Commits the outermost block's writes, TL2's commit: the values the
    /// cells held, with their list types, to retire; none on a conflict.
    /// The writes that lost to later ones of the same cell stay in the log.
    ///
    /// # Safety
    ///
    /// The cells are live.
    unsafe fn store(&mut self) -> Option<Vec<([u64; 2], u64)>> {
        let log = self;
        // The latest write of each cell, in address order.
        let mut cells: Vec<usize> = (0..log.writes.len()).collect();
        cells.sort_by_key(|&i| (log.writes[i].cell, std::cmp::Reverse(i)));
        cells.dedup_by_key(|&mut i| log.writes[i].cell);
        // The versions the locks were taken from.
        let mut locked: Vec<u64> = Vec::with_capacity(cells.len());
        let unlock = |locked: &[u64], log: &TxLog| {
            for (&i, &version) in cells.iter().zip(locked) {
                // SAFETY: the cell is live; the commit holds its lock.
                unsafe { &*log.writes[i].cell }.unlock(version);
            }
        };
        for &i in &cells {
            // SAFETY: as the caller promises, the cells are live.
            let cell = unsafe { &*log.writes[i].cell };
            let mut spins = 0;
            loop {
                let version = cell.version();
                if version & 1 == 0 {
                    if cell.lock(version) {
                        locked.push(version);
                        break;
                    }
                } else if !log.alone {
                    unlock(&locked, log);
                    return None;
                }
                back_off(&mut spins);
            }
        }
        let version = if log.alone {
            tick_alone()
        } else {
            match tick() {
                Some(version) => version,
                None => {
                    unlock(&locked, log);
                    return None;
                }
            }
        };
        // No other write came in between when the clock moved by this one.
        if version != log.read_version + 2 {
            let valid = log.reads.iter().all(|&(cell, read)| {
                match cells.iter().position(|&i| log.writes[i].cell == cell) {
                    Some(k) => locked[k] == read,
                    // SAFETY: the cell is live.
                    None => unsafe { &*cell }.version() == read,
                }
            });
            if !valid {
                unlock(&locked, log);
                return None;
            }
        }
        let mut old = Vec::with_capacity(cells.len());
        for &i in &cells {
            let w = &log.writes[i];
            // SAFETY: the cell is live and locked by this commit.
            let cell = unsafe { &*w.cell };
            old.push((cell.store(w.words), w.list));
            cell.unlock(version);
        }
        // The cells took the values that won; the others are given up.
        let mut won = vec![false; log.writes.len()];
        for &i in &cells {
            won[i] = true;
        }
        let mut k = 0;
        log.writes.retain(|_| {
            k += 1;
            !won[k - 1]
        });
        Some(old)
    }
}

system_stack_fn! {
    /// `rt_tx_abort(ctx)`: see `crag_abi::RuntimeFn::TxAbort`.
    fn rt_tx_abort(ctx: *const TaskContext) => abort_entry
}

/// The Rust half of `rt_tx_abort`.
///
/// # Safety
///
/// Called only by `rt_tx_abort`, in a block.
unsafe extern "C" fn abort_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    let (ctx, log, (heap, types)) = unsafe { (&*ctx, log_of(&*ctx), parts(&*ctx)) };
    // SAFETY: as the caller promises.
    unsafe { signals_of(ctx) }.fail(heap, types);
    match log.savepoints.pop() {
        Some(from) => {
            log.drop_writes(from, heap, types);
            log.depth -= 1;
        }
        None => log.finish(ctx, heap, types),
    }
}

system_stack_fn! {
    /// `rt_tx_retry(ctx)`: see `crag_abi::RuntimeFn::TxRetry`.
    fn rt_tx_retry(ctx: *const TaskContext) => retry_entry
}

/// The Rust half of `rt_tx_retry`.
///
/// # Safety
///
/// Called only by `rt_tx_retry`, in a block.
unsafe extern "C" fn retry_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    let (ctx, log, (heap, types)) = unsafe { (&*ctx, log_of(&*ctx), parts(&*ctx)) };
    // SAFETY: as the caller promises.
    unsafe { signals_of(ctx) }.conflict(true, heap, types);
    log.clear(ctx, heap, types);
    log.attempts += 1;
    if log.attempts >= ALONE_AFTER {
        enter_alone_once(log);
    } else {
        // Randomized exponential backoff, so that the attempts that
        // collided do not collide again.
        let spins = log.random(log.attempts.min(10) + 4);
        for _ in 0..spins {
            std::hint::spin_loop();
        }
    }
    log.start(ctx);
}

/// Loom model (Plan §11.7.13): two transfers between two cells commit or
/// conflict, and a third transaction that reads both sees their total.
#[cfg(all(test, loom))]
mod loom_models {
    use super::*;
    use crate::sync::Arc;

    /// One attempt of a transfer of `amount` from `from` to `to`: whether
    /// it committed.
    fn transfer(from: &Cell, to: &Cell, amount: u64) -> bool {
        let mut log = TxLog {
            depth: 1,
            read_version: clock(),
            ..TxLog::default()
        };
        // SAFETY: the cells outlive the attempt.
        unsafe {
            let (Some(x), Some(y)) = (log.read(from), log.read(to)) else {
                return false;
            };
            log.write(from, [x[0] - amount, 0], 0);
            log.write(to, [y[0] + amount, 0], 0);
            log.store().is_some()
        }
    }

    #[test]
    fn loom_model_tx_commit() {
        crate::sync::model(|| {
            let a = Arc::new(Cell::new([10, 0]));
            let b = Arc::new(Cell::new([10, 0]));
            let one = {
                let (a, b) = (a.clone(), b.clone());
                loom::thread::spawn(move || transfer(&a, &b, 1))
            };
            let two = {
                let (a, b) = (a.clone(), b.clone());
                loom::thread::spawn(move || transfer(&b, &a, 2))
            };
            let mut log = TxLog {
                depth: 1,
                read_version: clock(),
                ..TxLog::default()
            };
            // The transfers may commit between the two reads.
            // SAFETY: the cells outlive the attempt.
            let x = unsafe { log.read(&*a) };
            loom::thread::yield_now();
            // SAFETY: as above.
            let y = unsafe { log.read(&*b) };
            if let (Some(x), Some(y)) = (x, y) {
                assert_eq!(x[0] + y[0], 20, "an inconsistent read");
            }
            let (one, two) = (one.join().unwrap(), two.join().unwrap());
            let (x, y) = (a.read().1[0], b.read().1[0]);
            let moved = i64::from(one) - 2 * i64::from(two);
            assert_eq!((x as i64, y as i64), (10 - moved, 10 + moved));
        });
    }
}
