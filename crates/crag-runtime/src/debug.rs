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

//! The debugger's half in the runtime (Implementation Plan §11.8.6).
//!
//! Baseline code has a step at the start of every statement: a check of a
//! flag, the first word of a cell the loader makes for the step. While it
//! is clear, a step costs a load and a branch. When it is set, the code
//! copies the words of the locals that hold values to its frame and calls
//! `rt_step`, which decides whether the task stops there: at a breakpoint,
//! or at the step a task that was resumed stepping is waiting for. A task
//! that stops is suspended until the debugger resumes it, and the words of
//! its locals are kept for the debugger to show.
//!
//! Stepping compares stack depths: how far a frame lies below the top of
//! its fiber's stack, which stays the same when the stack moves.

use std::collections::{HashMap, HashSet};
use std::sync::{LazyLock, Mutex};

use crag_abi::FuncId;

use crate::fiber::{TaskContext, Worker};
use crate::sched::{FiberRef, WaitReason, suspend, wake};

/// How a stopped task goes on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resume {
    /// To the next breakpoint.
    Continue,
    /// To the next step anywhere.
    Into,
    /// To the next step in the same frame or one below it.
    Over,
    /// To the next step in a frame below this one.
    Out,
}

impl Resume {
    pub fn from_index(index: u8) -> Option<Resume> {
        Some(match index {
            0 => Resume::Continue,
            1 => Resume::Into,
            2 => Resume::Over,
            3 => Resume::Out,
            _ => return None,
        })
    }
}

/// A task stopped at a step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Paused {
    /// The task, by its context's address, which stays while it lives.
    pub task: u64,
    pub func: FuncId,
    pub step: u32,
    /// The words of the step's locals, in order.
    pub words: Vec<u64>,
    /// The functions of the frames that called it, innermost first, as far
    /// as the code map holds them.
    pub callers: Vec<FuncId>,
}

struct Stopped {
    paused: Paused,
    depth: usize,
    fiber: FiberRef,
}

#[derive(Default)]
struct State {
    breaks: HashSet<(FuncId, u32)>,
    /// Tasks resumed stepping: how, and from what depth.
    stepping: HashMap<u64, (Resume, usize)>,
    stopped: Vec<Stopped>,
}

static STATE: LazyLock<Mutex<State>> = LazyLock::new(Mutex::default);

fn state() -> std::sync::MutexGuard<'static, State> {
    STATE.lock().unwrap_or_else(|e| e.into_inner())
}

/// Sets the breakpoints: steps by function and index.
pub fn set_breakpoints(breaks: impl IntoIterator<Item = (FuncId, u32)>) {
    state().breaks = breaks.into_iter().collect();
}

/// The tasks stopped now, in the order they stopped.
pub fn paused() -> Vec<Paused> {
    state().stopped.iter().map(|s| s.paused.clone()).collect()
}

/// Whether a task resumed stepping has not stopped again yet.
pub fn stepping() -> bool {
    !state().stepping.is_empty()
}

/// Resumes a stopped task; false if it is not stopped.
pub fn resume(task: u64, how: Resume) -> bool {
    let mut state = state();
    let Some(i) = state.stopped.iter().position(|s| s.paused.task == task) else {
        return false;
    };
    let stopped = state.stopped.remove(i);
    if how != Resume::Continue {
        state.stepping.insert(task, (how, stopped.depth));
    }
    drop(state);
    wake(stopped.fiber, [0, 0]);
    true
}

/// Resumes every stopped task and forgets the breakpoints and stepping,
/// as when the app stops.
pub fn release_all() {
    let mut state = state();
    state.breaks.clear();
    state.stepping.clear();
    let stopped = std::mem::take(&mut state.stopped);
    drop(state);
    for s in stopped {
        wake(s.fiber, [0, 0]);
    }
}

suspending_fn! {
    /// `rt_step(ctx, func, step, words, count, fp)`: see
    /// `crag_abi::RuntimeFn::Step`.
    fn rt_step(ctx: *const TaskContext, func: u64, step: u64, words: *const u64, count: u64, fp: u64) => step_entry
}

/// The Rust half of `rt_step`: stops the task if it is to.
///
/// # Safety
///
/// Called only by `rt_step`: `words` holds `count` words in the calling
/// frame, whose frame pointer is `fp`, on the fiber of `ctx`.
unsafe extern "C" fn step_entry(
    ctx: *const TaskContext,
    func: u64,
    step: u64,
    words: *const u64,
    count: u64,
    fp: u64,
) {
    // SAFETY: as the caller promises.
    let ctx_ref = unsafe { &*ctx };
    let task = ctx as u64;
    let (func, step) = (FuncId(func as u32), step as u32);
    // SAFETY: a worker runs the fiber of `ctx`.
    let top = unsafe {
        (*ctx_ref.fiber.load(std::sync::atomic::Ordering::Relaxed))
            .stack
            .top()
    };
    let depth = top.saturating_sub(fp as usize);
    let mut state = state();
    let stop = state.breaks.contains(&(func, step))
        || match state.stepping.get(&task) {
            Some((Resume::Into, _)) => true,
            Some((Resume::Over, from)) => depth <= *from,
            Some((Resume::Out, from)) => depth < *from,
            Some((Resume::Continue, _)) | None => false,
        };
    if !stop {
        return;
    }
    state.stepping.remove(&task);
    // SAFETY: as the caller promises.
    let words = unsafe { std::slice::from_raw_parts(words, count as usize) }.to_vec();
    // SAFETY: the worker's code map stays while it runs the fiber.
    let callers = unsafe {
        let worker: *mut Worker = ctx_ref.worker.load(std::sync::atomic::Ordering::Relaxed);
        crate::unwind::callers(Worker::code(worker), fp as usize)
    };
    // SAFETY: called by the Rust half of a suspending function, for its
    // fiber.
    let fiber = unsafe { suspend(ctx_ref, WaitReason::Debug) };
    state.stopped.push(Stopped {
        paused: Paused {
            task,
            func,
            step,
            words,
            callers,
        },
        depth,
        fiber,
    });
}
