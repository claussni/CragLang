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

//! Traps and the unwinder (Plan §11.4.14).
//!
//! A check that fails releases what its frame holds and calls `rt_trap`,
//! which never returns. The frames below it are suspended at calls, and the
//! stack map of each call lists the slots of the boxes the frame holds
//! across it, each with a reference of its own. `rt_trap` walks the
//! frame-pointer chain to the fiber's first frame, releases those boxes,
//! records the trap and ends the fiber.
//!
//! Crag has no trap handlers yet (Specification §8.3), so a trap always ends
//! its task.

use std::sync::atomic::Ordering;

use crag_abi::{CodeObject, FuncId, NO_POSITION, TrapKind};

use crate::die;
use crate::fiber::{STATUS_TRAPPED, TaskContext, Worker};
use crate::rc::drop_box;

/// What the runtime knows of the loaded code: the stack maps of its calls,
/// by return address, and where each function lies.
#[derive(Debug, Default)]
pub struct CodeMap {
    /// Return addresses, sorted, with the offsets of the slots that hold
    /// boxes from the stack pointer at the call.
    safepoints: Vec<(usize, Box<[u32]>)>,
    /// The start and end of each function's code, sorted.
    functions: Vec<(usize, usize, FuncId)>,
}

impl CodeMap {
    pub fn new() -> CodeMap {
        CodeMap::default()
    }

    /// Adds a code object loaded with its entry point at `entry`.
    pub fn add(&mut self, func: FuncId, entry: usize, object: &CodeObject) {
        let base = entry - object.entry as usize;
        self.functions.push((base, base + object.code.len(), func));
        self.functions.sort_unstable_by_key(|f| f.0);
        for map in &object.stack_maps {
            let ret = base + map.return_offset as usize;
            self.safepoints.push((ret, map.slots.clone().into()));
        }
        self.safepoints.sort_unstable_by_key(|s| s.0);
    }

    /// The function whose code holds `pc`.
    pub fn function_at(&self, pc: usize) -> Option<FuncId> {
        let i = self.functions.partition_point(|f| f.0 <= pc);
        let &(start, end, func) = self.functions.get(i.checked_sub(1)?)?;
        (start..end).contains(&pc).then_some(func)
    }

    /// The slots of the call returning to `ret`; none for a call that holds
    /// no box across it, or for code not in the map.
    fn slots(&self, ret: usize) -> &[u32] {
        match self.safepoints.binary_search_by_key(&ret, |s| s.0) {
            Ok(i) => &self.safepoints[i].1,
            Err(_) => &[],
        }
    }
}

/// Why and where a fiber stopped.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Trap {
    pub kind: TrapKind,
    /// The byte offset of the expression that trapped in its module's
    /// source, if code generation knew it.
    pub position: Option<u32>,
    /// The function that trapped, then the functions of the frames below it
    /// in turn, as far as the code map holds them.
    pub stack: Vec<FuncId>,
}

/// `rt_trap(ctx, kind, position)`: see `crag_abi::RuntimeFn::Trap`.
///
/// Passes where the trapping frame's return address lies and its frame
/// pointer to `trap_entry`, on the system stack.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_trap(ctx: *const TaskContext, kind: u64, position: u64) -> ! {
    std::arch::naked_asm!(
        "mov rcx, rsp",
        "mov r8, rbp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {entry}",
        "ud2",
        worker = const std::mem::offset_of!(TaskContext, worker),
        entry = sym trap_entry,
    )
}

/// The Rust half of `rt_trap`: unwinds the fiber's stack, records the trap
/// and switches to the worker as if the fiber had finished.
///
/// # Safety
///
/// Called only by `rt_trap`. `ret` is where the return address into the
/// trapping frame lies, and `fp` is that frame's frame pointer.
unsafe extern "C" fn trap_entry(
    ctx: *const TaskContext,
    kind: u64,
    position: u64,
    ret: *const usize,
    fp: usize,
) -> ! {
    // SAFETY: `Worker::resume` stored the worker and the fiber in the
    // context, and the fiber's frames are suspended at calls.
    unsafe {
        let worker: *mut Worker = (*ctx).worker.load(Ordering::Relaxed);
        let trap = Trap {
            kind: TrapKind::from_index(kind).unwrap_or_else(|| die("a trap of no kind")),
            position: (position != NO_POSITION).then_some(position as u32),
            stack: unwind(worker, ret, fp),
        };
        // The fiber takes the trap, so nothing on this stack owns anything
        // when `leave` abandons it.
        (*(*ctx).fiber.load(Ordering::Relaxed)).trap = Some(trap);
        (*ctx).status.store(STATUS_TRAPPED, Ordering::Relaxed);
        leave(worker)
    }
}

/// Releases the boxes every frame below the trapping one holds, from the
/// return address at `ret` and the frame pointer `fp` down the chain to the
/// fiber's first frame, whose saved frame pointer is zero. Returns the
/// functions of the frames the code map knows, the trapping one first.
///
/// # Safety
///
/// As for `trap_entry`.
unsafe fn unwind(worker: *mut Worker, mut ret: *const usize, mut fp: usize) -> Vec<FuncId> {
    let mut stack = Vec::new();
    // SAFETY: as the caller promises. Each frame's stack pointer at its call
    // lies just above the return address; the frame pointer of the frame
    // below holds the next link of the chain, and the return address
    // into that frame lies just above it.
    unsafe {
        let code = Worker::code(worker);
        let (heap, types) = Worker::heap_and_types(worker);
        loop {
            let sp = ret as usize + 8;
            stack.extend(code.function_at(ret.read()));
            for &offset in code.slots(ret.read()) {
                let ptr = ((sp + offset as usize) as *const *mut u8).read();
                drop_box(heap, types, ptr);
            }
            if fp == 0 {
                return stack;
            }
            ret = (fp + 8) as *const usize;
            fp = (fp as *const usize).read();
        }
    }
}

/// Continues the worker at the switch frame its `resume` left on the
/// system stack, abandoning the Rust frames below it, which own nothing.
///
/// # Safety
///
/// The worker is running a fiber, from whose `resume` it switched.
#[unsafe(naked)]
unsafe extern "C" fn leave(worker: *mut Worker) -> ! {
    std::arch::naked_asm!(
        "mov rsp, [rdi]",
        "pop r15",
        "pop r14",
        "pop r13",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
    )
}
