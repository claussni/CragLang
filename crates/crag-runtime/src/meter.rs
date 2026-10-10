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

//! The metered tier's budgets (Implementation Plan §11.6.6).
//!
//! Metered code takes a step off the fuel in the task context at every
//! function entry and loop back-edge, and calls `rt_refuel` when the fuel
//! goes negative. A metered fiber holds the rest of its steps and hands
//! them to the fuel [`REFUEL`] at a time, so the runtime regains control
//! regularly. A fiber that is not metered starts with fuel that never runs
//! out.
//!
//! The memory budget is charged by the heap (see `heap`). When it is used
//! up, the heap empties the fuel, so the trap comes at the next step: there
//! the frame is at a safepoint whose stack map lists what it holds, which a
//! runtime function in the middle of its work is not.
//!
//! `rt_refuel` traps by jumping to `rt_trap` with the stack as the call
//! left it, so the unwinder starts at the call's return address, and the
//! call's stack map releases what the metered frame holds.

use std::mem::offset_of;
use std::sync::atomic::Ordering;

use crag_abi::{NO_POSITION, TrapKind};

use crate::fiber::{TaskContext, Worker};
use crate::stack::{RDI_SLOT, SAVE_BYTES, restore_registers, save_registers};

/// The steps one refill gives the fuel.
pub const REFUEL: u64 = 1 << 16;

/// What metered code a fiber runs may use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Meter {
    /// Function entries and loop iterations.
    pub steps: u64,
    /// Bytes the heap takes for the fiber, as the heap charges them.
    pub memory: usize,
}

/// A meter as the fiber uses it up.
#[derive(Debug)]
pub(crate) struct Metering {
    /// Steps not yet in the fuel.
    pub(crate) steps: u64,
    /// Bytes left, or none once the budget was exceeded.
    pub(crate) memory: Option<usize>,
}

impl Metering {
    pub(crate) fn new(meter: Meter) -> Metering {
        Metering {
            steps: meter.steps,
            memory: Some(meter.memory),
        }
    }
}

/// `rt_refuel(ctx)`: see `crag_abi::RuntimeFn::Refuel`.
///
/// Saves every register, asks `refuel_slow` on the system stack, and
/// either restores them and returns or traps.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_refuel(ctx: *const TaskContext) {
    std::arch::naked_asm!(
        save_registers!(),
        "mov rbx, rsp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {slow}",
        "mov rsp, rbx",
        "test rax, rax",
        "jnz 2f",
        restore_registers!(),
        "ret",
        // Trap: the kind is one less than the answer. Drop the save area,
        // so the stack pointer is at the return address as `rt_trap` finds
        // it after a call; the frame pointer is still the metered frame's.
        "2:",
        "lea rsi, [rax - 1]",
        "mov rdi, [rsp + {rdi_slot}]",
        "add rsp, {save}",
        "mov rdx, {no_position}",
        "jmp {trap}",
        worker = const offset_of!(TaskContext, worker),
        slow = sym refuel_slow,
        rdi_slot = const RDI_SLOT,
        save = const SAVE_BYTES - 8,
        no_position = const NO_POSITION,
        trap = sym crate::unwind::rt_trap,
    )
}

/// The Rust half of `rt_refuel`: zero after refilling the fuel, or one more
/// than the kind of the trap.
///
/// # Safety
///
/// Called only by `rt_refuel`, while a worker runs the fiber of `ctx`.
unsafe extern "C" fn refuel_slow(ctx: *const TaskContext) -> u64 {
    // SAFETY: `Worker::resume` stored the fiber and the worker in the
    // context, and the fiber is suspended in `rt_refuel`.
    unsafe {
        let ctx = &*ctx;
        let fiber = &mut *ctx.fiber.load(Ordering::Relaxed);
        let worker: *mut Worker = ctx.worker.load(Ordering::Relaxed);
        let (heap, _) = Worker::heap_and_types(worker);
        let Some(metering) = &mut fiber.metering else {
            ctx.fuel.store(i64::MAX, Ordering::Relaxed);
            return 0;
        };
        if heap.over_budget() {
            return TrapKind::OutOfMemory as u64 + 1;
        }
        if metering.steps == 0 {
            return TrapKind::OutOfSteps as u64 + 1;
        }
        let portion = metering.steps.min(REFUEL);
        metering.steps -= portion;
        // The step that emptied the fuel is one of the portion.
        ctx.fuel.store(portion as i64 - 1, Ordering::Relaxed);
        0
    }
}
