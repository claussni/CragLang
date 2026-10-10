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

//! The Crag runtime.
//!
//! M0 scope (Implementation Plan §11.3.1 to §11.3.4 and §11.3.9): fibers and
//! the context switch, stack growth by copying, the side stack, the sentinel
//! stop request and the stress harness. M1 adds the allocator, reference
//! counting, lists and maps, and traps (§11.4.11 to §11.4.14). M3 adds the
//! metered tier's budgets (§11.6.6).
//!
//! Runtime discipline (Compiler Architecture §2.1): no thread-locals, no
//! callbacks into Crag code from the runtime stack, panics abort in images
//! (see [`abort_on_panic`]).
//!
//! # What may be on a fiber stack
//!
//! A fiber stack is copied to a new address when it grows, so it may hold
//! only frames the runtime can relocate: frames of generated code, the entry
//! stub, and the register save areas of the assembly routines in this crate.
//! Those keep a frame-pointer chain and no other pointer into the stack. Rust
//! code never runs on a fiber stack; the assembly routines switch to the
//! worker's system stack before they call into Rust.

#[cfg(not(all(target_arch = "x86_64", unix)))]
compile_error!("the runtime's context switch is written for x86-64 Unix only");

#[macro_use]
mod system;

pub mod codec;
pub mod fiber;
pub mod heap;
pub mod list;
pub mod map;
pub mod meter;
pub mod print;
pub mod rc;
pub mod sentinel;
pub mod side_stack;
pub mod stack;
pub mod stress;
#[cfg(test)]
mod testing;
pub mod unwind;

pub use codec::{NotSolid, encode_value};
pub use fiber::{Fiber, FiberConfig, FiberState, TaskContext, Worker};
pub use heap::{Heap, alloc_box};
pub use meter::Meter;
pub use print::{PrintLimits, print_value, release_value};
pub use rc::{Types, release_box};
pub use sentinel::{StopHandle, StopReason, request_stop};
pub use unwind::{CodeMap, Trap};

use crag_abi::RuntimeFn;

/// The address of a runtime function, for the loader's symbol table.
pub fn runtime_fn_addr(func: RuntimeFn) -> usize {
    match func {
        RuntimeFn::Morestack => stack::rt_morestack as *const () as usize,
        RuntimeFn::SideGrow => side_stack::rt_side_grow as *const () as usize,
        RuntimeFn::Alloc => heap::rt_alloc as *const () as usize,
        RuntimeFn::Release => rc::rt_release as *const () as usize,
        RuntimeFn::ListPush => list::rt_list_push as *const () as usize,
        RuntimeFn::ListElem => list::rt_list_elem as *const () as usize,
        RuntimeFn::ListSlice => list::rt_list_slice as *const () as usize,
        RuntimeFn::MapInsert => map::rt_map_insert as *const () as usize,
        RuntimeFn::MapGet => map::rt_map_get as *const () as usize,
        RuntimeFn::Trap => unwind::rt_trap as *const () as usize,
        RuntimeFn::Refuel => meter::rt_refuel as *const () as usize,
    }
}

/// Makes every panic in this process end it at once, without unwinding.
/// Image processes call this first thing at startup.
///
/// A panic in an image has nowhere to unwind to: below the runtime's frames
/// lie generated code and assembly, which carry no unwinding information. The
/// hook runs before unwinding starts, prints the panic as usual and aborts,
/// so no destructor runs and no frame is unwound.
///
/// The workspace does not set `panic = "abort"`, because the host process
/// shares it and cancels queries by unwinding. Memory safety does not rest
/// on this hook: the runtime's entry points from assembly are C-convention
/// functions, and a panic that tries to leave one aborts anyway. The hook
/// makes the abort happen at the panic, with its message.
pub fn abort_on_panic() {
    let report = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        report(info);
        std::process::abort();
    }));
}

/// Reports a condition the runtime cannot recover from and ends the process.
/// It does not panic, so it behaves the same with or without the hook and
/// never unwinds through assembly frames.
pub(crate) fn die(message: &str) -> ! {
    eprintln!("crag runtime: {message}");
    std::process::abort()
}
