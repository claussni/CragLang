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

//! Entry points from generated code that run Rust on the system stack.

use std::sync::atomic::Ordering;

use crate::fiber::{TaskContext, Worker};
use crate::heap::Heap;
use crate::rc::Types;

/// Defines a runtime function with the C convention that generated code
/// calls on a fiber stack: it switches to the worker's system stack,
/// keeping the fiber's stack pointer in a callee-saved register, and calls
/// `$entry` there with the same arguments, at most six words, the task
/// context first. `$entry`'s result is the function's.
macro_rules! system_stack_fn {
    (
        $(#[$meta:meta])*
        fn $name:ident($($arg:ident: $ty:ty),*) $(-> $ret:ty)? => $entry:path
    ) => {
        $(#[$meta])*
        ///
        /// # Safety
        ///
        /// Only generated code may call this, on a fiber stack, with the
        /// fiber's task context.
        #[unsafe(naked)]
        pub(crate) unsafe extern "C" fn $name($($arg: $ty),*) $(-> $ret)? {
            std::arch::naked_asm!(
                "push rbx",
                "mov rbx, rsp",
                "mov rax, [rdi + {worker}]",
                "mov rsp, [rax]",
                "and rsp, -16",
                "call {entry}",
                "mov rsp, rbx",
                "pop rbx",
                "ret",
                worker = const std::mem::offset_of!($crate::fiber::TaskContext, worker),
                entry = sym $entry,
            )
        }
    };
}

/// The heap and the type descriptors of the worker running the fiber of
/// `ctx`, for the Rust half of a runtime function.
///
/// # Safety
///
/// Called on the system stack by a function `system_stack_fn!` defined,
/// while a worker runs the fiber of `ctx`. Nothing else uses the heap
/// until the function returns.
pub(crate) unsafe fn worker_of<'a>(ctx: *const TaskContext) -> (&'a mut Heap, &'a Types) {
    // SAFETY: `Worker::resume` stored the worker in the context.
    unsafe {
        let worker: *mut Worker = (*ctx).worker.load(Ordering::Relaxed);
        Worker::heap_and_types(worker)
    }
}
