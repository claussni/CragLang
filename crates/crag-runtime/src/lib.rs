//! The Crag runtime.
//!
//! M0 scope (Implementation Plan §11.3.1 to §11.3.4 and §11.3.9): fibers and
//! the context switch, stack growth by copying, the side stack, the sentinel
//! stop request and the stress harness.
//!
//! Runtime discipline (Compiler Architecture §2.1): no thread-locals, no
//! callbacks into Crag code from the runtime stack, panics abort.
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

pub mod fiber;
pub mod sentinel;
pub mod side_stack;
pub mod stack;
pub mod stress;

pub use fiber::{Fiber, FiberConfig, FiberState, TaskContext, Worker};
pub use sentinel::{StopHandle, StopReason, request_stop};

use crag_abi::RuntimeFn;

/// The address of a runtime function, for the loader's symbol table.
pub fn runtime_fn_addr(func: RuntimeFn) -> usize {
    match func {
        RuntimeFn::Morestack => stack::rt_morestack as *const () as usize,
    }
}

/// Reports a condition the runtime cannot recover from and ends the process.
/// Panics abort (Compiler Architecture §2.1), and this must not unwind
/// through assembly frames.
pub(crate) fn die(message: &str) -> ! {
    eprintln!("crag runtime: {message}");
    std::process::abort()
}
