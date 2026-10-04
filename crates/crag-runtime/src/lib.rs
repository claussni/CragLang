//! The Crag runtime.
//!
//! M0 scope (Implementation Plan §11.3.1 to §11.3.4 and §11.3.9): fibers and
//! the context switch, stack growth by copying, the side stack, the sentinel
//! stop request and the stress harness.
//!
//! Runtime discipline (Compiler Architecture §2.1): no thread-locals, no
//! callbacks into Crag code from the runtime stack, panics abort.

pub mod fiber;
pub mod sentinel;
pub mod side_stack;
pub mod stack;
pub mod stress;
