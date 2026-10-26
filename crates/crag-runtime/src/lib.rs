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
//! metered tier's budgets (§11.6.6), and strings and bytes (§11.6.9). M4
//! adds the scheduler (§11.7.1), the poller and timers (§11.7.2), scopes
//! (§11.7.3), cancellation (§11.7.4), streams and hubs (§11.7.5), refs
//! (§11.7.6), transactions (§11.7.7), commutative updates (§11.7.8),
//! `ext` locks (§11.7.9), the signals of blocks (§11.7.10), lazy cells
//! (§11.7.11) and deferred teardown (§11.7.12).
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

#[cfg(not(all(target_arch = "x86_64", target_os = "linux")))]
compile_error!("the runtime is written for x86-64 Linux only: its context switch and epoll");

#[macro_use]
mod system;

mod cancel;
pub mod codec;
mod deque;
mod epoch;
mod ext;
pub mod fiber;
pub mod heap;
mod io;
mod lazy;
pub mod list;
pub mod map;
pub mod meter;
pub mod poll;
pub mod print;
pub mod rc;
mod reactor;
mod refs;
pub mod sched;
mod scope;
pub mod sentinel;
pub mod side_stack;
mod signals;
pub mod stack;
mod stm;
mod stream;
pub mod stress;
pub mod teardown;
#[cfg(test)]
mod testing;
pub mod text;
pub mod timer;
pub mod unwind;

pub use cancel::CancelHandle;
pub use codec::{DecodeError, NotSolid, decode_value, encode_value};
pub use fiber::{Fiber, FiberConfig, FiberState, TaskContext, Worker};
pub use heap::{Heap, alloc_box};
pub use meter::Meter;
pub use print::{PrintLimits, print_value, release_value};
pub use rc::{Disposal, Types, next_disposal, release_box};
pub use sched::{FiberRef, Scheduler, SchedulerConfig, WaitReason, WorkerStats, wake};
pub use sentinel::{StopHandle, StopReason, request_stop};
pub use timer::{TimerId, TimerWheel};
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
        RuntimeFn::TextConcat => text::rt_text_concat as *const () as usize,
        RuntimeFn::TextEquals => text::rt_text_equals as *const () as usize,
        RuntimeFn::TextShow => text::rt_text_show as *const () as usize,
        RuntimeFn::Disposal => rc::rt_disposal as *const () as usize,
        RuntimeFn::Yield => sched::rt_yield as *const () as usize,
        RuntimeFn::Sleep => io::rt_sleep as *const () as usize,
        RuntimeFn::IoRead => io::rt_io_read as *const () as usize,
        RuntimeFn::IoWrite => io::rt_io_write as *const () as usize,
        RuntimeFn::IoAccept => io::rt_io_accept as *const () as usize,
        RuntimeFn::IoConnect => io::rt_io_connect as *const () as usize,
        RuntimeFn::ScopeNew => scope::rt_scope_new as *const () as usize,
        RuntimeFn::ScopeStart => scope::rt_scope_start as *const () as usize,
        RuntimeFn::ScopeNext => scope::rt_scope_next as *const () as usize,
        RuntimeFn::ScopeResult => scope::rt_scope_result as *const () as usize,
        RuntimeFn::ScopeCancel => scope::rt_scope_cancel as *const () as usize,
        RuntimeFn::ScopeEnd => scope::rt_scope_end as *const () as usize,
        RuntimeFn::EnterNoCancel => cancel::rt_enter_no_cancel as *const () as usize,
        RuntimeFn::ExitNoCancel => cancel::rt_exit_no_cancel as *const () as usize,
        RuntimeFn::StreamNew => stream::rt_stream_new as *const () as usize,
        RuntimeFn::StreamPut => stream::rt_stream_put as *const () as usize,
        RuntimeFn::StreamTryPut => stream::rt_stream_try_put as *const () as usize,
        RuntimeFn::StreamNext => stream::rt_stream_next as *const () as usize,
        RuntimeFn::StreamClose => stream::rt_stream_close as *const () as usize,
        RuntimeFn::StreamDispose => stream::rt_stream_dispose as *const () as usize,
        RuntimeFn::HubNew => stream::rt_hub_new as *const () as usize,
        RuntimeFn::HubSink => stream::rt_hub_sink as *const () as usize,
        RuntimeFn::HubSource => stream::rt_hub_source as *const () as usize,
        RuntimeFn::HubSeal => stream::rt_hub_seal as *const () as usize,
        RuntimeFn::HubRelease => stream::rt_hub_release as *const () as usize,
        RuntimeFn::HubDrop => stream::rt_hub_drop as *const () as usize,
        RuntimeFn::RefRead => refs::rt_ref_read as *const () as usize,
        RuntimeFn::RefCommit => refs::rt_ref_commit as *const () as usize,
        RuntimeFn::RefDone => refs::rt_ref_done as *const () as usize,
        RuntimeFn::RefSwap => refs::rt_ref_swap as *const () as usize,
        RuntimeFn::TxBegin => stm::rt_tx_begin as *const () as usize,
        RuntimeFn::TxRead => stm::rt_tx_read as *const () as usize,
        RuntimeFn::TxWrite => stm::rt_tx_write as *const () as usize,
        RuntimeFn::TxCommit => stm::rt_tx_commit as *const () as usize,
        RuntimeFn::TxAbort => stm::rt_tx_abort as *const () as usize,
        RuntimeFn::TxRetry => stm::rt_tx_retry as *const () as usize,
        RuntimeFn::RefApply => refs::rt_ref_apply as *const () as usize,
        RuntimeFn::ExtNew => ext::rt_ext_new as *const () as usize,
        RuntimeFn::ExtLock => ext::rt_ext_lock as *const () as usize,
        RuntimeFn::ExtUnlock => ext::rt_ext_unlock as *const () as usize,
        RuntimeFn::ExtFree => ext::rt_ext_free as *const () as usize,
        RuntimeFn::SignalEmit => signals::rt_signal_emit as *const () as usize,
        RuntimeFn::SignalNext => signals::rt_signal_next as *const () as usize,
        RuntimeFn::LazyNew => lazy::rt_lazy_new as *const () as usize,
        RuntimeFn::LazyGet => lazy::rt_lazy_get as *const () as usize,
        RuntimeFn::LazySet => lazy::rt_lazy_set as *const () as usize,
        RuntimeFn::LazyFree => lazy::rt_lazy_free as *const () as usize,
        RuntimeFn::ReleaseDeferred => teardown::rt_release_deferred as *const () as usize,
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
