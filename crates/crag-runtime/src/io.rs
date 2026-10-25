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

//! The runtime functions that wait for time and I/O (Plan §11.7.2).
//!
//! Each tries its operation first, and returns its result at once unless
//! it would block. Then a fiber of a scheduler suspends and waits in the
//! reactor, which wakes it with the result. A fiber a worker resumes by
//! hand has no reactor and blocks its thread instead.
//!
//! The file descriptors are non-blocking, as the library that opens them
//! makes them; on a blocking one an operation blocks its worker. Regular
//! files never block in that sense, so they are read and written at once.

use std::time::{Duration, Instant};

use crate::fiber::TaskContext;
use crate::reactor::{IoOp, IoResult};
use crate::sched::{WaitReason, scheduler_of, suspend, wake};

/// Two words in `rax` and `rdx`.
#[repr(C)]
pub(crate) struct Words(u64, u64);

suspending_fn! {
    /// `rt_sleep(ctx, nanos)`: see `crag_abi::RuntimeFn::Sleep`.
    fn rt_sleep(ctx: *const TaskContext, nanos: u64) => sleep_entry
}

/// The Rust half of `rt_sleep`.
///
/// # Safety
///
/// Called only by `rt_sleep`.
unsafe extern "C" fn sleep_entry(ctx: *const TaskContext, nanos: u64) {
    if nanos == 0 {
        return;
    }
    let duration = Duration::from_nanos(nanos);
    let now = Instant::now();
    // Beyond what the clock counts, a century does as well.
    let deadline = now
        .checked_add(duration)
        .unwrap_or_else(|| now + Duration::from_secs(100 * 365 * 86_400));
    // SAFETY: as the caller promises.
    unsafe {
        let ctx = &*ctx;
        let Some(shared) = scheduler_of(ctx) else {
            std::thread::sleep(duration);
            return;
        };
        let fiber = suspend(ctx, WaitReason::Sleep);
        shared.reactor.sleep_until(deadline, fiber);
    }
}

/// Runs `op` for the fiber of `ctx`, suspending it while it would block.
///
/// # Safety
///
/// Called by the Rust half of a function `suspending_fn!` defined, for
/// the fiber it was called on, with an operation whose buffer lives until
/// the fiber continues.
unsafe fn perform(ctx: *const TaskContext, op: IoOp) -> Words {
    let words = |[a, b]: IoResult| Words(a, b);
    if let Some(result) = op.attempt() {
        return words(result);
    }
    // SAFETY: as the caller promises.
    unsafe {
        let ctx = &*ctx;
        let Some(shared) = scheduler_of(ctx) else {
            return words(op.block());
        };
        let fiber = suspend(ctx, WaitReason::Io);
        if let Err((fiber, errno)) = shared.reactor.wait_io(op, fiber) {
            wake(fiber, [0, errno]);
        }
    }
    // The fiber suspends, and continues with the words of its wake.
    Words(0, 0)
}

suspending_fn! {
    /// `rt_io_read(ctx, fd, buf, len) -> (n, errno)`: see
    /// `crag_abi::RuntimeFn::IoRead`.
    fn rt_io_read(ctx: *const TaskContext, fd: u64, buf: *mut u8, len: u64) -> Words => read_entry
}

/// The Rust half of `rt_io_read`.
///
/// # Safety
///
/// Called only by `rt_io_read`.
unsafe extern "C" fn read_entry(ctx: *const TaskContext, fd: u64, buf: *mut u8, len: u64) -> Words {
    let op = IoOp::Read {
        fd: fd as i32,
        buf,
        len: len as usize,
    };
    // SAFETY: generated code passes a buffer of its fiber.
    unsafe { perform(ctx, op) }
}

suspending_fn! {
    /// `rt_io_write(ctx, fd, buf, len) -> (n, errno)`: see
    /// `crag_abi::RuntimeFn::IoWrite`.
    fn rt_io_write(ctx: *const TaskContext, fd: u64, buf: *const u8, len: u64) -> Words => write_entry
}

/// The Rust half of `rt_io_write`.
///
/// # Safety
///
/// Called only by `rt_io_write`.
unsafe extern "C" fn write_entry(
    ctx: *const TaskContext,
    fd: u64,
    buf: *const u8,
    len: u64,
) -> Words {
    let op = IoOp::Write {
        fd: fd as i32,
        buf,
        len: len as usize,
    };
    // SAFETY: as in `read_entry`.
    unsafe { perform(ctx, op) }
}

suspending_fn! {
    /// `rt_io_accept(ctx, fd) -> (fd, errno)`: see
    /// `crag_abi::RuntimeFn::IoAccept`.
    fn rt_io_accept(ctx: *const TaskContext, fd: u64) -> Words => accept_entry
}

/// The Rust half of `rt_io_accept`.
///
/// # Safety
///
/// Called only by `rt_io_accept`.
unsafe extern "C" fn accept_entry(ctx: *const TaskContext, fd: u64) -> Words {
    // SAFETY: the operation has no buffer.
    unsafe { perform(ctx, IoOp::Accept { fd: fd as i32 }) }
}

suspending_fn! {
    /// `rt_io_connect(ctx, fd, addr, len) -> (0, errno)`: see
    /// `crag_abi::RuntimeFn::IoConnect`.
    fn rt_io_connect(ctx: *const TaskContext, fd: u64, addr: *const u8, len: u64) -> Words => connect_entry
}

/// The Rust half of `rt_io_connect`: starts the connection, then waits
/// until it is made.
///
/// # Safety
///
/// Called only by `rt_io_connect`.
unsafe extern "C" fn connect_entry(
    ctx: *const TaskContext,
    fd: u64,
    addr: *const u8,
    len: u64,
) -> Words {
    let fd = fd as i32;
    // SAFETY: generated code passes a socket address of `len` bytes.
    let started = unsafe { libc::connect(fd, addr.cast(), len as libc::socklen_t) };
    if started == 0 {
        return Words(0, 0);
    }
    let errno = std::io::Error::last_os_error()
        .raw_os_error()
        .unwrap_or(libc::EIO);
    if errno != libc::EINPROGRESS && errno != libc::EINTR {
        return Words(0, errno as u64);
    }
    // SAFETY: the operation has no buffer.
    unsafe { perform(ctx, IoOp::Connect { fd }) }
}
