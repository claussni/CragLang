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

//! Standard output and files for `std.io` (Specification §15.6): printing
//! a string, and reading a whole file into a bytes value.
//!
//! Both block their worker for the time the system takes, which for a
//! terminal, a pipe being read or a local disk is short; a file is not a
//! descriptor the poller can wait on.

use std::io::Write;
use std::sync::Mutex;

use crag_abi::TEXT_LEN_MAX;

use crate::fiber::TaskContext;
use crate::system::worker_of;
use crate::text::{bytes_of, make_text};

/// Held for each print, so prints from tasks on other workers do not
/// interleave within a line.
static STDOUT: Mutex<()> = Mutex::new(());

system_stack_fn! {
    /// `rt_io_print(ctx, w0, w1, newline) -> errno`: see
    /// `crag_abi::RuntimeFn::IoPrint`.
    fn rt_io_print(ctx: *const TaskContext, w0: u64, w1: u64, newline: u64) -> u64 => print_entry
}

/// The Rust half of `rt_io_print`.
///
/// # Safety
///
/// Called only by `rt_io_print`, with a string the caller holds.
unsafe extern "C" fn print_entry(_ctx: *const TaskContext, w0: u64, w1: u64, newline: u64) -> u64 {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let text = unsafe { bytes_of(&words) };
    let line;
    let out = match newline {
        1 => {
            line = [text, b"\n"].concat();
            &line[..]
        }
        _ => text,
    };
    let _held = STDOUT.lock().unwrap_or_else(|e| e.into_inner());
    // Standard output is not buffered here, so what is printed is out
    // before the task goes on.
    let mut stdout = std::fs::File::from(
        // SAFETY: descriptor 1 is borrowed for the write and not closed,
        // since the file is forgotten after it.
        unsafe { <std::os::fd::OwnedFd as std::os::fd::FromRawFd>::from_raw_fd(1) },
    );
    let written = stdout.write_all(out);
    std::mem::forget(stdout);
    match written {
        Ok(()) => 0,
        Err(e) => e.raw_os_error().unwrap_or(libc::EIO) as u64,
    }
}

system_stack_fn! {
    /// `rt_io_read_file(ctx, w0, w1, out) -> errno`: see
    /// `crag_abi::RuntimeFn::IoReadFile`.
    fn rt_io_read_file(ctx: *const TaskContext, w0: u64, w1: u64, out: *mut u64) -> u64
        => read_file_entry
}

/// The Rust half of `rt_io_read_file`.
///
/// # Safety
///
/// Called only by `rt_io_read_file`, with a string the caller holds and
/// two words at `out`.
unsafe extern "C" fn read_file_entry(
    ctx: *const TaskContext,
    w0: u64,
    w1: u64,
    out: *mut u64,
) -> u64 {
    use std::os::unix::ffi::OsStrExt;
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let path = unsafe { bytes_of(&words) };
    if path.contains(&0) {
        return libc::EINVAL as u64;
    }
    let path = std::path::Path::new(std::ffi::OsStr::from_bytes(path));
    let bytes = match std::fs::metadata(path) {
        Ok(m) if m.len() >= TEXT_LEN_MAX => return libc::EFBIG as u64,
        Ok(m) if m.is_dir() => return libc::EISDIR as u64,
        Ok(_) => match std::fs::read(path) {
            Ok(bytes) => bytes,
            Err(e) => return e.raw_os_error().unwrap_or(libc::EIO) as u64,
        },
        Err(e) => return e.raw_os_error().unwrap_or(libc::EIO) as u64,
    };
    if bytes.len() as u64 >= TEXT_LEN_MAX {
        return libc::EFBIG as u64;
    }
    // SAFETY: as the caller promises.
    let (heap, _) = unsafe { worker_of(ctx) };
    let [a, b] = make_text(heap, &[&bytes]);
    // SAFETY: as the caller promises, `out` has room for two words.
    unsafe {
        out.write(a);
        out.add(1).write(b);
    }
    0
}
