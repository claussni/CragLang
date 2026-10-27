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

//! The process's own context for `std.env` (Specification §19.7): the
//! program's arguments, which the tool that runs it sets, the environment's
//! variables and the platform.

use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::sync::Mutex;

use crate::fiber::TaskContext;
use crate::system::worker_of;
use crate::text::{bytes_of, make_text};
use crate::{list, map};

static ARGS: Mutex<Vec<Vec<u8>>> = Mutex::new(Vec::new());

/// Sets the arguments the program sees, without its name.
pub fn set_program_args(args: Vec<Vec<u8>>) {
    *ARGS.lock().unwrap_or_else(|e| e.into_inner()) = args;
}

system_stack_fn! {
    /// `rt_env_args(ctx, list)`: see `crag_abi::RuntimeFn::EnvArgs`.
    fn rt_env_args(ctx: *const TaskContext, list: *mut u8) -> *mut u8 => args_entry
}

system_stack_fn! {
    /// `rt_env_var(ctx, w0, w1, out)`: see `crag_abi::RuntimeFn::EnvVar`.
    fn rt_env_var(ctx: *const TaskContext, w0: u64, w1: u64, out: *mut u64) -> u64 => var_entry
}

system_stack_fn! {
    /// `rt_env_vars(ctx, map)`: see `crag_abi::RuntimeFn::EnvVars`.
    fn rt_env_vars(ctx: *const TaskContext, map: *mut u8) -> *mut u8 => vars_entry
}

system_stack_fn! {
    /// `rt_env_platform(ctx, which)`: see `crag_abi::RuntimeFn::EnvPlatform`.
    fn rt_env_platform(ctx: *const TaskContext, which: u64) -> u64 => platform_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with live collections of the types
/// they name, whose references they take, and a string the caller holds.
unsafe extern "C" fn args_entry(ctx: *const TaskContext, mut list: *mut u8) -> *mut u8 {
    let args = ARGS.lock().unwrap_or_else(|e| e.into_inner()).clone();
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        for arg in args {
            let words = make_text(heap, &[&arg]);
            list = list::push(heap, types, list, &words);
        }
    }
    list
}

/// See `args_entry`.
unsafe extern "C" fn var_entry(ctx: *const TaskContext, w0: u64, w1: u64, out: *mut u64) -> u64 {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let name = std::ffi::OsStr::from_bytes(unsafe { bytes_of(&words) });
    if name.is_empty() || name.as_bytes().contains(&b'=') || name.as_bytes().contains(&0) {
        return 0;
    }
    let Some(value) = std::env::var_os(name) else {
        return 0;
    };
    // SAFETY: as the caller promises, `out` has room for two words.
    unsafe {
        let (heap, _) = worker_of(ctx);
        let [a, b] = make_text(heap, &[&value.into_vec()]);
        out.write(a);
        out.add(1).write(b);
    }
    1
}

/// See `args_entry`.
unsafe extern "C" fn vars_entry(ctx: *const TaskContext, mut map: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        for (name, value) in std::env::vars_os() {
            let (Some(name), Some(value)) = (name.to_str(), value.to_str()) else {
                continue;
            };
            let key = make_text(heap, &[name.as_bytes()]);
            let value = make_text(heap, &[value.as_bytes()]);
            map = map::insert(heap, types, map, &key, &value);
        }
    }
    map
}

/// See `args_entry`.
unsafe extern "C" fn platform_entry(_ctx: *const TaskContext, which: u64) -> u64 {
    match which {
        // Linux, MacOs, Windows, FreeBsd.
        0 => match std::env::consts::OS {
            "macos" => 1,
            "windows" => 2,
            "freebsd" => 3,
            _ => 0,
        },
        // X64, Arm64.
        _ => match std::env::consts::ARCH {
            "aarch64" => 1,
            _ => 0,
        },
    }
}
