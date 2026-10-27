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

//! The failed assertions of the test that runs (Specification §19.12):
//! `std.test` records each one, and the test runner takes them when the
//! test ends. Tests run one after another, so one list serves them.

use std::sync::Mutex;

use crate::fiber::TaskContext;
use crate::text::bytes_of;

static FAILURES: Mutex<Vec<(String, u64)>> = Mutex::new(Vec::new());

/// The failures recorded since the last call, each its message and the
/// byte offset of its assertion in its module, in the order they came.
pub fn take_test_failures() -> Vec<(String, u64)> {
    std::mem::take(&mut *FAILURES.lock().unwrap_or_else(|e| e.into_inner()))
}

system_stack_fn! {
    /// `rt_test_record(ctx, w0, w1, position)`: see
    /// `crag_abi::RuntimeFn::TestRecord`.
    fn rt_test_record(ctx: *const TaskContext, w0: u64, w1: u64, position: u64) => record_entry
}

/// The Rust half of `rt_test_record`.
///
/// # Safety
///
/// Called only by `rt_test_record`, with a string the caller holds.
unsafe extern "C" fn record_entry(_ctx: *const TaskContext, w0: u64, w1: u64, position: u64) {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let message = String::from_utf8_lossy(unsafe { bytes_of(&words) }).into_owned();
    FAILURES
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .push((message, position));
}
