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

//! Stress harness: run fiber tests with the smallest initial stack (Plan §11.3.9).
//!
//! Stack-copying bugs hide until a stack happens to move at the wrong moment.
//! In the tortured configuration every call that reaches a stack check moves
//! the stack to a fresh mapping and verifies the frame-pointer chain, so a
//! stale pointer into the old stack faults at once.
//!
//! Setting the environment variable `CRAG_TORTURE` makes
//! `FiberConfig::default()` tortured, which stresses a whole test run.

use crate::fiber::FiberConfig;

/// Runs the test with the tortured configuration.
pub fn run_tortured(test: impl FnOnce(FiberConfig)) {
    test(FiberConfig::tortured());
}
