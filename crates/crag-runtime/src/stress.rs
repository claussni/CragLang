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
