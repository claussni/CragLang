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
//!
//! Concurrency bugs hide until threads meet at the wrong moment (Plan
//! §11.7.13). Setting `CRAG_JITTER` to a number seeds random delays at
//! every suspension point and wake, so that a test run sees interleavings
//! it would rarely see otherwise.

use std::cell::Cell;
use std::hash::{DefaultHasher, Hash, Hasher};
use std::sync::OnceLock;

use crate::fiber::FiberConfig;

/// The seed of the delays, if `CRAG_JITTER` asks for them.
fn jitter_seed() -> Option<u64> {
    static SEED: OnceLock<Option<u64>> = OnceLock::new();
    *SEED.get_or_init(|| std::env::var("CRAG_JITTER").ok()?.parse().ok())
}

/// Waits a random while, mostly not at all, if `CRAG_JITTER` is set.
pub(crate) fn jitter() {
    let Some(seed) = jitter_seed() else {
        return;
    };
    thread_local! {
        static STATE: Cell<u64> = const { Cell::new(0) };
    }
    let r = STATE.with(|state| {
        let mut x = state.get();
        if x == 0 {
            // Each thread draws its own numbers from the seed.
            let mut hasher = DefaultHasher::new();
            std::thread::current().id().hash(&mut hasher);
            x = (seed ^ hasher.finish()) | 1;
        }
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        state.set(x);
        x
    });
    match r % 16 {
        0..=9 => {}
        10..=14 => {
            for _ in 0..(r >> 8) % 2_000 {
                std::hint::spin_loop();
            }
        }
        _ => std::thread::yield_now(),
    }
}

/// Runs the test with the tortured configuration.
pub fn run_tortured(test: impl FnOnce(FiberConfig)) {
    test(FiberConfig::tortured());
}
