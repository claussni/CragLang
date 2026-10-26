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

//! The atomics of the lock-free parts that the loom models check (Plan
//! §11.7.13): the standard ones, or loom's when built with `--cfg loom`,
//! which runs a model under every interleaving that matters.
//!
//! Only `cargo test --lib loom` runs with `--cfg loom`, since loom's
//! atomics work only inside a model.

#[cfg(not(loom))]
pub(crate) use std::sync::atomic::{AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize, fence};
#[cfg(not(loom))]
pub(crate) use std::sync::{Arc, Mutex};

#[cfg(loom)]
pub(crate) use loom::sync::atomic::{AtomicIsize, AtomicPtr, AtomicU64, AtomicUsize, fence};
#[cfg(loom)]
pub(crate) use loom::sync::{Arc, Mutex};

/// Runs `f` as a loom model. Without a bound loom tries every preemption,
/// which does not finish for these models, so the bound is 3 unless
/// `LOOM_MAX_PREEMPTIONS` sets another.
#[cfg(all(test, loom))]
pub(crate) fn model<F: Fn() + Sync + Send + 'static>(f: F) {
    let mut builder = loom::model::Builder::new();
    builder.preemption_bound.get_or_insert(3);
    builder.check(f);
}
