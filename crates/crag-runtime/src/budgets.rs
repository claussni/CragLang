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

//! The process's budgets (Specification §18.7, Implementation Plan
//! §11.10.9): those it enforces as a receiver and those it sends under,
//! read from its budget directory once, at startup ([`init`]), and what
//! each has taken (`crag_budget::Registry`).
//!
//! The directory is `crag run --budgets <dir>`, or `CRAG_BUDGETS`. A
//! process that starts without one has no budgets: it ignores stamps, and
//! sends code unstamped. `std.transport` reads and manages the budgets
//! through `rt_budget_op`.

use std::path::Path;
use std::sync::OnceLock;

use crag_abi::budget_op::*;
use crag_budget::registry::Side;
use crag_budget::{Limits, Origin, Registry};

use crate::fiber::TaskContext;
use crate::system::worker_of;
use crate::text::make_text;

static REGISTRY: OnceLock<Registry> = OnceLock::new();

/// Reads the budget directory `dir`, or `CRAG_BUDGETS` without one, as
/// the process's budgets. The first call decides; later ones change
/// nothing.
pub fn init(dir: Option<&Path>) -> Result<(), String> {
    if REGISTRY.get().is_some() {
        return Ok(());
    }
    let registry = load(dir)?;
    let _ = REGISTRY.set(registry);
    Ok(())
}

fn load(dir: Option<&Path>) -> Result<Registry, String> {
    let from_env = std::env::var_os("CRAG_BUDGETS").filter(|v| !v.is_empty());
    match dir.map(Path::to_path_buf).or(from_env.map(Into::into)) {
        Some(dir) => Registry::load(&dir),
        None => Ok(Registry::default()),
    }
}

/// The process's budgets, read from `CRAG_BUDGETS` if no `init` came
/// first.
pub fn registry() -> &'static Registry {
    REGISTRY
        .get_or_init(|| load(None).unwrap_or_else(|why| crate::die(&format!("the budgets: {why}"))))
}

system_stack_fn! {
    /// `rt_budget_op(ctx, scratch, op, side, index)`: see
    /// `crag_abi::RuntimeFn::BudgetOp`.
    fn rt_budget_op(ctx: *const TaskContext, scratch: *mut u64, op: u64, side: u64, index: u64) -> u64
        => op_entry
}

/// The Rust half of `rt_budget_op`.
///
/// # Safety
///
/// Called only by `rt_budget_op`, with two scratch words.
unsafe extern "C" fn op_entry(
    ctx: *const TaskContext,
    scratch: *mut u64,
    op: u64,
    side: u64,
    index: u64,
) -> u64 {
    const NONE: u64 = u64::MAX;
    let registry = registry();
    let side = match side {
        0 => Side::Receiving,
        _ => Side::Sending,
    };
    let index = index as usize;
    // SAFETY: as the caller promises.
    let give = |text: &str| unsafe {
        let (heap, _) = worker_of(&*ctx);
        let [w0, w1] = make_text(heap, &[text.as_bytes()]);
        scratch.write(w0);
        scratch.add(1).write(w1);
        0
    };
    let limit = |n: Option<u64>| n.unwrap_or(NONE);
    let described = || registry.describe(side, index);
    let text = |f: fn(&Origin) -> &str| match described() {
        Some((origin, _)) => give(f(&origin)),
        None => NONE,
    };
    let limits = |f: fn(&Limits) -> Option<u64>| match described() {
        Some((_, limits)) => limit(f(&limits)),
        None => NONE,
    };
    match op {
        COUNT => registry.count(side) as u64,
        DOCUMENT => text(|o| &o.document),
        DATE => text(|o| &o.date),
        ISSUER => text(|o| &o.issuer),
        NAME => text(|o| &o.name),
        LIMIT_STEPS => limits(|l| l.steps),
        LIMIT_MEMORY => limits(|l| l.memory),
        LIMIT_RUNS => limits(|l| l.runs),
        USED_STEPS => registry.usage(side, index).map_or(NONE, |u| limit(u.steps)),
        USED_MEMORY => registry
            .usage(side, index)
            .map_or(NONE, |u| limit(u.memory)),
        USED_RUNS => registry.usage(side, index).map_or(NONE, |u| u.runs),
        RENEW => match registry.renew(side, index) {
            Ok(()) => 0,
            Err(why) => {
                give(&why);
                1
            }
        },
        RESET => u64::from(!registry.reset(side, index)),
        _ => NONE,
    }
}
