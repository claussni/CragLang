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

//! Tier-up in the images (Implementation Plan §11.10.2): the functions
//! whose baseline code counted many calls and back-edges are compiled
//! again in the optimizing tier and swapped in through their slots.
//!
//! A run in the scratch image is asked for hot functions while it waits,
//! so a long REPL input speeds up as it runs. The app image is asked
//! between other requests, at the UI's and the debug adapter's clock,
//! as long as the code is what the app runs: after an edit that is not
//! reloaded yet, optimized code would bring the edit in without a reload.
//!
//! Optimized code has no steps. A breakpoint in an optimized function, or
//! in one inlined into it, sends the function back to its baseline code
//! (Specification §20.3); the image sees to that when the breakpoints are
//! set, and leaves such functions out of tier-up.

use std::collections::HashMap;

use crag_abi::FuncId;
use crag_backend::{code, func_id};
use crag_mir::{InstanceKey, Tier};
use crag_session::{ImageKind, Optimized, ShippedFunction, TierUp};

use crate::exec::{compile, hot};
use crate::main_instance;
use crate::project::Project;
use crate::scratch::{Scratch, Shipped, shipped_functions};

/// Whether code shipped to images tiers up: compiled in the baseline tier,
/// with a count that makes a function hot.
pub(crate) fn tiers_up() -> bool {
    Tier::compiled() == Tier::Baseline && hot() > 0
}

/// Compiles hot functions of an image in the optimizing tier.
pub(crate) struct Hot<'s, 'a> {
    pub project: &'a Project,
    /// The instances the image runs, by their functions.
    pub instances: &'s HashMap<FuncId, InstanceKey<'a>>,
    /// What the host knows of the image's code.
    pub shipped: &'s mut Shipped,
}

impl TierUp for Hot<'_, '_> {
    fn threshold(&self) -> u64 {
        hot()
    }

    /// Optimized code for the hot functions not tried before. A function
    /// whose optimized code does not compile, or calls what the image has
    /// not loaded, stays baseline, and is not tried again until new code
    /// of it is shipped.
    fn hot(&mut self, funcs: &[FuncId]) -> Option<Optimized> {
        let (db, program) = (&self.project.db, self.project.program);
        let mut types = Vec::new();
        let mut functions = Vec::new();
        for &func in funcs {
            // A function of another run is the business of that run.
            let Some(&instance) = self.instances.get(&func) else {
                continue;
            };
            if !self.shipped.tried.insert(func) {
                continue;
            }
            let Some(Ok(optimized)) = code(db, program, instance, Tier::Hot) else {
                continue;
            };
            if optimized
                .calls
                .iter()
                .any(|&c| !self.instances.contains_key(&func_id(c)))
            {
                continue;
            }
            for t in &optimized.types {
                if !types.contains(t) {
                    types.push(t.clone());
                }
            }
            functions.push(ShippedFunction {
                id: optimized.func,
                signature: optimized.slot.signature,
                params: optimized.params,
                returns: optimized.returns,
                object: optimized.object.clone(),
            });
        }
        (!functions.is_empty()).then_some((types, functions))
    }

    fn optimized(&mut self, funcs: &[FuncId]) {
        self.shipped.optimized += funcs.len();
    }
}

impl Scratch {
    /// Swaps the app's hot functions for optimized code: how many it
    /// swapped. Nothing is swapped while the code differs from what the
    /// app runs; a reload or a restart brings them together again.
    pub fn tier_up_app(&mut self, project: &Project) -> Result<usize, String> {
        let swapped = self.swap_hot_app(project);
        if let Err(why) = &swapped
            && self.session.app().is_none()
        {
            self.app_ended = Some(why.clone());
        }
        swapped
    }

    fn swap_hot_app(&mut self, project: &Project) -> Result<usize, String> {
        if !tiers_up() || self.session.app().is_none() || self.app.stale {
            return Ok(0);
        }
        let threshold = hot();
        let funcs = self
            .session
            .profile(ImageKind::App, threshold)
            .map_err(|e| e.to_string())?;
        if funcs.iter().all(|f| self.app.tried.contains(f)) {
            return Ok(0);
        }
        let main = main_instance(project)?;
        let compiled = compile(project, &[main])?;
        if !self
            .session
            .changed(ImageKind::App, &shipped_functions(&compiled))
            .is_empty()
        {
            self.app.stale = true;
            return Ok(0);
        }
        let mut hot = Hot {
            project,
            instances: &compiled.instances,
            shipped: &mut self.app,
        };
        let Some(optimized) = hot.hot(&funcs) else {
            return Ok(0);
        };
        let swapped = self
            .session
            .optimize(ImageKind::App, optimized)
            .map_err(|e| e.to_string())?;
        self.app.optimized += swapped.len();
        Ok(swapped.len())
    }

    /// How many functions of the scratch image and of the app were swapped
    /// for optimized code.
    pub fn optimized(&self) -> (usize, usize) {
        (self.scratch.optimized, self.app.optimized)
    }
}
