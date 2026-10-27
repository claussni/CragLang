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

//! The app image and reloads (Implementation Plan §11.8.4, §11.8.5,
//! Specification §20.2).
//!
//! The app runs the project's `main` in an image of its own, apart from
//! the scratch image, and keeps running while the code changes. A reload
//! compiles what `main` reaches from the code as it is now and ships what
//! changed; the image swaps it in under the running app. Frames already
//! running finish on their old code, and every later call through a slot
//! reaches the new code, so a server loop written as a tail call picks it
//! up at its next round.
//!
//! A reload is a transaction: code with errors is rejected before
//! anything is sent, and an image that cannot load the code keeps what it
//! had. Calls between old and new code are safe by construction: a slot's
//! signature spells out the layouts of the types passing through it, so a
//! function whose types changed gets a new slot, which only new code
//! calls, while running code keeps calling the old function.

use crag_backend::func_id;
use crag_session::{AppStatus, ImageKind, RunResult, descriptor_hash};

use crate::diagnostics::{check, render_diagnostic};
use crate::exec::compile;
use crate::main_instance;
use crate::project::Project;
use crate::scratch::{Scratch, Shipment, Shipped};

/// The most diagnostics a rejected reload lists.
const SHOWN_DIAGNOSTICS: usize = 5;

/// The project's errors, as a rejected start or reload reports them.
fn errors(project: &Project) -> Option<String> {
    let diagnostics = check(project);
    if diagnostics.is_empty() {
        return None;
    }
    let mut out = String::new();
    for d in diagnostics.iter().take(SHOWN_DIAGNOSTICS) {
        let file = &project.file(d.module).shown;
        out += &render_diagnostic(d, file, project.source(d.module));
    }
    if diagnostics.len() > SHOWN_DIAGNOSTICS {
        out += &format!("and {} more\n", diagnostics.len() - SHOWN_DIAGNOSTICS);
    }
    Some(out)
}

impl Scratch {
    /// Starts the app: an app image, with what `main` reaches, running
    /// `main`. An app that runs already is stopped first.
    pub fn start_app(&mut self, project: &Project) -> Result<Shipment, String> {
        if let Some(errors) = errors(project) {
            return Err(format!(
                "the app cannot start, the code has errors:\n{errors}"
            ));
        }
        let main = main_instance(project)?;
        self.stop_app()?;
        self.session
            .start_app_image()
            .map_err(|e| format!("cannot start the app image: {e}"))?;
        self.app = Shipped::default();
        let compiled = compile(project, &[main])?;
        let shipment = self.ship_to(ImageKind::App, project, &compiled, &[main], true)?;
        if !self.breakpoints.is_empty() {
            let breakpoints = self.breakpoints.clone();
            self.set_breakpoints(project, &breakpoints)?;
        }
        self.session
            .start_app(func_id(main))
            .map_err(|e| e.to_string())?;
        Ok(shipment)
    }

    /// Reloads the app with the code as it is now: what changed is swapped
    /// in while the app runs. A rejected reload changes nothing.
    pub fn reload(&mut self, project: &Project) -> Result<Shipment, String> {
        if self.session.app().is_none() {
            return Err("no app runs; start it first".into());
        }
        if let Some(errors) = errors(project) {
            return Err(format!(
                "the reload is rejected, the code has errors; the app runs on unchanged:\n{errors}"
            ));
        }
        let main = main_instance(project)?;
        let compiled = compile(project, &[main])?;
        // Boxes of the old code may still be alive and are freed by their
        // type's descriptor, so a type keeps its descriptor while the app
        // runs: one whose counted fields moved needs a restart.
        if let Some(known) = self.session.descriptors(ImageKind::App) {
            let changed = compiled.types.iter().any(|(index, descriptor)| {
                known
                    .get(index)
                    .is_some_and(|hash| *hash != descriptor_hash(descriptor))
            });
            if changed {
                return Err(
                    "the reload is rejected; the app runs on unchanged: a type moved \
                    the fields that hold references, and its values of the old layout \
                    may still be alive; restart the app to use it"
                        .into(),
                );
            }
        }
        // Values the compiler computed are not filled in: code that reads
        // their cells runs. They are computed again when next read.
        let shipment = self
            .ship_to(ImageKind::App, project, &compiled, &[main], false)
            .map_err(|e| format!("the reload is rejected; the app runs on unchanged: {e}"))?;
        // The breakpoints move with the lines of the new code.
        if !self.breakpoints.is_empty() {
            let breakpoints = self.breakpoints.clone();
            self.set_breakpoints(project, &breakpoints)?;
        }
        Ok(shipment)
    }

    /// How the app is doing, in words: `None` while it runs.
    pub fn app_status(&mut self, project: &Project) -> Result<Option<String>, String> {
        if self.session.app().is_none() {
            return Ok(Some("no app runs".into()));
        }
        Ok(
            match self.session.app_status().map_err(|e| e.to_string())? {
                AppStatus::Running => None,
                AppStatus::Stopped => Some("the app was stopped".into()),
                AppStatus::Ended(RunResult::Trapped(trap)) => Some(format!(
                    "the app trapped:\n{}",
                    crate::exec::report(project, &self.app.functions, &trap)
                )),
                AppStatus::Ended(_) => Some("the app finished".into()),
            },
        )
    }

    /// Stops the app and ends its image.
    pub fn stop_app(&mut self) -> Result<(), String> {
        self.session.stop_app().map_err(|e| e.to_string())
    }
}
