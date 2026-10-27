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

//! The debugger's host side (Implementation Plan §11.8.6, Specification
//! §20.3): breakpoints by file and line, the app's stopped tasks, stepping
//! and their locals.
//!
//! Every statement of baseline code has a step, and the host knows where
//! each starts and which locals hold values there. A breakpoint is the
//! first step of each function on its line; the image sets those steps'
//! flags, and a task that reaches one stops. Breakpoints are kept by file
//! and line, so a reload, which moves the steps, places them again.

use crag_session::PausedTask;

use crate::diagnostics::line_col;
use crate::project::Project;
use crate::scratch::Scratch;

/// How a stopped task goes on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resume {
    /// To the next breakpoint.
    Continue,
    /// To the next statement anywhere.
    Into,
    /// To the next statement of this function or the one that called it.
    Over,
    /// To the next statement of the function that called this one.
    Out,
}

/// A stopped task as the user sees it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pause {
    pub task: u64,
    /// The function and where it stopped: file and line, from one.
    pub function: String,
    pub file: String,
    pub line: u32,
    /// The functions that called it, innermost first.
    pub callers: Vec<String>,
}

impl Scratch {
    /// Sets the app's breakpoints, by file and line from one, in place of
    /// those before: for each, how many functions have a statement there.
    pub fn set_breakpoints(
        &mut self,
        project: &Project,
        breakpoints: &[(String, u32)],
    ) -> Result<Vec<usize>, String> {
        self.breakpoints = breakpoints.to_vec();
        let mut steps = Vec::new();
        let mut placed = vec![0; breakpoints.len()];
        for (&func, f) in &self.app.functions {
            let file = &project.file(f.module).shown;
            let source = project.source(f.module);
            for (k, (want_file, want_line)) in breakpoints.iter().enumerate() {
                if file != want_file {
                    continue;
                }
                let first = f.steps.iter().position(|step| {
                    step.position
                        .is_some_and(|p| line_col(source, p).0 as u32 == *want_line)
                });
                if let Some(step) = first {
                    steps.push((func, step as u32));
                    placed[k] += 1;
                }
            }
        }
        if self.session.app().is_some() {
            self.session.set_breaks(steps).map_err(|e| e.to_string())?;
        }
        Ok(placed)
    }

    /// The breakpoints, by file and line.
    pub fn breakpoints(&self) -> &[(String, u32)] {
        &self.breakpoints
    }

    /// The app's stopped tasks.
    pub fn pauses(&mut self, project: &Project) -> Result<Vec<Pause>, String> {
        if self.session.app().is_none() {
            return Ok(Vec::new());
        }
        let tasks = self.session.pauses().map_err(|e| e.to_string())?;
        Ok(tasks.iter().map(|t| self.pause(project, t)).collect())
    }

    fn pause(&self, project: &Project, task: &PausedTask) -> Pause {
        let name = |func| {
            self.app
                .functions
                .get(&func)
                .map_or_else(|| format!("function {}", func.0), |f| f.name.clone())
        };
        let (file, line) = match self.app.functions.get(&task.func) {
            Some(f) => {
                let position = f.steps.get(task.step as usize).and_then(|s| s.position);
                let line = position.map_or(0, |p| line_col(project.source(f.module), p).0 as u32);
                (project.file(f.module).shown.clone(), line)
            }
            None => (String::new(), 0),
        };
        Pause {
            task: task.task,
            function: name(task.func),
            file,
            line,
            callers: task.callers.iter().map(|&f| name(f)).collect(),
        }
    }

    /// Resumes a stopped task.
    pub fn resume(&mut self, task: u64, how: Resume) -> Result<(), String> {
        let how = match how {
            Resume::Continue => 0,
            Resume::Into => 1,
            Resume::Over => 2,
            Resume::Out => 3,
        };
        self.session.resume(task, how).map_err(|e| e.to_string())
    }

    /// The locals of a stopped task where it stopped: names and values.
    pub fn locals(&mut self, task: u64) -> Result<Vec<(String, String)>, String> {
        let tasks = self.session.pauses().map_err(|e| e.to_string())?;
        let paused = tasks
            .iter()
            .find(|t| t.task == task)
            .ok_or_else(|| format!("task {task:x} is not stopped"))?;
        let Some(step) = self
            .app
            .functions
            .get(&paused.func)
            .and_then(|f| f.steps.get(paused.step as usize))
        else {
            return Ok(Vec::new());
        };
        let locals = step.locals.clone();
        let texts = self
            .session
            .locals(
                task,
                locals
                    .iter()
                    .map(|l| ((*l.shapes).clone(), l.root))
                    .collect(),
            )
            .map_err(|e| e.to_string())?;
        Ok(locals.into_iter().map(|l| l.name).zip(texts).collect())
    }
}
