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

//! The buffer list, the file tree and the right pane with its views.

use super::*;

impl Ui {
    pub(super) fn buffers_command(&mut self, command: Command) {
        match command {
            Command::Up { .. } => self.buffer_selected = self.buffer_selected.saturating_sub(1),
            Command::Down { .. } => {
                if self.buffer_selected + 1 < self.buffers.len() {
                    self.buffer_selected += 1;
                }
            }
            Command::Enter if self.buffer_selected < self.buffers.len() => {
                self.current = self.buffer_selected;
                self.focus = Focus::Editor;
            }
            _ => {}
        }
    }

    pub(super) fn files_command(&mut self, command: Command) {
        let tree = self.file_tree();
        match command {
            Command::Up { .. } => self.file_selected = self.file_selected.saturating_sub(1),
            Command::Down { .. } => {
                if self.file_selected + 1 < tree.len() {
                    self.file_selected += 1;
                }
            }
            Command::Enter | Command::Right { .. } | Command::Left { .. } => {
                let Some(item) = tree.get(self.file_selected) else {
                    return;
                };
                if let Some(dir) = &item.dir {
                    let open = !matches!(command, Command::Left { .. })
                        && (matches!(command, Command::Right { .. }) || !item.open);
                    if open {
                        self.expanded.insert(dir.clone());
                    } else {
                        self.expanded.remove(dir);
                    }
                } else if let (Some(file), Command::Enter) = (&item.file, command) {
                    let file = file.clone();
                    self.jump_to(&file, None);
                }
            }
            _ => {}
        }
    }

    pub(super) fn right_command(&mut self, command: Command) {
        let len = match self.right_view {
            RightView::Problems => self.problems.len(),
            RightView::Tasks => self.pauses.len(),
            _ => 0,
        };
        match command {
            Command::Left { .. } | Command::Right { .. } => {
                let i = RightView::ALL
                    .iter()
                    .position(|v| *v == self.right_view)
                    .unwrap_or(0);
                let next = match command {
                    Command::Left { .. } => (i + RightView::ALL.len() - 1) % RightView::ALL.len(),
                    _ => (i + 1) % RightView::ALL.len(),
                };
                self.right_view = RightView::ALL[next];
                self.right_selected = 0;
            }
            Command::Up { .. } => self.right_selected = self.right_selected.saturating_sub(1),
            Command::Down { .. } => {
                if self.right_selected + 1 < len {
                    self.right_selected += 1;
                }
            }
            Command::Enter => match self.right_view {
                RightView::Problems => {
                    if let Some(p) = self.problems.get(self.right_selected).cloned() {
                        self.jump_to(&p.file, Some(p.start));
                    }
                }
                RightView::Tasks => {
                    if let Some(p) = self.pauses.get(self.right_selected).cloned() {
                        let at = self.line_offset(&p.file, p.line);
                        self.jump_to(&p.file, at);
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }

    /// The locals of the stopped task the tasks view has chosen.
    pub fn chosen_locals(&mut self) -> Vec<(String, String)> {
        let Some(task) = self.chosen_task().map(|p| p.task) else {
            return Vec::new();
        };
        self.repl.scratch().locals(task).unwrap_or_default()
    }

    /// Whether a buffer differs from the code the app runs.
    pub fn differs_from_app(&self, buffer: &Buffer) -> bool {
        self.repl
            .app_text(&buffer.name)
            .is_some_and(|text| text != buffer.text())
    }

    /// Whether a line, from one, of a file has a breakpoint.
    pub fn has_breakpoint(&self, file: &str, line: u32) -> bool {
        self.repl
            .breakpoints()
            .iter()
            .any(|(f, l)| f == file && *l == line)
    }
}
