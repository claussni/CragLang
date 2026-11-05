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

//! What the commands do: the dispatch by focus and overlay, the palette,
//! the hints, saving and formatting, and the app and its debugger.

use super::*;

impl Ui {
    /// Carries out a command.
    pub fn command(&mut self, command: Command) {
        if self.overlay.is_some() && self.overlay_command(command) {
            return;
        }
        self.message = None;
        match command {
            Command::Quit => self.ask_quit(),
            Command::QuickSwitch => self.quick_switch(),
            Command::Palette => {
                let items = PaletteCommand::ALL
                    .iter()
                    .map(|&c| PickItem {
                        label: c.label(),
                        detail: c.key().unwrap_or_default().into(),
                        target: Target::Command(c),
                    })
                    .collect();
                self.overlay = Some(Overlay::Pick(Picker::new("Commands", items)));
            }
            Command::CycleFocus => {
                self.focus = match self.focus {
                    Focus::Editor => Focus::Repl,
                    Focus::Repl if self.right_open => Focus::Right,
                    Focus::Repl | Focus::Right if self.left_open => Focus::Buffers,
                    Focus::Buffers => Focus::Files,
                    _ => Focus::Editor,
                }
            }
            Command::FocusLeft => {
                self.left_open = true;
                self.focus = Focus::Buffers;
            }
            Command::FocusEditor => self.focus = Focus::Editor,
            Command::FocusRepl => self.focus = Focus::Repl,
            Command::FocusRight => {
                self.right_open = true;
                self.focus = Focus::Right;
            }
            Command::ToggleLeft => {
                self.left_open = !self.left_open;
                if !self.left_open && matches!(self.focus, Focus::Buffers | Focus::Files) {
                    self.focus = Focus::Editor;
                }
            }
            Command::ToggleRight => {
                self.right_open = !self.right_open;
                if !self.right_open && self.focus == Focus::Right {
                    self.focus = Focus::Editor;
                }
            }
            Command::Escape => {
                if self.focus != Focus::Editor {
                    self.focus = Focus::Editor;
                } else {
                    self.buffer_mut().cursor.anchor = None;
                }
            }
            Command::Reload => {
                self.overlay = Some(Overlay::Confirm {
                    question: "Save every changed buffer and reload the app?".into(),
                    then: PaletteCommand::Reload,
                })
            }
            Command::Breakpoint => self.toggle_breakpoint(),
            Command::Continue => self.go_on(Resume::Continue),
            Command::StepOver => self.go_on(Resume::Over),
            Command::StepInto => self.go_on(Resume::Into),
            Command::StepOut => self.go_on(Resume::Out),
            Command::Pause => {
                self.message = Some("pausing a running task is not supported yet".into())
            }
            Command::Evaluate => self.evaluate_at_cursor(),
            Command::Back => self.back(),
            Command::Forward => self.forward(),
            Command::NextProblem => self.next_problem(),
            _ => match self.focus {
                Focus::Editor => self.edit(command),
                Focus::Repl => self.repl_command(command),
                Focus::Buffers => self.buffers_command(command),
                Focus::Files => self.files_command(command),
                Focus::Right => self.right_command(command),
            },
        }
    }

    fn quick_switch(&mut self) {
        let mut items: Vec<PickItem> = self
            .buffers
            .iter()
            .map(|b| PickItem {
                label: b.name.clone(),
                detail: if b.dirty() {
                    "● open".into()
                } else {
                    "open".into()
                },
                target: Target::File(b.name.clone(), None),
            })
            .collect();
        for file in self.project_files().into_iter().chain(self.std_files()) {
            if !self.buffers.iter().any(|b| b.name == file) {
                items.push(PickItem {
                    label: file.clone(),
                    detail: String::new(),
                    target: Target::File(file, None),
                });
            }
        }
        self.overlay = Some(Overlay::Pick(Picker::new("Open", items)));
    }

    /// Handles a command while an overlay is open; false to let it through.
    fn overlay_command(&mut self, command: Command) -> bool {
        let Some(overlay) = self.overlay.as_mut() else {
            return false;
        };
        match overlay {
            Overlay::Pick(picker) => match command {
                Command::Escape => self.overlay = None,
                Command::Up { .. } => picker.selected = picker.selected.saturating_sub(1),
                Command::Down { .. } => {
                    if picker.selected + 1 < picker.shown.len() {
                        picker.selected += 1;
                    }
                }
                Command::Char(c) => {
                    picker.query.push(c);
                    picker.filter();
                }
                Command::Backspace { .. } => {
                    picker.query.pop();
                    picker.filter();
                }
                Command::Enter => {
                    let target = picker.current().map(|i| i.target.clone());
                    self.overlay = None;
                    match target {
                        Some(Target::File(file, at)) => self.jump_to(&file, at),
                        Some(Target::Command(c)) => self.palette(c),
                        Some(Target::History(text)) => {
                            self.input = Buffer::new("input", &text, None);
                            self.input.cursor = Cursor::at(self.input.len());
                            self.focus = Focus::Repl;
                        }
                        None => {}
                    }
                }
                _ => return true,
            },
            Overlay::Find {
                query,
                replace,
                replacing,
            } => match command {
                Command::Escape => self.overlay = None,
                Command::Indent => {
                    *replacing = !*replacing;
                    if *replacing && replace.is_none() {
                        *replace = Some(String::new());
                    }
                }
                Command::Char(c) => match (*replacing, replace) {
                    (true, Some(r)) => r.push(c),
                    _ => query.push(c),
                },
                Command::Backspace { .. } => {
                    match (*replacing, replace) {
                        (true, Some(r)) => r.pop(),
                        _ => query.pop(),
                    };
                }
                Command::Enter => {
                    let (query, replacement) =
                        (query.clone(), replace.clone().filter(|_| *replacing));
                    self.find_next(&query, replacement.as_deref());
                }
                _ => return false,
            },
            Overlay::Info(_) => {
                self.overlay = None;
                // Esc only closes; any other key also does what it does.
                return command == Command::Escape;
            }
            Overlay::Completion {
                items,
                selected,
                start,
            } => match command {
                Command::Escape => self.overlay = None,
                Command::Up { .. } => *selected = selected.saturating_sub(1),
                Command::Down { .. } => {
                    if *selected + 1 < items.len() {
                        *selected += 1;
                    }
                }
                Command::Enter | Command::Indent => {
                    let (label, start) = (items.get(*selected).map(|c| c.label.clone()), *start);
                    self.overlay = None;
                    if let Some(label) = label {
                        let pos = self.buffer().cursor.pos;
                        self.buffer_mut()
                            .replace(start..pos, &label, EditKind::Other);
                        self.edited();
                    }
                }
                _ => {
                    self.overlay = None;
                    return false;
                }
            },
            Overlay::Confirm { then, .. } => {
                let then = *then;
                self.overlay = None;
                if matches!(command, Command::Char('y' | 'Y')) {
                    self.palette(then);
                }
            }
        }
        true
    }

    /// Carries out a command of the palette.
    pub fn palette(&mut self, command: PaletteCommand) {
        match command {
            PaletteCommand::Save => self.save(),
            PaletteCommand::SaveAll => self.save_all(),
            PaletteCommand::Format => self.format(),
            PaletteCommand::StartApp => {
                self.save_all();
                self.run_repl(":start");
            }
            PaletteCommand::Reload => {
                self.save_all();
                self.run_repl(":reload");
            }
            PaletteCommand::StopApp => self.run_repl(":stop"),
            PaletteCommand::View(view) => {
                self.right_view = view;
                self.right_open = true;
                self.right_selected = 0;
            }
            PaletteCommand::Hints => self.hints = !self.hints,
            PaletteCommand::Key(c) => {
                // Commands of the editor or the REPL act there.
                match c {
                    Command::HistorySearch | Command::ClearRepl => self.focus = Focus::Repl,
                    Command::Undo
                    | Command::Redo
                    | Command::Find
                    | Command::ToggleComment
                    | Command::Complete
                    | Command::Info
                    | Command::Definition
                    | Command::References
                    | Command::Evaluate
                    | Command::Breakpoint => self.focus = Focus::Editor,
                    _ => {}
                }
                self.command(c);
            }
            PaletteCommand::Quit => self.ask_quit(),
            PaletteCommand::QuitNow => self.quit = true,
        }
    }

    /// The keys that matter now, with what they do, for the hint line:
    /// those of what lies over the screen, else of a debugging session,
    /// else of the part that has the focus; then those that always work,
    /// which the line keeps when it has to drop others.
    pub fn hints(&self) -> (Vec<Hint>, Vec<Hint>) {
        let close = ("Esc", "Close");
        let only = |hints: Vec<Hint>| (hints, Vec::new());
        match &self.overlay {
            Some(Overlay::Pick(_)) => {
                return only(vec![("↑↓", "Choose"), ("Enter", "Take"), close]);
            }
            Some(Overlay::Find { .. }) => {
                return only(vec![("Enter", "Next"), ("Tab", "Replace"), close]);
            }
            Some(Overlay::Completion { .. }) => {
                return only(vec![("↑↓", "Choose"), ("Enter", "Insert"), close]);
            }
            Some(Overlay::Confirm { .. }) => return only(vec![("y", "Yes"), ("n", "No")]),
            Some(Overlay::Info(_)) => return only(vec![close]),
            None => {}
        }
        let key = |c| key_name(c).unwrap_or_default();
        let always = vec![
            (key(Command::Palette), "Commands"),
            (key(Command::Quit), "Quit"),
        ];
        let mut hints = if !self.pauses.is_empty() {
            vec![
                (key(Command::Continue), "Continue"),
                (key(Command::StepOver), "Over"),
                (key(Command::StepInto), "Into"),
                (key(Command::StepOut), "Out"),
                (key(Command::Breakpoint), "Breakpoint"),
            ]
        } else {
            match self.focus {
                Focus::Editor => vec![
                    (key(Command::Save), "Save"),
                    (key(Command::QuickSwitch), "Open"),
                    (key(Command::Info), "Info"),
                    (key(Command::Definition), "Definition"),
                    (key(Command::Complete), "Complete"),
                    (key(Command::Evaluate), "Evaluate"),
                    (key(Command::Breakpoint), "Breakpoint"),
                ],
                Focus::Repl => vec![
                    ("Enter", "Run"),
                    (key(Command::LineBreak), "New line"),
                    ("↑↓", "History"),
                    (key(Command::HistorySearch), "Search"),
                    (key(Command::ClearRepl), "Clear"),
                    ("Esc", "Editor"),
                ],
                Focus::Buffers | Focus::Files => {
                    vec![("↑↓", "Choose"), ("Enter", "Open"), ("Esc", "Editor")]
                }
                Focus::Right => vec![
                    ("↑↓", "Choose"),
                    ("Enter", "Go to"),
                    ("←→", "Other view"),
                    ("Esc", "Editor"),
                ],
            }
        };
        hints.push((key(Command::CycleFocus), "Next panel"));
        (hints, always)
    }

    /// Quits, asking first when that would lose unsaved changes.
    fn ask_quit(&mut self) {
        let unsaved = self
            .buffers
            .iter()
            .filter(|b| b.dirty() && !b.readonly)
            .count();
        if unsaved == 0 {
            self.quit = true;
            return;
        }
        let what = match unsaved {
            1 => "1 buffer has unsaved changes".to_string(),
            n => format!("{n} buffers have unsaved changes"),
        };
        self.overlay = Some(Overlay::Confirm {
            question: format!("{what}, which are lost. Quit?"),
            then: PaletteCommand::QuitNow,
        });
    }

    pub fn save(&mut self) {
        let b = self.buffer();
        if b.readonly {
            self.message = Some(format!("{} cannot change", b.name));
            return;
        }
        let Some(path) = b
            .path
            .clone()
            .or_else(|| self.repl.project().root.as_ref().map(|r| r.join(&b.name)))
        else {
            self.message = Some("this buffer has no file".into());
            return;
        };
        let text = b.text();
        match std::fs::write(&path, &text) {
            Ok(()) => {
                let b = self.buffer_mut();
                b.saved();
                b.path = Some(path);
                self.message = Some(format!("saved {}", self.buffer().name));
                self.push();
            }
            Err(e) => self.message = Some(format!("cannot save {}: {e}", path.display())),
        }
    }

    pub fn save_all(&mut self) {
        let current = self.current;
        // A buffer has a file once saved, or if it is one of the project's.
        let own = self.project_files();
        for i in 0..self.buffers.len() {
            let b = &self.buffers[i];
            if b.dirty() && !b.readonly && (b.path.is_some() || own.contains(&b.name)) {
                self.current = i;
                self.save();
            }
        }
        self.current = current;
    }

    fn format(&mut self) {
        let package = self.repl.project().package.clone();
        let package = (!package.is_empty()).then_some(package.as_str());
        let text = self.buffer().text();
        match crag_fmt::format(&text, package) {
            Ok(formatted) if formatted == text => self.message = Some("already formatted".into()),
            Ok(formatted) => {
                self.buffer_mut().set_text(&formatted);
                self.edited();
            }
            Err(crag_fmt::FormatError::Syntax(_)) => {
                self.message =
                    Some("the buffer does not parse; it is formatted once it does".into())
            }
            Err(crag_fmt::FormatError::Changed) => {
                self.message = Some("the formatter would change what this means; left alone".into())
            }
        }
    }

    fn toggle_breakpoint(&mut self) {
        let (file, line) = {
            let b = self.buffer();
            (b.name.clone(), b.line_col(b.cursor.pos).0 as u32 + 1)
        };
        let mut breakpoints = self.repl.breakpoints();
        match breakpoints.iter().position(|b| *b == (file.clone(), line)) {
            Some(i) => {
                breakpoints.remove(i);
            }
            None => breakpoints.push((file.clone(), line)),
        }
        match self.repl.set_breakpoints(&breakpoints) {
            Ok(_) => {
                let set = breakpoints.contains(&(file.clone(), line));
                self.message = Some(match set {
                    true => format!("breakpoint at {file}:{line}"),
                    false => format!("no breakpoint at {file}:{line}"),
                });
            }
            Err(e) => self.message = Some(e),
        }
    }

    /// The stopped task the debugger acts on: the one chosen in the tasks
    /// view, else the first.
    pub(super) fn chosen_task(&self) -> Option<&Pause> {
        self.pauses.get(self.right_selected).or(self.pauses.first())
    }

    fn go_on(&mut self, how: Resume) {
        let Some(task) = self.chosen_task().map(|p| p.task) else {
            self.message = Some("no task is stopped".into());
            return;
        };
        let result = self.repl.scratch().resume(task, how);
        self.pauses.retain(|p| p.task != task);
        if let Err(e) = result {
            self.message = Some(e);
        }
    }

    /// Ctrl+E: evaluates the selection, or the cursor's line, in the
    /// scratch image; the result shows at the end of the line.
    fn evaluate_at_cursor(&mut self) {
        if self.focus == Focus::Repl {
            let text = self.input.text();
            self.submit(&text);
            return;
        }
        self.push();
        let b = self.buffer();
        let (line, _) = b.line_col(b.cursor.pos);
        let text = match b.cursor.selection() {
            Some(range) => b.slice(range),
            None => b.line_text(line).trim().to_string(),
        };
        let text = text.strip_prefix("let ").map_or(text.clone(), |t| {
            t.split_once('=')
                .map_or(t.to_string(), |(_, value)| value.trim().to_string())
        });
        if text.is_empty() {
            return;
        }
        let name = b.name.clone();
        // The expression means what it means in its file: the session gets
        // the file's imports, and the module itself, once.
        let imports: Vec<String> = b
            .text()
            .lines()
            .filter(|l| l.starts_with("import "))
            .map(str::to_string)
            .chain(self.module_path(&name).map(|m| format!("import {m}")))
            .collect();
        for import in imports {
            if self.imported.insert(import.clone()) {
                let _ = self.repl.eval_input(&import);
            }
        }
        let result = match self.repl.eval_input(&text) {
            Ok(output) => {
                let mut shown = output.render().trim_end().to_string();
                if let Some(ty) = self.repl.shown_type() {
                    shown = format!("{shown} : {ty}");
                }
                shown
            }
            Err(errors) => errors.lines().next().unwrap_or("error").to_string(),
        };
        self.inline.retain(|(n, l, _)| !(*n == name && *l == line));
        if !result.is_empty() {
            self.inline.push((name, line, result));
        }
    }
}
