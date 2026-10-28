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

//! What the UI holds and what its commands do (Specification §20.8). The
//! state knows nothing of the terminal: the event loop feeds it commands
//! and ticks, and `view` draws it.

use std::collections::HashSet;
use std::path::PathBuf;
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::debug::{Pause, Resume};
use crate::diagnostics::{check, line_col};
use crate::lsp::analysis;
use crate::repl::{EvalOutput, Repl, is_complete};

use super::buffer::{Buffer, Cursor, EditKind};
use super::highlight::Highlights;
use super::keys::{Command, key_name};

/// How long typing pauses before buffers reach the compiler (§11.8.2).
pub const PUSH_PAUSE: Duration = Duration::from_millis(300);

/// Which part of the screen keys go to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Focus {
    Editor,
    Repl,
    Buffers,
    Files,
    Right,
}

impl Focus {
    pub fn name(self) -> &'static str {
        match self {
            Focus::Editor => "Editor",
            Focus::Repl => "REPL",
            Focus::Buffers => "Buffers",
            Focus::Files => "Files",
            Focus::Right => "Panel",
        }
    }
}

/// The right panel's views, one at a time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RightView {
    Watches,
    Tasks,
    Tests,
    Problems,
}

impl RightView {
    pub const ALL: [RightView; 4] = [
        RightView::Watches,
        RightView::Tasks,
        RightView::Tests,
        RightView::Problems,
    ];

    pub fn name(self) -> &'static str {
        match self {
            RightView::Watches => "Watches",
            RightView::Tasks => "Tasks",
            RightView::Tests => "Tests",
            RightView::Problems => "Problems",
        }
    }
}

/// An error at a place of a file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Problem {
    pub file: String,
    /// Line and column, from one.
    pub line: usize,
    pub column: usize,
    pub message: String,
    /// Byte offsets in the file's text.
    pub start: u32,
    pub end: u32,
}

/// A line of the REPL's output.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OutLine {
    pub text: String,
    pub kind: OutKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OutKind {
    Input,
    Value,
    /// A value's type, shown dimmed after it.
    Type,
    Error,
    Info,
    /// What a program printed.
    Printed,
}

/// Where a pick leads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Target {
    /// A file as the project shows it, at a byte offset.
    File(String, Option<u32>),
    Command(PaletteCommand),
    History(String),
}

/// What the command palette offers.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PaletteCommand {
    Save,
    SaveAll,
    Format,
    StartApp,
    Reload,
    StopApp,
    View(RightView),
    /// Shows or hides the hint line.
    Hints,
    /// What a key does, for those who look for it here.
    Key(Command),
    Quit,
    /// Quits although buffers have unsaved changes; asked for first.
    QuitNow,
}

impl PaletteCommand {
    const ALL: [PaletteCommand; 35] = {
        use Command as C;
        use PaletteCommand as P;
        [
            P::Key(C::QuickSwitch),
            P::Save,
            P::SaveAll,
            P::Format,
            P::Key(C::Find),
            P::Key(C::Undo),
            P::Key(C::Redo),
            P::Key(C::ToggleComment),
            P::Key(C::Complete),
            P::Key(C::Info),
            P::Key(C::Definition),
            P::Key(C::References),
            P::Key(C::Back),
            P::Key(C::Forward),
            P::Key(C::NextProblem),
            P::Key(C::Evaluate),
            P::StartApp,
            P::Reload,
            P::StopApp,
            P::Key(C::Breakpoint),
            P::Key(C::Continue),
            P::Key(C::StepOver),
            P::Key(C::StepInto),
            P::Key(C::StepOut),
            P::Key(C::HistorySearch),
            P::Key(C::ClearRepl),
            P::Key(C::CycleFocus),
            P::Key(C::ToggleLeft),
            P::Key(C::ToggleRight),
            P::View(RightView::Problems),
            P::View(RightView::Tasks),
            P::View(RightView::Watches),
            P::View(RightView::Tests),
            P::Hints,
            P::Quit,
        ]
    };

    /// The key that does the same, if one does.
    pub fn key(self) -> Option<&'static str> {
        match self {
            PaletteCommand::Save => key_name(Command::Save),
            PaletteCommand::Reload => key_name(Command::Reload),
            PaletteCommand::Quit => key_name(Command::Quit),
            PaletteCommand::Key(c) => key_name(c),
            _ => None,
        }
    }

    fn label(self) -> String {
        use Command as C;
        match self {
            PaletteCommand::Save => "Save the buffer".into(),
            PaletteCommand::SaveAll => "Save every buffer".into(),
            PaletteCommand::Format => "Format the buffer".into(),
            PaletteCommand::StartApp => "Start the app".into(),
            PaletteCommand::Reload => "Reload the app".into(),
            PaletteCommand::StopApp => "Stop the app".into(),
            PaletteCommand::View(view) => format!("Show {}", view.name()),
            PaletteCommand::Hints => "Show or hide the key hints".into(),
            PaletteCommand::Key(c) => match c {
                C::QuickSwitch => "Open a file",
                C::Find => "Find and replace",
                C::Undo => "Undo",
                C::Redo => "Redo",
                C::ToggleComment => "Comment or uncomment the lines",
                C::Complete => "Complete the name",
                C::Info => "Tell about the name",
                C::Definition => "Go to the definition",
                C::References => "Find the references",
                C::Back => "Go back",
                C::Forward => "Go forward",
                C::NextProblem => "Go to the next problem",
                C::Evaluate => "Evaluate the line",
                C::Breakpoint => "Set or clear a breakpoint",
                C::Continue => "Continue the paused tasks",
                C::StepOver => "Step over",
                C::StepInto => "Step into",
                C::StepOut => "Step out",
                C::HistorySearch => "Search the REPL's history",
                C::ClearRepl => "Clear the REPL",
                C::CycleFocus => "Move to the next panel",
                C::ToggleLeft => "Show or hide the left panels",
                C::ToggleRight => "Show or hide the right panel",
                _ => "",
            }
            .into(),
            PaletteCommand::Quit | PaletteCommand::QuitNow => "Quit".into(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PickItem {
    pub label: String,
    pub detail: String,
    pub target: Target,
}

/// A modal list with fuzzy search, as in Helix.
#[derive(Clone, Debug)]
pub struct Picker {
    pub title: String,
    pub query: String,
    pub items: Vec<PickItem>,
    /// Indices of the items that match, best first.
    pub shown: Vec<usize>,
    pub selected: usize,
}

/// How well `query` matches `text`, if it does: its characters in order,
/// scoring runs and an early start.
pub fn fuzzy(query: &str, text: &str) -> Option<i64> {
    if query.is_empty() {
        return Some(0);
    }
    let text: Vec<char> = text.to_lowercase().chars().collect();
    let mut score = 0i64;
    let mut at = 0;
    let mut last: Option<usize> = None;
    for q in query.to_lowercase().chars() {
        let found = (at..text.len()).find(|&i| text[i] == q)?;
        score += match last {
            Some(l) if found == l + 1 => 10,
            _ => 1,
        };
        if found == 0 {
            score += 5;
        }
        last = Some(found);
        at = found + 1;
    }
    Some(score - text.len() as i64 / 8)
}

impl Picker {
    pub fn new(title: &str, items: Vec<PickItem>) -> Picker {
        let mut picker = Picker {
            title: title.into(),
            query: String::new(),
            items,
            shown: Vec::new(),
            selected: 0,
        };
        picker.filter();
        picker
    }

    fn filter(&mut self) {
        let mut scored: Vec<(i64, usize)> = self
            .items
            .iter()
            .enumerate()
            .filter_map(|(i, item)| fuzzy(&self.query, &item.label).map(|s| (s, i)))
            .collect();
        // Stable on equal scores, so the order given ranks: buffers first.
        scored.sort_by_key(|&(s, i)| (-s, i));
        self.shown = scored.into_iter().map(|(_, i)| i).collect();
        self.selected = 0;
    }

    pub fn current(&self) -> Option<&PickItem> {
        self.shown.get(self.selected).map(|&i| &self.items[i])
    }
}

/// What lies over the screen.
#[derive(Clone, Debug)]
pub enum Overlay {
    Pick(Picker),
    Find {
        query: String,
        replace: Option<String>,
        /// Whether keys go to the replacement.
        replacing: bool,
    },
    Info(String),
    Completion {
        items: Vec<analysis::Completion>,
        selected: usize,
        /// Where the word being completed starts.
        start: usize,
    },
    Confirm {
        question: String,
        then: PaletteCommand,
    },
}

/// A place jumped from, for Alt+, and Alt+.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Place {
    file: String,
    pos: usize,
}

/// A key and what it does, for the hint line.
pub type Hint = (&'static str, &'static str);

/// The mode the status bar shows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Edit,
    Run,
    Debug(usize),
}

pub struct Ui {
    pub repl: Repl,
    pub buffers: Vec<Buffer>,
    pub current: usize,
    pub focus: Focus,
    pub left_open: bool,
    pub right_open: bool,
    pub right_view: RightView,
    /// Directories of the file tree that are open.
    pub expanded: HashSet<String>,
    pub file_selected: usize,
    pub buffer_selected: usize,
    pub right_selected: usize,
    pub input: Buffer,
    pub output: Vec<OutLine>,
    /// The end of what programs printed after its last newline.
    printed: String,
    pub history: Vec<String>,
    history_at: Option<usize>,
    pub overlay: Option<Overlay>,
    pub message: Option<String>,
    clipboard: String,
    jumps: Vec<Place>,
    jump_at: usize,
    pub problems: Vec<Problem>,
    /// When edited buffers go to the compiler, and the versions they had.
    push_at: Option<Instant>,
    pushed: Vec<(String, u64)>,
    /// Results of Ctrl+E, by buffer and line, shown dimmed at its end.
    pub inline: Vec<(String, usize, String)>,
    pub pauses: Vec<Pause>,
    /// Where the last error in the REPL's output points.
    repl_error: Option<(String, usize)>,
    /// What Ctrl+E imported into the session.
    imported: HashSet<String>,
    pub quit: bool,
    /// The current buffer's highlighting, by its place, name and version.
    highlight: Option<(usize, String, u64, Rc<Highlights>)>,
    /// Whether the hint line shows the keys that matter now.
    pub hints: bool,
    /// The lines the editor shows, for paging.
    pub page: usize,
}

/// An entry of the file tree.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FileItem {
    pub label: String,
    pub depth: usize,
    /// The file as the project shows it, or none for a directory.
    pub file: Option<String>,
    /// The directory's key, for expanding it.
    pub dir: Option<String>,
    pub open: bool,
}

fn is_word(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

impl Ui {
    pub fn new(repl: Repl) -> Ui {
        let mut ui = Ui {
            repl,
            buffers: Vec::new(),
            current: 0,
            focus: Focus::Editor,
            left_open: true,
            right_open: true,
            right_view: RightView::Problems,
            expanded: HashSet::new(),
            file_selected: 0,
            buffer_selected: 0,
            right_selected: 0,
            input: Buffer::new("input", "", None),
            output: Vec::new(),
            printed: String::new(),
            history: Vec::new(),
            history_at: None,
            overlay: None,
            message: None,
            clipboard: String::new(),
            jumps: Vec::new(),
            jump_at: 0,
            problems: Vec::new(),
            push_at: None,
            pushed: Vec::new(),
            inline: Vec::new(),
            pauses: Vec::new(),
            repl_error: None,
            imported: HashSet::new(),
            quit: false,
            hints: true,
            highlight: None,
            page: 20,
        };
        ui.show_project();
        ui
    }

    /// Shows the REPL's project afresh, with its main module open.
    fn show_project(&mut self) {
        self.buffers.clear();
        self.current = 0;
        self.expanded = HashSet::from([String::new()]);
        self.file_selected = 0;
        self.buffer_selected = 0;
        self.right_selected = 0;
        self.jumps.clear();
        self.jump_at = 0;
        self.problems.clear();
        self.push_at = None;
        self.pushed.clear();
        self.inline.clear();
        self.pauses.clear();
        self.repl_error = None;
        self.imported.clear();
        self.highlight = None;
        // The main module first, as the project names it.
        let main = self.main_file();
        match main.or_else(|| self.project_files().into_iter().next()) {
            Some(file) => self.open(&file, None),
            None => self.buffers.push(Buffer::new("scratch", "", None)),
        }
        self.check();
    }

    fn main_file(&self) -> Option<String> {
        let project = self.repl.project();
        let main = project.main.as_deref()?;
        let module = project.module(main)?;
        Some(project.file(module).shown.clone())
    }

    /// The project's own files, as it shows them.
    pub fn project_files(&self) -> Vec<String> {
        self.repl
            .project()
            .texts()
            .into_iter()
            .map(|(shown, _)| shown)
            .collect()
    }

    /// The bundled modules of `std`, as the project shows them.
    fn std_files(&self) -> Vec<String> {
        let project = self.repl.project();
        let own = project.own().len();
        project.files[..project.files.len() - own]
            .iter()
            .map(|f| f.shown.clone())
            .collect()
    }

    pub fn buffer(&self) -> &Buffer {
        &self.buffers[self.current]
    }

    pub fn buffer_mut(&mut self) -> &mut Buffer {
        &mut self.buffers[self.current]
    }

    pub fn mode(&self) -> Mode {
        if !self.pauses.is_empty() {
            Mode::Debug(self.pauses.len())
        } else if self.repl.app_runs() {
            Mode::Run
        } else {
            Mode::Edit
        }
    }

    /// The file tree: directories by module path, then `std`.
    pub fn file_tree(&self) -> Vec<FileItem> {
        let mut out = Vec::new();
        let name = self.repl.project().package.clone();
        let root_label = if name.is_empty() {
            "files".to_string()
        } else {
            name
        };
        out.push(FileItem {
            label: root_label,
            depth: 0,
            file: None,
            dir: Some(String::new()),
            open: self.expanded.contains(""),
        });
        if self.expanded.contains("") {
            let mut files = self.project_files();
            files.sort();
            let mut dirs_shown: HashSet<String> = HashSet::new();
            for file in files {
                let parts: Vec<&str> = file.split('/').collect();
                let mut visible = true;
                for d in 0..parts.len() - 1 {
                    let key = parts[..=d].join("/");
                    if !visible {
                        break;
                    }
                    if dirs_shown.insert(key.clone()) {
                        out.push(FileItem {
                            label: parts[d].to_string(),
                            depth: d + 1,
                            file: None,
                            dir: Some(key.clone()),
                            open: self.expanded.contains(&key),
                        });
                    }
                    visible = self.expanded.contains(&key);
                }
                if visible {
                    out.push(FileItem {
                        label: parts[parts.len() - 1].to_string(),
                        depth: parts.len(),
                        file: Some(file.clone()),
                        dir: None,
                        open: false,
                    });
                }
            }
        }
        let open = self.expanded.contains("std");
        out.push(FileItem {
            label: "dependencies".into(),
            depth: 0,
            file: None,
            dir: Some("std".into()),
            open,
        });
        if open {
            for file in self.std_files() {
                out.push(FileItem {
                    label: file.trim_end_matches(" (bundled)").to_string(),
                    depth: 1,
                    file: Some(file),
                    dir: None,
                    open: false,
                });
            }
        }
        out
    }

    /// Opens a file as the project shows it, or switches to its buffer, and
    /// puts the cursor at a byte offset.
    pub fn open(&mut self, file: &str, at: Option<u32>) {
        if let Some(i) = self.buffers.iter().position(|b| b.name == file) {
            self.current = i;
        } else {
            let project = self.repl.project();
            let Some((module, dependency)) = project
                .files
                .iter()
                .find(|f| f.shown == file)
                .map(|f| (f.module, f.dependency.is_some()))
            else {
                self.message = Some(format!("{file} is no file of the project"));
                return;
            };
            let text = project.source(module).to_string();
            // A dependency's module is a published package's, never edited.
            let path = project
                .root
                .as_ref()
                .filter(|_| !dependency)
                .map(|r| r.join(file))
                .filter(|p| p.is_file());
            let readonly = dependency || (path.is_none() && file.ends_with("(bundled)"));
            let mut buffer = Buffer::new(file, &text, path);
            buffer.readonly = readonly;
            self.pushed.push((file.to_string(), 0));
            self.buffers.push(buffer);
            self.current = self.buffers.len() - 1;
        }
        if let Some(at) = at {
            let b = self.buffer_mut();
            let pos = b.char_of(at);
            b.cursor = Cursor::at(pos);
            let (line, _) = b.line_col(pos);
            b.scroll = line.saturating_sub(5);
        }
        self.focus = Focus::Editor;
    }

    /// Remembers where the cursor is before a jump.
    fn record_jump(&mut self) {
        let place = Place {
            file: self.buffer().name.clone(),
            pos: self.buffer().cursor.pos,
        };
        self.jumps.truncate(self.jump_at);
        self.jumps.push(place);
        self.jump_at = self.jumps.len();
    }

    fn jump_to(&mut self, file: &str, at: Option<u32>) {
        self.record_jump();
        self.open(file, at);
    }

    /// Gives the compiler the buffers that changed since it last had them
    /// and checks the project again.
    pub fn push(&mut self) {
        self.push_at = None;
        let mut changed = false;
        for b in &self.buffers {
            if b.readonly {
                continue;
            }
            let known = self.pushed.iter_mut().find(|(n, _)| *n == b.name);
            match known {
                Some((_, version)) if *version == b.version => continue,
                Some((_, version)) => *version = b.version,
                None => self.pushed.push((b.name.clone(), b.version)),
            }
            let project = self.repl.project_mut();
            let module = project
                .files
                .iter()
                .find(|f| f.shown == b.name)
                .map(|f| f.module);
            if let Some(module) = module
                && project.source(module) != b.text()
            {
                project.set_source(module, b.text());
                changed = true;
            }
        }
        if changed {
            self.check();
        }
    }

    /// The project's errors, as problems.
    pub fn check(&mut self) {
        let project = self.repl.project();
        self.problems = check(project)
            .into_iter()
            .filter_map(|d| {
                let file = project.file(d.module).shown.clone();
                // The REPL's own module shows its errors in the REPL.
                if file == "repl" {
                    return None;
                }
                let (line, column) = line_col(project.source(d.module), d.range.start);
                Some(Problem {
                    file,
                    line,
                    column,
                    message: d.message,
                    start: d.range.start,
                    end: d.range.end,
                })
            })
            .collect();
    }

    /// What the clock does: buffers reach the compiler after a pause in
    /// typing, and the app's stopped tasks show.
    pub fn tick(&mut self, now: Instant) {
        if self.push_at.is_some_and(|at| now >= at) {
            self.push();
        }
        self.show_printed(false);
        if self.repl.app_runs() {
            let pauses = self.repl.pauses().unwrap_or_default();
            let new = pauses
                .iter()
                .find(|p| !self.pauses.iter().any(|q| q.task == p.task))
                .cloned();
            self.pauses = pauses;
            if let Some(pause) = new {
                // A breakpoint hit: the task tree, and the paused line.
                self.right_view = RightView::Tasks;
                self.right_open = true;
                self.right_selected = self
                    .pauses
                    .iter()
                    .position(|p| p.task == pause.task)
                    .unwrap_or(0);
                let at = self.line_offset(&pause.file, pause.line);
                self.jump_to(&pause.file, at);
                self.message = Some(format!(
                    "stopped in {} at {}:{}",
                    pause.function, pause.file, pause.line
                ));
            }
        } else {
            self.pauses.clear();
        }
    }

    /// The byte offset where a line, from one, of a file starts.
    fn line_offset(&self, file: &str, line: u32) -> Option<u32> {
        let project = self.repl.project();
        let module = project.files.iter().find(|f| f.shown == file)?.module;
        let text = project.source(module);
        let start: usize = text
            .split_inclusive('\n')
            .take(line.saturating_sub(1) as usize)
            .map(str::len)
            .sum();
        Some(start as u32)
    }

    fn edited(&mut self) {
        self.push_at = Some(Instant::now() + PUSH_PAUSE);
        let (name, line) = {
            let b = self.buffer();
            (b.name.clone(), b.line_col(b.cursor.pos).0)
        };
        self.inline.retain(|(n, l, _)| !(*n == name && *l == line));
    }

    /// The highlighting of the current buffer, lexed again only when it
    /// changed.
    pub fn highlights(&mut self) -> Rc<Highlights> {
        let b = &self.buffers[self.current];
        match &self.highlight {
            Some((at, name, version, h))
                if *at == self.current && *name == b.name && *version == b.version =>
            {
                h.clone()
            }
            _ => {
                let h = Rc::new(Highlights::of(&b.text()));
                self.highlight = Some((self.current, b.name.clone(), b.version, h.clone()));
                h
            }
        }
    }

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
    fn chosen_task(&self) -> Option<&Pause> {
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

    fn back(&mut self) {
        if self.jump_at == 0 {
            return;
        }
        if self.jump_at == self.jumps.len() {
            let here = Place {
                file: self.buffer().name.clone(),
                pos: self.buffer().cursor.pos,
            };
            self.jumps.push(here);
        }
        self.jump_at -= 1;
        let place = self.jumps[self.jump_at].clone();
        self.goto_place(&place);
    }

    fn forward(&mut self) {
        if self.jump_at + 1 >= self.jumps.len() {
            return;
        }
        self.jump_at += 1;
        let place = self.jumps[self.jump_at].clone();
        self.goto_place(&place);
    }

    fn goto_place(&mut self, place: &Place) {
        self.open(&place.file, None);
        let b = self.buffer_mut();
        b.cursor = Cursor::at(place.pos.min(b.len()));
        let (line, _) = b.line_col(b.cursor.pos);
        if line < b.scroll {
            b.scroll = line;
        }
    }

    /// F8: the next problem after the cursor, in this file or the next;
    /// in the REPL, the place of its last error.
    fn next_problem(&mut self) {
        if self.focus == Focus::Repl
            && let Some((file, line)) = self.repl_error.clone()
        {
            let at = self.line_offset(&file, line as u32);
            self.jump_to(&file, at);
            return;
        }
        self.push();
        if self.problems.is_empty() {
            self.message = Some("no problems".into());
            return;
        }
        let name = self.buffer().name.clone();
        let here = self.buffer().byte_of(self.buffer().cursor.pos);
        let next = self
            .problems
            .iter()
            .find(|p| p.file == name && p.start > here)
            .or_else(|| self.problems.iter().find(|p| p.file > name))
            .or_else(|| self.problems.first())
            .cloned()
            .expect("there are problems");
        self.jump_to(&next.file, Some(next.start));
        self.message = Some(next.message);
    }

    // The editor.

    fn edit(&mut self, command: Command) {
        let readonly = self.buffer().readonly;
        let changes = matches!(
            command,
            Command::Char(_)
                | Command::Enter
                | Command::LineBreak
                | Command::Backspace { .. }
                | Command::Delete { .. }
                | Command::Indent
                | Command::Dedent
                | Command::Cut
                | Command::Paste
                | Command::Undo
                | Command::Redo
                | Command::ToggleComment
        );
        if readonly && changes {
            self.message = Some(format!("{} cannot change", self.buffer().name));
            return;
        }
        let page = self.page;
        match command {
            Command::Save => return self.save(),
            Command::Find => {
                self.overlay = Some(Overlay::Find {
                    query: self
                        .buffer()
                        .cursor
                        .selection()
                        .map_or_else(String::new, |r| self.buffer().slice(r)),
                    replace: None,
                    replacing: false,
                });
                return;
            }
            Command::Complete => return self.complete(),
            Command::Info => return self.info(),
            Command::Definition => return self.definition(),
            Command::References => return self.references(),
            Command::CopyOrInterrupt => {
                if let Some(range) = self.buffer().cursor.selection() {
                    self.clipboard = self.buffer().slice(range);
                }
                return;
            }
            _ => {}
        }
        let b = &mut self.buffers[self.current];
        move_or_edit(b, command, page, &mut self.clipboard);
        if changes {
            self.edited();
        }
    }

    fn complete(&mut self) {
        self.push();
        let b = self.buffer();
        let pos = b.cursor.pos;
        let mut start = pos;
        while start > 0 && is_word(b.rope().char(start - 1)) {
            start -= 1;
        }
        let prefix = b.slice(start..pos);
        let Some(module) = self.module_of(&b.name) else {
            return;
        };
        let offset = b.byte_of(pos);
        let project = self.repl.project();
        let items: Vec<analysis::Completion> =
            analysis::completion(&project.db, project.program, module, offset)
                .into_iter()
                .filter(|c| c.label.starts_with(&prefix))
                .collect();
        if items.is_empty() {
            self.message = Some("no completions".into());
            return;
        }
        self.overlay = Some(Overlay::Completion {
            items,
            selected: 0,
            start,
        });
    }

    /// The module path of a file of the project, as imports name it.
    fn module_path(&self, file: &str) -> Option<String> {
        let module = self.module_of(file)?;
        let project = self.repl.project();
        project
            .own()
            .iter()
            .any(|f| f.module == module)
            .then(|| module.path(&project.db).clone())
    }

    fn module_of(&self, file: &str) -> Option<crag_hir::ModuleId> {
        let project = self.repl.project();
        project
            .files
            .iter()
            .find(|f| f.shown == file)
            .map(|f| f.module)
    }

    fn info(&mut self) {
        self.push();
        let b = self.buffer();
        let Some(module) = self.module_of(&b.name) else {
            return;
        };
        let offset = b.byte_of(b.cursor.pos);
        let project = self.repl.project();
        match analysis::hover(&project.db, project.program, module, offset) {
            Some((text, _)) => {
                let text: String = text
                    .lines()
                    .filter(|l| !l.starts_with("```"))
                    .collect::<Vec<_>>()
                    .join("\n");
                self.overlay = Some(Overlay::Info(text));
            }
            None => self.message = Some("nothing to tell here".into()),
        }
    }

    fn definition(&mut self) {
        self.push();
        let b = self.buffer();
        let Some(module) = self.module_of(&b.name) else {
            return;
        };
        let offset = b.byte_of(b.cursor.pos);
        let project = self.repl.project();
        let (db, program) = (&project.db, project.program);
        let place = analysis::target_at(db, program, module, offset)
            .and_then(|(t, _)| analysis::definition(db, program, t));
        match place {
            Some(place) => {
                let file = project.file(place.module).shown.clone();
                self.jump_to(&file, Some(place.range.start));
            }
            None => self.message = Some("no definition here".into()),
        }
    }

    fn references(&mut self) {
        self.push();
        let b = self.buffer();
        let Some(module) = self.module_of(&b.name) else {
            return;
        };
        let offset = b.byte_of(b.cursor.pos);
        let project = self.repl.project();
        let (db, program) = (&project.db, project.program);
        let files = analysis::Files {
            entries: project
                .files
                .iter()
                .map(|f| analysis::FileEntry {
                    module: f.module,
                    uri: f.shown.clone(),
                    editable: true,
                })
                .collect(),
            package: None,
        };
        let Some((target, _)) = analysis::target_at(db, program, module, offset) else {
            self.message = Some("no name here".into());
            return;
        };
        let items: Vec<PickItem> = analysis::references(db, program, &files, target, true)
            .into_iter()
            .map(|p| {
                let file = project.file(p.module).shown.clone();
                let source = project.source(p.module);
                let (line, column) = line_col(source, p.range.start);
                let text = source
                    .lines()
                    .nth(line - 1)
                    .unwrap_or("")
                    .trim()
                    .to_string();
                PickItem {
                    label: format!("{file}:{line}:{column}"),
                    detail: text,
                    target: Target::File(file, Some(p.range.start)),
                }
            })
            .collect();
        self.overlay = Some(Overlay::Pick(Picker::new("References", items)));
    }

    fn find_next(&mut self, query: &str, replacement: Option<&str>) {
        if query.is_empty() {
            return;
        }
        let b = &mut self.buffers[self.current];
        if let (Some(replacement), Some(range)) = (replacement, b.cursor.selection())
            && b.slice(range.clone()) == query
        {
            b.replace(range, replacement, EditKind::Other);
        }
        let text = b.text();
        let from = b.rope().char_to_byte(b.cursor.pos);
        let found = text[from..]
            .find(query)
            .map(|i| i + from)
            .or_else(|| text.find(query));
        match found {
            Some(byte) => {
                let start = b.rope().byte_to_char(byte);
                let end = start + query.chars().count();
                b.cursor = Cursor {
                    pos: end,
                    anchor: Some(start),
                };
                let (line, _) = b.line_col(start);
                if line < b.scroll || line >= b.scroll + self.page {
                    b.scroll = line.saturating_sub(self.page / 2);
                }
            }
            None => self.message = Some(format!("`{query}` is not in the buffer")),
        }
        if replacement.is_some() {
            self.edited();
        }
    }

    // The REPL.

    fn repl_command(&mut self, command: Command) {
        match command {
            Command::Enter => {
                let text = self.input.text();
                if text.trim_start().starts_with(':') || is_complete(&text) {
                    self.submit(&text);
                } else {
                    self.input.insert("\n", EditKind::Typing);
                }
            }
            Command::LineBreak => self.input.insert("\n", EditKind::Typing),
            Command::ClearRepl => self.output.clear(),
            Command::HistorySearch => {
                let items = self
                    .history
                    .iter()
                    .rev()
                    .map(|h| PickItem {
                        label: h.replace('\n', " "),
                        detail: String::new(),
                        target: Target::History(h.clone()),
                    })
                    .collect();
                self.overlay = Some(Overlay::Pick(Picker::new("History", items)));
            }
            Command::Up { .. } if !self.input.text().contains('\n') => self.history_step(true),
            Command::Down { .. } if !self.input.text().contains('\n') => self.history_step(false),
            Command::CopyOrInterrupt => {
                if let Some(range) = self.input.cursor.selection() {
                    self.clipboard = self.input.slice(range);
                }
            }
            command => {
                let page = self.page;
                move_or_edit(&mut self.input, command, page, &mut self.clipboard);
            }
        }
    }

    fn history_step(&mut self, back: bool) {
        if self.history.is_empty() {
            return;
        }
        let at = match (self.history_at, back) {
            (None, true) => self.history.len() - 1,
            (None, false) => return,
            (Some(0), true) => 0,
            (Some(i), true) => i - 1,
            (Some(i), false) if i + 1 < self.history.len() => i + 1,
            (Some(_), false) => {
                self.history_at = None;
                self.input = Buffer::new("input", "", None);
                return;
            }
        };
        self.history_at = Some(at);
        let text = self.history[at].clone();
        self.input = Buffer::new("input", &text, None);
        self.input.cursor = Cursor::at(self.input.len());
    }

    /// The REPL's prompt: the image it runs in, and a stopped frame.
    pub fn prompt(&self) -> String {
        match self.chosen_task() {
            Some(p) => format!("scratch [{} {}:{}]> ", p.function, p.file, p.line),
            None => "scratch> ".into(),
        }
    }

    /// Runs the REPL's input.
    fn submit(&mut self, text: &str) {
        let text = text.trim_end().to_string();
        self.input = Buffer::new("input", "", None);
        self.history_at = None;
        if text.trim().is_empty() {
            return;
        }
        if self.history.last() != Some(&text) {
            self.history.push(text.clone());
        }
        // `:reload` saves the changed buffers first (§20.2); `:edit` opens.
        if let Some(rest) = text.trim().strip_prefix(":edit") {
            let file = rest.trim().to_string();
            self.echo(&text);
            self.open(&file, None);
            return;
        }
        if matches!(text.trim(), ":reload" | ":start") {
            self.save_all();
        }
        self.echo(&text);
        self.run_repl_quietly(&text);
    }

    fn echo(&mut self, text: &str) {
        let prompt = self.prompt();
        for (i, line) in text.lines().enumerate() {
            let lead = if i == 0 {
                prompt.clone()
            } else {
                " ".repeat(prompt.len())
            };
            self.output.push(OutLine {
                text: format!("{lead}{line}"),
                kind: OutKind::Input,
            });
        }
    }

    /// Lines of the REPL's output, all of one kind.
    fn say(&mut self, text: &str, kind: OutKind) {
        for line in text.lines() {
            self.output.push(OutLine {
                text: line.to_string(),
                kind,
            });
        }
    }

    /// Runs REPL input as if typed, showing it.
    pub fn run_repl(&mut self, text: &str) {
        self.echo(text);
        self.run_repl_quietly(text);
    }

    /// Shows what programs printed as lines of the REPL's output; a line
    /// not ended yet waits for its end, unless `all`.
    fn show_printed(&mut self, all: bool) {
        self.printed += &self.repl.take_printed();
        let end = match all {
            true => self.printed.len(),
            false => self.printed.rfind('\n').map_or(0, |i| i + 1),
        };
        let done: String = self.printed.drain(..end).collect();
        for line in done.lines() {
            self.output.push(OutLine {
                text: line.to_string(),
                kind: OutKind::Printed,
            });
        }
    }

    fn run_repl_quietly(&mut self, text: &str) {
        // `:cd` saves the buffers of the project it leaves.
        if let Some(rest) = text.trim().strip_prefix(":cd")
            && rest.starts_with(char::is_whitespace)
        {
            self.save_all();
            match self.repl.change_dir(rest.trim()) {
                Ok(output) => {
                    self.show_project();
                    self.say(&output.render(), OutKind::Info);
                }
                Err(errors) => self.say(&errors, OutKind::Error),
            }
            return;
        }
        self.push();
        let result = self.repl.eval_input(text);
        self.show_printed(true);
        let (shown, kind) = match result {
            Ok(EvalOutput::Quit) => {
                self.quit = true;
                return;
            }
            Ok(output @ EvalOutput::Value(_)) => (output.render(), OutKind::Value),
            Ok(output) => (output.render(), OutKind::Info),
            Err(errors) => (errors, OutKind::Error),
        };
        if kind == OutKind::Error {
            self.repl_error = shown.lines().find_map(|l| {
                let rest = l.trim().strip_prefix("--> ")?;
                let mut parts = rest.rsplitn(3, ':');
                let _column = parts.next()?;
                let line: usize = parts.next()?.parse().ok()?;
                Some((parts.next()?.to_string(), line))
            });
        }
        let lines: Vec<&str> = shown.lines().collect();
        // Long output is folded.
        const FOLD: usize = 40;
        for line in lines.iter().take(FOLD) {
            self.output.push(OutLine {
                text: line.to_string(),
                kind,
            });
        }
        if lines.len() > FOLD {
            self.output.push(OutLine {
                text: format!("… {} more lines", lines.len() - FOLD),
                kind: OutKind::Info,
            });
        }
        // The type goes dimmed after the value's last line.
        if kind == OutKind::Value
            && let Some(ty) = self.repl.shown_type()
        {
            self.output.push(OutLine {
                text: format!(" : {ty}"),
                kind: OutKind::Type,
            });
        }
        // Definitions may have changed what the files mean.
        self.check();
    }

    // The panels.

    fn buffers_command(&mut self, command: Command) {
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

    fn files_command(&mut self, command: Command) {
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

    fn right_command(&mut self, command: Command) {
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

/// Moves the cursor or edits the text, as the editor and the REPL's input
/// both do.
fn move_or_edit(b: &mut Buffer, command: Command, page: usize, clipboard: &mut String) {
    let pos = b.cursor.pos;
    let select = |b: &mut Buffer, select: bool| {
        if select {
            if b.cursor.anchor.is_none() {
                b.cursor.anchor = Some(b.cursor.pos);
            }
        } else {
            b.cursor.anchor = None;
        }
    };
    let move_line = |b: &mut Buffer, down: bool, lines: usize| {
        let (line, col) = b.line_col(b.cursor.pos);
        let goal = b.goal.unwrap_or(col);
        let target = if down {
            (line + lines).min(b.lines().saturating_sub(1))
        } else {
            line.saturating_sub(lines)
        };
        b.cursor.pos = b.line_to_offset(target) + goal.min(b.line_len(target));
        b.goal = Some(goal);
    };
    match command {
        Command::Left { select: s, word } => {
            select(b, s);
            let mut p = pos.saturating_sub(1);
            if word {
                while p > 0 && !is_word(b.rope().char(p)) {
                    p -= 1;
                }
                while p > 0 && is_word(b.rope().char(p - 1)) {
                    p -= 1;
                }
            }
            b.cursor.pos = p;
            b.goal = None;
        }
        Command::Right { select: s, word } => {
            select(b, s);
            let mut p = (pos + 1).min(b.len());
            if word {
                while p < b.len() && !is_word(b.rope().char(p)) {
                    p += 1;
                }
                while p < b.len() && is_word(b.rope().char(p)) {
                    p += 1;
                }
            }
            b.cursor.pos = p;
            b.goal = None;
        }
        Command::Up { select: s } => {
            select(b, s);
            move_line(b, false, 1);
        }
        Command::Down { select: s } => {
            select(b, s);
            move_line(b, true, 1);
        }
        Command::PageUp => {
            select(b, false);
            move_line(b, false, page.max(1));
        }
        Command::PageDown => {
            select(b, false);
            move_line(b, true, page.max(1));
        }
        Command::Home { select: s } => {
            select(b, s);
            let (line, col) = b.line_col(pos);
            let start = b.line_to_offset(line);
            // Home goes to the first character of the line, then its start.
            let indent = b.line_text(line).chars().take_while(|c| *c == ' ').count();
            b.cursor.pos = start + if col == indent { 0 } else { indent };
            b.goal = None;
        }
        Command::End { select: s } => {
            select(b, s);
            let (line, _) = b.line_col(pos);
            b.cursor.pos = b.line_to_offset(line) + b.line_len(line);
            b.goal = None;
        }
        Command::SelectAll => {
            b.cursor = Cursor {
                pos: b.len(),
                anchor: Some(0),
            };
        }
        Command::Char(c) => b.insert(&c.to_string(), EditKind::Typing),
        Command::Enter | Command::LineBreak => {
            // A new line keeps the indentation, one level deeper after `{`.
            let (line, _) = b.line_col(pos);
            let text = b.line_text(line);
            let mut indent: String = text.chars().take_while(|c| *c == ' ').collect();
            let before = b.slice(b.line_to_offset(line)..pos);
            if before.trim_end().ends_with('{') || before.trim_end().ends_with("->") {
                indent += "  ";
            }
            b.insert(&format!("\n{indent}"), EditKind::Other);
        }
        Command::Backspace { word } => match b.cursor.selection() {
            Some(range) => b.delete(range),
            None if pos > 0 => {
                let mut start = pos - 1;
                if word {
                    while start > 0 && is_word(b.rope().char(start - 1)) {
                        start -= 1;
                    }
                }
                b.delete(start..pos);
            }
            None => {}
        },
        Command::Delete { word } => match b.cursor.selection() {
            Some(range) => b.delete(range),
            None if pos < b.len() => {
                let mut end = pos + 1;
                if word {
                    while end < b.len() && is_word(b.rope().char(end)) {
                        end += 1;
                    }
                }
                b.delete(pos..end);
            }
            None => {}
        },
        Command::Indent | Command::Dedent => {
            let range = b.cursor.selection().unwrap_or(pos..pos);
            let (first, _) = b.line_col(range.start);
            let (last, _) = b.line_col(range.end);
            if command == Command::Indent && b.cursor.selection().is_none() {
                b.insert("  ", EditKind::Typing);
                return;
            }
            for line in (first..=last).rev() {
                let start = b.line_to_offset(line);
                if command == Command::Indent {
                    b.replace(start..start, "  ", EditKind::Other);
                } else {
                    let spaces = b
                        .line_text(line)
                        .chars()
                        .take(2)
                        .take_while(|c| *c == ' ')
                        .count();
                    b.replace(start..start + spaces, "", EditKind::Other);
                }
            }
            b.cursor = Cursor::at(b.line_to_offset(first) + b.line_len(first));
        }
        Command::ToggleComment => {
            let range = b.cursor.selection().unwrap_or(pos..pos);
            let (first, _) = b.line_col(range.start);
            let (last, _) = b.line_col(range.end);
            let commented = (first..=last).all(|l| {
                let t = b.line_text(l);
                t.trim().is_empty() || t.trim_start().starts_with("//")
            });
            for line in (first..=last).rev() {
                let text = b.line_text(line);
                let indent = text.chars().take_while(|c| *c == ' ').count();
                let start = b.line_to_offset(line) + indent;
                if commented {
                    let rest = &text[indent..];
                    let n = if rest.starts_with("// ") {
                        3
                    } else if rest.starts_with("//") {
                        2
                    } else {
                        0
                    };
                    b.replace(start..start + n, "", EditKind::Other);
                } else if !text.trim().is_empty() {
                    b.replace(start..start, "// ", EditKind::Other);
                }
            }
        }
        Command::Cut => {
            if let Some(range) = b.cursor.selection() {
                *clipboard = b.slice(range.clone());
                b.delete(range);
            }
        }
        Command::Paste => {
            if !clipboard.is_empty() {
                b.insert(&clipboard.clone(), EditKind::Other);
            }
        }
        Command::Undo => {
            b.undo();
        }
        Command::Redo => {
            b.redo();
        }
        _ => {}
    }
    // The view follows the cursor.
    let (line, _) = b.line_col(b.cursor.pos);
    if line < b.scroll {
        b.scroll = line;
    } else if line >= b.scroll + page.max(1) {
        b.scroll = line + 1 - page.max(1);
    }
}

/// The paths of files the UI may open, for tests.
pub fn project_path(ui: &Ui, file: &str) -> Option<PathBuf> {
    ui.repl.project().root.as_ref().map(|r| r.join(file))
}
