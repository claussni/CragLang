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
use std::rc::Rc;
use std::time::{Duration, Instant};

use crate::debug::{Pause, Resume};
use crate::diagnostics::{check, line_col};
use crate::lsp::analysis;
use crate::repl::{EvalOutput, Repl, is_complete};

use super::buffer::{Buffer, Cursor, EditKind};
use super::highlight::Highlights;
use super::keys::{Command, key_name};

mod command;
mod console;
mod editor;
mod panes;

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
    /// typing, the app's stopped tasks show, and its hot functions are
    /// swapped for optimized code.
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
            let _ = self.repl.tier_up_app();
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
