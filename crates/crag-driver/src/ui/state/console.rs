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

//! The REPL pane: its input, history and prompt, and what a run
//! prints and shows.

use super::*;

impl Ui {
    pub(super) fn repl_command(&mut self, command: Command) {
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
    pub(super) fn submit(&mut self, text: &str) {
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
    pub(super) fn show_printed(&mut self, all: bool) {
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
}
