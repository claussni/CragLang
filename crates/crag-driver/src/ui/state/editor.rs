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

//! The editor's commands: moving through places and problems, editing,
//! completion, information, definitions, references and search.

use super::*;

impl Ui {
    pub(super) fn back(&mut self) {
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

    pub(super) fn forward(&mut self) {
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
    pub(super) fn next_problem(&mut self) {
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

    pub(super) fn edit(&mut self, command: Command) {
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
    pub(super) fn module_path(&self, file: &str) -> Option<String> {
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

    pub(super) fn find_next(&mut self, query: &str, replacement: Option<&str>) {
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
}
