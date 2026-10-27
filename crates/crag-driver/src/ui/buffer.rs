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

//! A text buffer (Implementation Plan §11.8.2): a rope with a file, an undo
//! history and a cursor.
//!
//! The text is a `ropey::Rope`, a balanced tree of chunks that counts
//! bytes, characters and lines in each node, so edits and line lookups
//! take time logarithmic in the size of the text. Positions are character
//! indices; the compiler's byte offsets are converted at the edges.
//!
//! Every change is an edit that records what it removed and inserted, so
//! undo replays it backwards. Edits of one kind that follow each other,
//! like typing a word, are one step of the history.

use std::path::PathBuf;

use ropey::Rope;

/// A change: at `at`, `removed` gave way to `inserted`.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Edit {
    at: usize,
    removed: String,
    inserted: String,
    /// The cursor before and after.
    before: Cursor,
    after: Cursor,
}

/// The cursor, and the other end of the selection if there is one.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Cursor {
    pub pos: usize,
    pub anchor: Option<usize>,
}

impl Cursor {
    pub fn at(pos: usize) -> Cursor {
        Cursor { pos, anchor: None }
    }

    /// The selected range, if anything is selected.
    pub fn selection(&self) -> Option<std::ops::Range<usize>> {
        let anchor = self.anchor?;
        (anchor != self.pos).then(|| anchor.min(self.pos)..anchor.max(self.pos))
    }
}

/// What kind of edit a step of the history is, so that typing merges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EditKind {
    Typing,
    Deleting,
    /// Anything else: a paste, a replacement, a formatting. It merges with
    /// nothing.
    Other,
}

pub struct Buffer {
    rope: Rope,
    /// The file, if the buffer has one.
    pub path: Option<PathBuf>,
    /// How the project shows the file, or a name for a buffer without one.
    pub name: String,
    /// Whether it must not change, as a bundled module of `std`.
    pub readonly: bool,
    pub cursor: Cursor,
    /// The first line shown and the column the cursor keeps while it moves
    /// up and down.
    pub scroll: usize,
    pub goal: Option<usize>,
    undo: Vec<(Vec<Edit>, EditKind)>,
    redo: Vec<Vec<Edit>>,
    /// The text as last saved or loaded.
    saved: String,
    /// Counts changes, so that others see when the text changed.
    pub version: u64,
}

impl Buffer {
    pub fn new(name: &str, text: &str, path: Option<PathBuf>) -> Buffer {
        Buffer {
            rope: Rope::from_str(text),
            path,
            name: name.to_string(),
            readonly: false,
            cursor: Cursor::default(),
            scroll: 0,
            goal: None,
            undo: Vec::new(),
            redo: Vec::new(),
            saved: text.to_string(),
            version: 0,
        }
    }

    pub fn rope(&self) -> &Rope {
        &self.rope
    }

    pub fn text(&self) -> String {
        self.rope.to_string()
    }

    pub fn len(&self) -> usize {
        self.rope.len_chars()
    }

    pub fn is_empty(&self) -> bool {
        self.rope.len_chars() == 0
    }

    pub fn lines(&self) -> usize {
        self.rope.len_lines()
    }

    /// Whether the text differs from what was last saved or loaded.
    pub fn dirty(&self) -> bool {
        self.rope != self.saved.as_str()
    }

    /// Marks the text as saved.
    pub fn saved(&mut self) {
        self.saved = self.text();
    }

    /// The character index where line `line`, from zero, starts; the end for
    /// a line past it.
    pub fn line_to_offset(&self, line: usize) -> usize {
        if line >= self.rope.len_lines() {
            return self.rope.len_chars();
        }
        self.rope.line_to_char(line)
    }

    /// The line and column, from zero, of a character index.
    pub fn line_col(&self, pos: usize) -> (usize, usize) {
        let pos = pos.min(self.rope.len_chars());
        let line = self.rope.char_to_line(pos);
        (line, pos - self.rope.line_to_char(line))
    }

    /// The characters of a line without its line break.
    pub fn line_len(&self, line: usize) -> usize {
        if line >= self.rope.len_lines() {
            return 0;
        }
        let slice = self.rope.line(line);
        let mut len = slice.len_chars();
        if len > 0 && slice.char(len - 1) == '\n' {
            len -= 1;
        }
        len
    }

    pub fn line_text(&self, line: usize) -> String {
        if line >= self.rope.len_lines() {
            return String::new();
        }
        let text = self.rope.line(line).to_string();
        text.strip_suffix('\n').unwrap_or(&text).to_string()
    }

    /// The byte offset of a character index, as the compiler counts.
    pub fn byte_of(&self, pos: usize) -> u32 {
        self.rope.char_to_byte(pos.min(self.rope.len_chars())) as u32
    }

    /// The character index of a byte offset.
    pub fn char_of(&self, byte: u32) -> usize {
        self.rope
            .byte_to_char((byte as usize).min(self.rope.len_bytes()))
    }

    pub fn slice(&self, range: std::ops::Range<usize>) -> String {
        let end = range.end.min(self.len());
        let start = range.start.min(end);
        self.rope.slice(start..end).to_string()
    }

    /// Replaces `range` with `text` and puts the cursor at the end of what
    /// was inserted. Edits of `kind` typing or deleting next to the last
    /// one join its step of the history.
    pub fn replace(&mut self, range: std::ops::Range<usize>, text: &str, kind: EditKind) {
        let end = range.end.min(self.len());
        let start = range.start.min(end);
        let removed = self.slice(start..end);
        if removed.is_empty() && text.is_empty() {
            return;
        }
        let before = self.cursor;
        self.rope.remove(start..end);
        self.rope.insert(start, text);
        let after = Cursor::at(start + text.chars().count());
        self.cursor = after;
        self.goal = None;
        self.version += 1;
        self.redo.clear();
        let edit = Edit {
            at: start,
            removed,
            inserted: text.to_string(),
            before,
            after,
        };
        let joins = match self.undo.last() {
            Some((edits, last)) if *last == kind && kind != EditKind::Other => {
                let previous = edits.last().expect("a step has an edit");
                match kind {
                    // Typing on at the end of what was typed, within a line.
                    EditKind::Typing => {
                        previous.after.pos == start
                            && !text.contains('\n')
                            && edit.removed.is_empty()
                    }
                    // Deleting on from where the last deletion was.
                    EditKind::Deleting => {
                        edit.inserted.is_empty() && (start == previous.at || end == previous.at)
                    }
                    EditKind::Other => false,
                }
            }
            _ => false,
        };
        match joins {
            true => self.undo.last_mut().expect("joins a step").0.push(edit),
            false => self.undo.push((vec![edit], kind)),
        }
    }

    /// Inserts at the cursor, replacing the selection.
    pub fn insert(&mut self, text: &str, kind: EditKind) {
        let range = self
            .cursor
            .selection()
            .unwrap_or(self.cursor.pos..self.cursor.pos);
        self.replace(range, text, kind);
    }

    /// Deletes `range`.
    pub fn delete(&mut self, range: std::ops::Range<usize>) {
        self.replace(range, "", EditKind::Deleting);
    }

    /// Replaces the whole text, as formatting does, keeping the cursor's
    /// line and column where they still exist.
    pub fn set_text(&mut self, text: &str) {
        let (line, col) = self.line_col(self.cursor.pos);
        self.replace(0..self.len(), text, EditKind::Other);
        let line = line.min(self.lines().saturating_sub(1));
        self.cursor = Cursor::at(self.line_to_offset(line) + col.min(self.line_len(line)));
    }

    /// Takes back the last step of the history; false if there was none.
    pub fn undo(&mut self) -> bool {
        let Some((edits, _)) = self.undo.pop() else {
            return false;
        };
        for edit in edits.iter().rev() {
            let end = edit.at + edit.inserted.chars().count();
            self.rope.remove(edit.at..end);
            self.rope.insert(edit.at, &edit.removed);
        }
        self.cursor = edits[0].before;
        self.version += 1;
        self.redo.push(edits);
        true
    }

    /// Does again what `undo` took back; false if there was nothing.
    pub fn redo(&mut self) -> bool {
        let Some(edits) = self.redo.pop() else {
            return false;
        };
        for edit in &edits {
            let end = edit.at + edit.removed.chars().count();
            self.rope.remove(edit.at..end);
            self.rope.insert(edit.at, &edit.inserted);
        }
        self.cursor = edits.last().expect("a step has an edit").after;
        self.version += 1;
        self.undo.push((edits, EditKind::Other));
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn edits_keep_lines_and_offsets() {
        let mut b = Buffer::new("t", "let x = 1\nlet ü = 2\n", None);
        assert_eq!(b.lines(), 3);
        assert_eq!(b.line_to_offset(1), 10);
        assert_eq!(b.line_col(14), (1, 4));
        assert_eq!(b.byte_of(15), 16);
        assert_eq!(b.char_of(16), 15);
        b.cursor = Cursor::at(9);
        b.insert("0", EditKind::Typing);
        assert_eq!(b.line_text(0), "let x = 10");
        assert!(b.dirty());
        b.delete(9..10);
        assert_eq!(b.line_text(0), "let x = 1");
        assert!(!b.dirty());
    }

    #[test]
    fn typing_a_word_is_one_step_of_undo() {
        let mut b = Buffer::new("t", "fn f() {}\n", None);
        b.cursor = Cursor::at(8);
        for c in ["4", "2"] {
            b.insert(c, EditKind::Typing);
        }
        b.insert("\n", EditKind::Typing);
        assert_eq!(b.text(), "fn f() {42\n}\n");
        assert!(b.undo());
        assert_eq!(b.text(), "fn f() {42}\n");
        assert!(b.undo());
        assert_eq!(b.text(), "fn f() {}\n");
        assert_eq!(b.cursor.pos, 8);
        assert!(!b.undo());
        assert!(b.redo());
        assert_eq!(b.text(), "fn f() {42}\n");
        assert_eq!(b.cursor.pos, 10);
    }

    #[test]
    fn a_selection_is_replaced() {
        let mut b = Buffer::new("t", "hello world", None);
        b.cursor = Cursor {
            pos: 11,
            anchor: Some(6),
        };
        assert_eq!(b.cursor.selection(), Some(6..11));
        b.insert("rope", EditKind::Other);
        assert_eq!(b.text(), "hello rope");
        b.set_text("hi\nthere");
        assert_eq!(b.line_col(b.cursor.pos), (0, 2));
    }

    #[test]
    fn a_large_text_edits_quickly() {
        let line = "let value = compute(1, 2, 3) + other\n";
        let text = line.repeat(200_000);
        let mut b = Buffer::new("big", &text, None);
        let start = std::time::Instant::now();
        for i in 0..10_000 {
            let at = b.line_to_offset((i * 17) % 200_000);
            b.cursor = Cursor::at(at);
            b.insert("x", EditKind::Other);
        }
        assert_eq!(b.lines(), 200_001);
        assert!(start.elapsed().as_secs() < 5, "{:?}", start.elapsed());
    }
}
