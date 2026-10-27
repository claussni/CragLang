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

//! The comments of a file, and the empty lines that keep their place.
//!
//! Comments are trivia in the tree. The printer emits them by position:
//! before a token it writes the comments that come before it, and after a
//! token the comment on the rest of its line.

use std::collections::HashSet;

use crag_syntax::{LeafKind, SyntaxNode, TokenKind, TriviaKind};

pub(crate) struct Comment {
    pub start: u32,
    pub text: String,
    pub line: bool,
    /// Whether the comment begins its line.
    pub own_line: bool,
    /// Whether an empty line comes before it.
    pub blank_before: bool,
    /// Whether a line break follows it before the next token.
    pub newline_after: bool,
    /// The end of the token before it.
    pub after: u32,
}

pub(crate) struct Comments {
    pub list: Vec<Comment>,
    /// The tokens after an empty line, by their start.
    pub blank_before: HashSet<u32>,
}

impl Comments {
    pub fn collect(root: &SyntaxNode) -> Comments {
        let mut list: Vec<Comment> = Vec::new();
        let mut blank_before = HashSet::new();
        let mut newlines = 0;
        let mut first = true;
        // The last comment, until a token follows it.
        let mut open: Option<usize> = None;
        let mut after = 0;
        for token in root.descendant_tokens() {
            match token.kind() {
                LeafKind::Trivia(TriviaKind::Newline) | LeafKind::Token(TokenKind::Newline) => {
                    newlines += 1;
                    if let Some(i) = open {
                        list[i].newline_after = true;
                    }
                }
                LeafKind::Trivia(kind @ (TriviaKind::LineComment | TriviaKind::BlockComment)) => {
                    list.push(Comment {
                        start: token.range().start,
                        text: token.text().to_string(),
                        line: kind == TriviaKind::LineComment,
                        own_line: first || newlines > 0,
                        blank_before: newlines > 1,
                        newline_after: false,
                        after,
                    });
                    open = Some(list.len() - 1);
                    newlines = 0;
                }
                LeafKind::Trivia(TriviaKind::Whitespace) => {}
                LeafKind::Token(_) => {
                    after = token.range().end;
                    if newlines > 1 {
                        blank_before.insert(token.range().start);
                    }
                    newlines = 0;
                    first = false;
                    open = None;
                }
            }
        }
        Comments { list, blank_before }
    }
}
