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

//! Crag syntax (Implementation Plan §11.4.1–§11.4.3).
//!
//! The lexer cuts source text into tokens. It is lossless: every byte of the
//! source belongs to exactly one token or to the trivia in front of one, and
//! a final `Eof` token carries the trivia at the end of the file.
//!
//! The parser turns the tokens into a concrete syntax tree, lossless as
//! well: its leaves, trivia included, spell out the source exactly. A green
//! tree holds the shape and the text; a red tree over it adds parents and
//! positions while walking. After an edit, `reparse` parses again only the
//! block the edit falls into, where it can.

mod grammar;
mod green;
mod kind;
mod lexer;
mod parser;
mod red;
mod reparse;
mod token;

pub use green::{GreenElement, GreenNode, GreenToken};
pub use kind::{LeafKind, SyntaxKind};
pub use lexer::{lex, relex};
pub use parser::{ParseError, parse};
pub use red::{SyntaxElement, SyntaxNode, SyntaxToken};
pub use reparse::reparse;
pub use token::{TextEdit, Token, TokenKind, Trivia, TriviaKind};
