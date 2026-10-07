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
//! a final `Eof` token carries the trivia at the end of the file. The parser
//! and the concrete syntax tree build on it.

mod lexer;
mod token;

pub use lexer::{lex, relex};
pub use token::{TextEdit, Token, TokenKind, Trivia, TriviaKind};
