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

//! Tokens, their kinds and the trivia in front of them.

use std::ops::Range;

/// Every kind of token (Specification Appendix D.1).
///
/// Literals are lexed by their shape only. Whether an escape is known, a
/// number fits its type or a literal is closed is checked when the literal
/// is decoded, so an unterminated string is still a `Str` token.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TokenKind {
    /// A name. A keyword directly after `.` or `?.` is a field name and
    /// lexes as `Ident` (Specification §2.5).
    Ident,
    /// A lone `_`.
    Underscore,
    Int,
    Float,
    /// A string literal without interpolation, ordinary or triple-quoted.
    Str,
    /// A string up to and including the `{` of its first interpolation.
    StrStart,
    /// Like `StrStart`, for a triple-quoted string.
    TripleStrStart,
    /// From the `}` ending an interpolation to the `{` of the next one.
    StrMid,
    /// From the `}` ending the last interpolation to the closing quote.
    StrEnd,
    /// `b"…"`, which has no interpolation.
    Bytes,
    /// `'…'`.
    CodePoint,

    // Keywords (Specification Appendix B.1). Contextual keywords lex as
    // `Ident`.
    Let,
    Var,
    Ref,
    Ext,
    Embed,
    Type,
    Form,
    Fn,
    Test,
    Pub,
    Opaque,
    Distinct,
    Is,
    Where,
    On,
    If,
    Else,
    Case,
    Pass,
    For,
    In,
    Return,
    Emit,
    Atomic,
    Lazy,
    Import,
    As,
    And,
    Or,
    Not,

    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Comma,
    Semicolon,
    Colon,
    Dot,
    DotDot,
    QuestionDot,
    /// `???`.
    Hole,
    Arrow,
    Equals,
    EqEq,
    BangEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Plus,
    PlusPercent,
    Minus,
    MinusPercent,
    Star,
    StarPercent,
    Slash,
    Percent,
    Pipe,
    /// One character that may begin or continue a prefix (§2.8): `~ ! ? @ #
    /// $ ^ &`. Which prefixes exist depends on the imports, so the parser
    /// joins adjacent symbol tokens by the longest declared prefix.
    Symbol,

    /// A newline that ends a statement (§2.3). Every other newline is
    /// trivia.
    Newline,
    /// A character no token starts with, or a block comment that is never
    /// closed.
    Error,
    /// The end of the file, carrying the trivia after the last token.
    Eof,
}

impl TokenKind {
    pub fn keyword(word: &str) -> Option<TokenKind> {
        use TokenKind::*;
        Some(match word {
            "let" => Let,
            "var" => Var,
            "ref" => Ref,
            "ext" => Ext,
            "embed" => Embed,
            "type" => Type,
            "form" => Form,
            "fn" => Fn,
            "test" => Test,
            "pub" => Pub,
            "opaque" => Opaque,
            "distinct" => Distinct,
            "is" => Is,
            "where" => Where,
            "on" => On,
            "if" => If,
            "else" => Else,
            "case" => Case,
            "pass" => Pass,
            "for" => For,
            "in" => In,
            "return" => Return,
            "emit" => Emit,
            "atomic" => Atomic,
            "lazy" => Lazy,
            "import" => Import,
            "as" => As,
            "and" => And,
            "or" => Or,
            "not" => Not,
            _ => return None,
        })
    }

    pub fn is_keyword(self) -> bool {
        (TokenKind::Let as u8..=TokenKind::Not as u8).contains(&(self as u8))
    }

    /// Whether a line ending in this token continues on the next line: a
    /// binary operator, `,` or `->` (§2.3).
    pub fn continues_line(self) -> bool {
        use TokenKind::*;
        matches!(
            self,
            Plus | PlusPercent
                | Minus
                | MinusPercent
                | Star
                | StarPercent
                | Slash
                | Percent
                | DotDot
                | EqEq
                | BangEq
                | Lt
                | LtEq
                | Gt
                | GtEq
                | Is
                | And
                | Or
                | Comma
                | Arrow
        )
    }
}

/// A token: its kind, its text and the trivia in front of it, as byte
/// offsets into the source. The trivia is `trivia_start..start`, the text
/// `start..end`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub trivia_start: u32,
    pub start: u32,
    pub end: u32,
}

impl Token {
    pub fn range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }

    pub fn text<'a>(&self, source: &'a str) -> &'a str {
        &source[self.range()]
    }

    /// The whitespace, newlines and comments in front of the token.
    pub fn trivia<'a>(&self, source: &'a str) -> Trivia<'a> {
        Trivia {
            text: &source[..self.start as usize],
            pos: self.trivia_start as usize,
        }
    }

    pub(crate) fn shifted(self, delta: i64) -> Token {
        let shift = |offset: u32| (offset as i64 + delta) as u32;
        Token {
            kind: self.kind,
            trivia_start: shift(self.trivia_start),
            start: shift(self.start),
            end: shift(self.end),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TriviaKind {
    /// Spaces, tabs and carriage returns.
    Whitespace,
    /// A newline that does not end a statement.
    Newline,
    LineComment,
    BlockComment,
}

/// The pieces of a token's trivia, with their byte ranges in the source.
pub struct Trivia<'a> {
    /// The source up to the token, so the pieces end where it begins.
    text: &'a str,
    pos: usize,
}

impl Iterator for Trivia<'_> {
    type Item = (TriviaKind, Range<usize>);

    fn next(&mut self) -> Option<Self::Item> {
        let bytes = self.text.as_bytes();
        let start = self.pos;
        let kind = match bytes.get(start)? {
            b'\n' => {
                self.pos += 1;
                TriviaKind::Newline
            }
            b'/' if bytes.get(start + 1) == Some(&b'/') => {
                self.pos = bytes[start..]
                    .iter()
                    .position(|&b| b == b'\n')
                    .map_or(bytes.len(), |i| start + i);
                TriviaKind::LineComment
            }
            b'/' => {
                self.pos = self.text[start + 2..]
                    .find("*/")
                    .map_or(bytes.len(), |i| start + 2 + i + 2);
                TriviaKind::BlockComment
            }
            _ => {
                let len = bytes[start..]
                    .iter()
                    .position(|b| !matches!(b, b' ' | b'\t' | b'\r'))
                    .unwrap_or(bytes.len() - start);
                self.pos += len;
                TriviaKind::Whitespace
            }
        };
        Some((kind, start..self.pos))
    }
}

/// A change to a source text: the bytes `start..end` of the old text are
/// replaced by `insert`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TextEdit {
    pub start: u32,
    pub end: u32,
    pub insert: String,
}

impl TextEdit {
    pub fn apply(&self, text: &str) -> String {
        let mut out = String::with_capacity(text.len() + self.insert.len());
        out.push_str(&text[..self.start as usize]);
        out.push_str(&self.insert);
        out.push_str(&text[self.end as usize..]);
        out
    }

    /// How much longer the text gets, in bytes.
    pub fn delta(&self) -> i64 {
        self.insert.len() as i64 - (self.end - self.start) as i64
    }
}
