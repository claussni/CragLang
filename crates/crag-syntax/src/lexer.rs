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

//! The lexer (Implementation Plan §11.4.1): a hand-written loop over bytes.
//!
//! Besides its position, the lexer keeps a small state: the brackets and
//! string interpolations that are open, and the kind of the last token. The
//! state decides three things:
//!
//! - whether a newline ends a statement (§2.3): not inside `( )` or `[ ]`
//!   or an interpolation, not after a binary operator other than `..`, `,`
//!   or `->`, and not before a line that begins with `.`, `?.` or `else`;
//! - whether a `}` closes a block or an interpolation, which continues the
//!   string;
//! - whether a keyword is a field name, after `.` or `?.`.
//!
//! The state changes only through `State::advance`, by the kind of each
//! token. Replaying the kinds of a token list therefore recovers the state
//! at any token, which is what lets `relex` start in the middle of a file.

use crate::token::{TextEdit, Token, TokenKind};

/// Cuts `text` into tokens. The last token is always `Eof`.
pub fn lex(text: &str) -> Vec<Token> {
    let mut lexer = Lexer::new(text, 0, State::default());
    let mut tokens = Vec::new();
    loop {
        let token = lexer.next_token();
        tokens.push(token);
        if token.kind == TokenKind::Eof {
            return tokens;
        }
    }
}

/// How far past its end the lexer may look to decide a token, in bytes:
/// `1..` needs two to tell a range from `1.5`, `???` two to tell it from `?`.
const LOOKAHEAD: usize = 2;

/// Relexes after an edit. `text` is the new text, `old` the tokens of the
/// text before `edit`. The result equals `lex(text)`.
///
/// Lexing restarts at the last token no lookahead from before the edit could
/// see, backing up over newline tokens, whose meaning depends on the next
/// line. It stops once a token after the edit starts where an old token
/// started, shifted by the edit, in the same state: from there on the old
/// tokens are reused with shifted offsets.
pub fn relex(text: &str, old: &[Token], edit: &TextEdit) -> Vec<Token> {
    let edit_start = edit.start as usize;
    let edit_end = edit_start + edit.insert.len();
    let delta = edit.delta();

    let first = old.partition_point(|t| t.end as usize + LOOKAHEAD < edit_start);
    let mut restart = first.min(old.len() - 1).saturating_sub(1);
    while restart > 0 && old[restart - 1].kind == TokenKind::Newline {
        restart -= 1;
    }

    let mut state = State::default();
    for token in &old[..restart] {
        state.advance(token.kind);
    }
    let mut out = old[..restart].to_vec();
    // `old_state` is the state in front of `old[next_old]`.
    let mut old_state = state.clone();
    let mut next_old = restart;
    let mut lexer = Lexer::new(text, old[restart].trivia_start as usize, state);
    loop {
        let pos = lexer.pos as i64;
        if lexer.pos >= edit_end {
            while next_old < old.len() && old[next_old].trivia_start as i64 + delta < pos {
                old_state.advance(old[next_old].kind);
                next_old += 1;
            }
            if next_old < old.len()
                && old[next_old].trivia_start as i64 + delta == pos
                && old_state == lexer.state
            {
                out.extend(old[next_old..].iter().map(|t| t.shifted(delta)));
                return out;
            }
        }
        let token = lexer.next_token();
        out.push(token);
        if token.kind == TokenKind::Eof {
            return out;
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Open {
    Paren,
    Bracket,
    Brace,
    Interpolation { triple: bool },
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
struct State {
    open: Vec<Open>,
    last: Option<TokenKind>,
}

impl State {
    fn advance(&mut self, kind: TokenKind) {
        use TokenKind::*;
        match kind {
            LParen => self.open.push(Open::Paren),
            LBracket => self.open.push(Open::Bracket),
            LBrace => self.open.push(Open::Brace),
            StrStart => self.open.push(Open::Interpolation { triple: false }),
            TripleStrStart => self.open.push(Open::Interpolation { triple: true }),
            RParen => self.close(Open::Paren),
            RBracket => self.close(Open::Bracket),
            RBrace => self.close(Open::Brace),
            StrMid | StrEnd => {
                if let Some(i) = self.interpolation() {
                    let keep = if kind == StrMid { i + 1 } else { i };
                    self.open.truncate(keep);
                }
            }
            _ => {}
        }
        self.last = Some(kind);
    }

    /// Closes the innermost `open` and whatever was left open inside it. A
    /// closer without a match inside the current interpolation is ignored.
    fn close(&mut self, open: Open) {
        for i in (0..self.open.len()).rev() {
            match self.open[i] {
                o if o == open => return self.open.truncate(i),
                Open::Interpolation { .. } => return,
                _ => {}
            }
        }
    }

    /// The index of the interpolation a `}` would close, if it does not
    /// close a block first.
    fn interpolation(&self) -> Option<usize> {
        for i in (0..self.open.len()).rev() {
            match self.open[i] {
                Open::Brace => return None,
                Open::Interpolation { .. } => return Some(i),
                _ => {}
            }
        }
        None
    }

    fn newlines_are_whitespace(&self) -> bool {
        matches!(
            self.open.last(),
            Some(Open::Paren | Open::Bracket | Open::Interpolation { .. })
        ) || self.last.is_some_and(TokenKind::continues_line)
    }
}

struct Lexer<'a> {
    text: &'a str,
    pos: usize,
    state: State,
    /// The start of the next token after a run of trivia, and whether it
    /// continues the line before; a run with many newlines asks often.
    next_line: Option<(usize, bool)>,
}

impl<'a> Lexer<'a> {
    fn new(text: &'a str, pos: usize, state: State) -> Lexer<'a> {
        assert!(text.len() <= u32::MAX as usize, "source text over 4 GiB");
        Lexer {
            text,
            pos,
            state,
            next_line: None,
        }
    }

    fn byte(&self, ahead: usize) -> Option<u8> {
        self.text.as_bytes().get(self.pos + ahead).copied()
    }

    fn rest(&self) -> &'a str {
        &self.text[self.pos..]
    }

    fn next_token(&mut self) -> Token {
        let trivia_start = self.pos;
        let (start, kind) = loop {
            let start = self.pos;
            match self.byte(0) {
                None => break (start, TokenKind::Eof),
                Some(b' ' | b'\t' | b'\r') => self.pos += 1,
                Some(b'\n') => {
                    self.pos += 1;
                    if !self.newline_is_whitespace(start) {
                        break (start, TokenKind::Newline);
                    }
                }
                Some(b'/') if self.byte(1) == Some(b'/') => self.line_comment(),
                Some(b'/') if self.byte(1) == Some(b'*') => {
                    if !self.block_comment() {
                        break (start, TokenKind::Error);
                    }
                }
                Some(_) => break (start, self.token()),
            }
        };
        self.state.advance(kind);
        Token {
            kind,
            trivia_start: trivia_start as u32,
            start: start as u32,
            end: self.pos as u32,
        }
    }

    fn line_comment(&mut self) {
        self.pos += self.rest().find('\n').unwrap_or(self.rest().len());
    }

    /// Skips a block comment; false if it is never closed, in which case it
    /// runs to the end of the file.
    fn block_comment(&mut self) -> bool {
        match self.rest()[2..].find("*/") {
            Some(i) => {
                self.pos += 2 + i + 2;
                true
            }
            None => {
                self.pos = self.text.len();
                false
            }
        }
    }

    fn newline_is_whitespace(&mut self, newline: usize) -> bool {
        if self.state.newlines_are_whitespace() {
            return true;
        }
        match self.next_line {
            Some((next, continues)) if next > newline => continues,
            _ => {
                let next = self.skip_trivia(newline + 1);
                let continues = continues_previous_line(&self.text[next..]);
                self.next_line = Some((next, continues));
                continues
            }
        }
    }

    /// The position of the first byte at or after `pos` that is not
    /// whitespace, a newline or a comment.
    fn skip_trivia(&self, mut pos: usize) -> usize {
        let bytes = self.text.as_bytes();
        while let Some(&b) = bytes.get(pos) {
            match b {
                b' ' | b'\t' | b'\r' | b'\n' => pos += 1,
                b'/' if bytes.get(pos + 1) == Some(&b'/') => {
                    pos += self.text[pos..].find('\n').unwrap_or(bytes.len() - pos);
                }
                b'/' if bytes.get(pos + 1) == Some(&b'*') => {
                    match self.text[pos + 2..].find("*/") {
                        Some(i) => pos += 2 + i + 2,
                        None => return bytes.len(),
                    }
                }
                _ => break,
            }
        }
        pos
    }

    fn token(&mut self) -> TokenKind {
        use TokenKind::*;
        let one = |lexer: &mut Lexer, kind| {
            lexer.pos += 1;
            kind
        };
        let two = |lexer: &mut Lexer, second: u8, double, single| {
            if lexer.byte(1) == Some(second) {
                lexer.pos += 2;
                double
            } else {
                lexer.pos += 1;
                single
            }
        };
        match self.byte(0).unwrap() {
            b'(' => one(self, LParen),
            b')' => one(self, RParen),
            b'[' => one(self, LBracket),
            b']' => one(self, RBracket),
            b'{' => one(self, LBrace),
            b'}' => {
                self.pos += 1;
                match self.state.interpolation() {
                    Some(i) => {
                        let Open::Interpolation { triple } = self.state.open[i] else {
                            unreachable!()
                        };
                        match self.string_body(triple, true) {
                            Body::Interpolation => StrMid,
                            Body::End => StrEnd,
                        }
                    }
                    None => RBrace,
                }
            }
            b',' => one(self, Comma),
            b';' => one(self, Semicolon),
            b':' => one(self, Colon),
            b'|' => one(self, Pipe),
            b'.' => two(self, b'.', DotDot, Dot),
            b'=' => two(self, b'=', EqEq, Equals),
            b'<' => two(self, b'=', LtEq, Lt),
            b'>' => two(self, b'=', GtEq, Gt),
            b'+' => two(self, b'%', PlusPercent, Plus),
            b'*' => two(self, b'%', StarPercent, Star),
            b'/' => one(self, Slash),
            b'%' => one(self, Percent),
            b'-' => match self.byte(1) {
                Some(b'>') => {
                    self.pos += 2;
                    Arrow
                }
                _ => two(self, b'%', MinusPercent, Minus),
            },
            b'!' => two(self, b'=', BangEq, Symbol),
            b'?' if self.rest().starts_with("???") => {
                self.pos += 3;
                Hole
            }
            b'?' => two(self, b'.', QuestionDot, Symbol),
            b'~' | b'@' | b'#' | b'$' | b'^' | b'&' => one(self, Symbol),
            b'"' => self.string(),
            b'\'' => self.code_point(),
            b'b' if self.byte(1) == Some(b'"') => {
                self.pos += 2;
                self.string_body(false, false);
                Bytes
            }
            b'0'..=b'9' => self.number(),
            _ => {
                let c = self.rest().chars().next().unwrap();
                if c == '_' || c.is_alphabetic() {
                    self.word()
                } else {
                    self.pos += c.len_utf8();
                    Error
                }
            }
        }
    }

    fn string(&mut self) -> TokenKind {
        let triple = self.rest().starts_with("\"\"\"");
        self.pos += if triple { 3 } else { 1 };
        match (self.string_body(triple, true), triple) {
            (Body::End, _) => TokenKind::Str,
            (Body::Interpolation, false) => TokenKind::StrStart,
            (Body::Interpolation, true) => TokenKind::TripleStrStart,
        }
    }

    /// Scans string content up to and including the closing quote or the
    /// `{` of an interpolation. An ordinary string that reaches the end of
    /// its line, or any string that reaches the end of the file, ends there
    /// unclosed.
    fn string_body(&mut self, triple: bool, interpolates: bool) -> Body {
        let bytes = self.text.as_bytes();
        loop {
            match self.byte(0) {
                None => return Body::End,
                Some(b'\n') if !triple => return Body::End,
                Some(b'\\') => {
                    self.pos += 1;
                    match self.rest().chars().next() {
                        Some('\n') if !triple => {}
                        Some(c) => self.pos += c.len_utf8(),
                        None => {}
                    }
                }
                Some(b'"') if !triple => {
                    self.pos += 1;
                    return Body::End;
                }
                Some(b'"') if self.rest().starts_with("\"\"\"") => {
                    self.pos += 3;
                    return Body::End;
                }
                Some(b'{') if interpolates => {
                    if bytes.get(self.pos + 1) == Some(&b'{') {
                        self.pos += 2;
                    } else {
                        self.pos += 1;
                        return Body::Interpolation;
                    }
                }
                Some(_) => self.pos += self.rest().chars().next().unwrap().len_utf8(),
            }
        }
    }

    fn code_point(&mut self) -> TokenKind {
        self.pos += 1;
        loop {
            match self.byte(0) {
                None | Some(b'\n') => break,
                Some(b'\'') => {
                    self.pos += 1;
                    break;
                }
                Some(b'\\') => {
                    self.pos += 1;
                    if let Some(c) = self.rest().chars().next().filter(|&c| c != '\n') {
                        self.pos += c.len_utf8();
                    }
                }
                Some(_) => self.pos += self.rest().chars().next().unwrap().len_utf8(),
            }
        }
        TokenKind::CodePoint
    }

    /// A number takes every letter, digit and `_` that follows, so `12ab` is
    /// one malformed literal. A `.` belongs to it only before a digit, which
    /// keeps `1..9` a range and `2.abs()` a call.
    fn number(&mut self) -> TokenKind {
        let digits = |lexer: &mut Lexer| {
            while lexer
                .byte(0)
                .is_some_and(|b| b.is_ascii_digit() || b == b'_')
            {
                lexer.pos += 1;
            }
        };
        let mut kind = TokenKind::Int;
        let radix = self.byte(0) == Some(b'0') && matches!(self.byte(1), Some(b'x' | b'b' | b'o'));
        if !radix {
            digits(self);
            if self.byte(0) == Some(b'.') && self.byte(1).is_some_and(|b| b.is_ascii_digit()) {
                self.pos += 1;
                digits(self);
                kind = TokenKind::Float;
            }
            let digit_at = |ahead| self.byte(ahead).is_some_and(|b: u8| b.is_ascii_digit());
            if matches!(self.byte(0), Some(b'e' | b'E')) {
                let sign = matches!(self.byte(1), Some(b'+' | b'-')) as usize;
                if digit_at(1 + sign) {
                    self.pos += 1 + sign;
                    digits(self);
                    kind = TokenKind::Float;
                }
            }
        }
        while self
            .byte(0)
            .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            self.pos += 1;
        }
        kind
    }

    fn word(&mut self) -> TokenKind {
        let start = self.pos;
        let len = self
            .rest()
            .find(|c: char| !(c == '_' || c.is_alphanumeric()))
            .unwrap_or(self.rest().len());
        self.pos += len;
        let word = &self.text[start..self.pos];
        let field = matches!(
            self.state.last,
            Some(TokenKind::Dot | TokenKind::QuestionDot)
        );
        match TokenKind::keyword(word) {
            _ if word == "_" => TokenKind::Underscore,
            Some(keyword) if !field => keyword,
            _ => TokenKind::Ident,
        }
    }
}

enum Body {
    Interpolation,
    End,
}

/// Whether a line starting with `text` continues the line before: it
/// begins with `.` (but not `..`), `?.` or `else` (§2.3).
fn continues_previous_line(text: &str) -> bool {
    if text.starts_with("?.") || (text.starts_with('.') && !text.starts_with("..")) {
        return true;
    }
    text.strip_prefix("else")
        .is_some_and(|rest| !rest.starts_with(|c: char| c == '_' || c.is_alphanumeric()))
}
