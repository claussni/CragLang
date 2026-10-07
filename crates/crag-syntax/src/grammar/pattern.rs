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

//! Patterns (Specification Appendix D.5).

use super::{delimited, ty};
use crate::kind::SyntaxKind as S;
use crate::parser::{Parser, TokenSet};
use crate::token::TokenKind as T;

const LITERALS: TokenSet = TokenSet::new(&[T::Int, T::Float, T::Str, T::Bytes, T::CodePoint]);

/// Tokens a missing pattern leaves alone.
const NOT_A_PATTERN: TokenSet = TokenSet::new(&[
    T::Newline,
    T::RBrace,
    T::RParen,
    T::RBracket,
    T::Eof,
    T::Comma,
    T::Arrow,
    T::Equals,
    T::Colon,
    T::In,
    T::Where,
]);

/// `alt ("|" alt)*`. Where `binds` is false, a `:` after a name is left to
/// the caller as a type annotation (`let x: Int`, `{ n: Int -> … }`); where
/// it is true, `n: Int` binds `n` and matches `Int` (§6.9).
pub(crate) fn pattern(p: &mut Parser, binds: bool) {
    let start = p.checkpoint();
    alternative(p, binds);
    if p.at(T::Pipe) {
        p.start_at(start, S::OrPat);
        while p.eat(T::Pipe) {
            alternative(p, binds);
        }
        p.finish_node();
    }
}

fn alternative(p: &mut Parser, binds: bool) {
    if !p.enter() {
        return;
    }
    let start = p.checkpoint();
    match p.current() {
        T::Underscore => {
            p.start(S::WildcardPat);
            p.bump();
            p.finish_node();
        }
        kind if LITERALS.contains(kind) => {
            p.bump();
            let kind = if p.eat(T::DotDot) {
                if p.at_set(LITERALS) {
                    p.bump();
                } else {
                    p.error("expected a literal");
                }
                S::RangePat
            } else {
                S::LiteralPat
            };
            p.start_at(start, kind);
            p.finish_node();
        }
        T::LParen => {
            p.start(S::RecordPat);
            fields(p);
            p.finish_node();
        }
        T::LBracket => {
            p.start(S::ListPat);
            p.bump();
            delimited(p, T::RBracket, "`]`", "a pattern", |p| {
                if p.at(T::DotDot) {
                    p.start(S::RestPat);
                    p.bump();
                    p.eat(T::Ident);
                    p.finish_node();
                } else {
                    pattern(p, true);
                }
            });
            p.finish_node();
        }
        T::Ident if binds && p.nth(1) == T::Colon => {
            p.start(S::BindPat);
            p.bump();
            p.bump();
            alternative(p, binds);
            p.finish_node();
        }
        T::Ident => {
            p.bump();
            let type_args = p.at(T::LBracket);
            if type_args {
                ty::type_args(p);
            }
            let kind = if p.at(T::LParen) {
                fields(p);
                S::RecordPat
            } else if type_args {
                S::TypePat
            } else {
                S::NamePat
            };
            p.start_at(start, kind);
            p.finish_node();
        }
        _ if p.at_set(NOT_A_PATTERN) => p.error("expected a pattern"),
        _ => p.bump_error("expected a pattern"),
    }
}

/// `( field, … )`, where a field is `name: pattern?` or a pattern.
fn fields(p: &mut Parser) {
    p.bump();
    delimited(p, T::RParen, "`)`", "a field pattern", |p| {
        let named = (p.at(T::Ident) || p.current().is_keyword()) && p.nth(1) == T::Colon;
        if named {
            p.start(S::PatField);
            p.bump();
            p.bump();
            if !p.at(T::Comma) && !p.at(T::RParen) {
                pattern(p, true);
            }
            p.finish_node();
        } else {
            pattern(p, true);
        }
    });
}
