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

//! Types (Specification Appendix D.6).

use super::{delimited, is_clause};
use crate::kind::SyntaxKind as S;
use crate::parser::{Parser, TokenSet};
use crate::token::TokenKind as T;

/// Tokens a missing type leaves alone.
const NOT_A_TYPE: TokenSet = TokenSet::new(&[
    T::Newline,
    T::RBrace,
    T::RParen,
    T::RBracket,
    T::Eof,
    T::Comma,
    T::Equals,
    T::LBrace,
    T::Arrow,
]);

/// A function type, or a union of one or more atoms.
pub(crate) fn ty(p: &mut Parser) {
    if !p.enter() {
        return;
    }
    if p.at(T::LParen) && p.nth(p.skip_balanced(0)) == T::Arrow {
        // Everything after `->` is the result (§3.7).
        p.start(S::FnType);
        p.start(S::FnTypeParams);
        p.bump();
        delimited(p, T::RParen, "`)`", "a parameter type", ty);
        p.finish_node();
        p.bump();
        ty(p);
        p.finish_node();
        return;
    }
    let start = p.checkpoint();
    atom(p);
    if p.at(T::Pipe) {
        p.start_at(start, S::UnionType);
        while p.eat(T::Pipe) {
            atom(p);
        }
        p.finish_node();
    }
}

pub(crate) fn atom(p: &mut Parser) {
    match p.current() {
        T::Ident => {
            p.start(S::NamedType);
            p.bump();
            if p.at(T::LBracket) {
                type_args(p);
            }
            p.finish_node();
        }
        T::Underscore => {
            p.start(S::InferType);
            p.bump();
            p.finish_node();
        }
        T::LParen if p.nth(1) == T::RParen => {
            p.start(S::UnitType);
            p.bump();
            p.bump();
            p.finish_node();
        }
        T::LParen => {
            let field = (p.nth(1) == T::Ident || p.nth(1).is_keyword()) && p.nth(2) == T::Colon;
            if field || p.nth(1) == T::DotDot {
                record(p);
            } else {
                p.start(S::ParenType);
                p.bump();
                ty(p);
                // A function type's markers: `((Int) -> Int is Pure)`.
                if p.at(T::Is) {
                    is_clause(p);
                }
                p.expect(T::RParen, "`)`");
                p.finish_node();
            }
        }
        _ if p.at_set(NOT_A_TYPE) => p.error("expected a type"),
        _ => p.bump_error("expected a type"),
    }
}

/// `(name: T, ..Parent, ..)` (§3.4, §3.8.1).
fn record(p: &mut Parser) {
    p.start(S::RecordType);
    p.bump();
    delimited(p, T::RParen, "`)`", "a field", |p| {
        if p.at(T::DotDot) && matches!(p.nth(1), T::RParen | T::Comma) {
            p.start(S::OpenRow);
            p.bump();
        } else if p.at(T::DotDot) {
            p.start(S::SpreadType);
            p.bump();
            ty(p);
        } else {
            p.start(S::TypeField);
            p.bump();
            p.expect(T::Colon, "`:`");
            ty(p);
        }
        p.finish_node();
    });
    p.finish_node();
}

/// `[T, …]`, where an argument may also be an integer (`Fixed[2]`) or, last,
/// an `is` clause (§11.4).
pub(crate) fn type_args(p: &mut Parser) {
    p.start(S::TypeArgs);
    p.bump();
    delimited(p, T::RBracket, "`]`", "a type argument", |p| {
        match p.current() {
            T::Int => {
                p.start(S::Literal);
                p.bump();
                p.finish_node();
            }
            T::Is => is_clause(p),
            _ => ty(p),
        }
    });
    p.finish_node();
}
