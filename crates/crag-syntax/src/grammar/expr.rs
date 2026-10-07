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

//! Expressions (Specification Appendix D.4, precedence §6.2.1).
//!
//! Binary operators are parsed by binding power, the Pratt loop of
//! `expr_bp`. Each level has a left and a right power; a left-associative
//! level binds tighter on its right. `==` and the other comparisons, `is`
//! and `..` do not chain: a second one on the same level is reported and
//! parsed as if it chained to the left.

use super::{delimited, is_clause, pattern, statements, ty};
use crate::kind::SyntaxKind as S;
use crate::parser::{Parser, TokenSet};
use crate::token::TokenKind as T;

/// Tokens a missing expression leaves alone, since an enclosing rule needs
/// them.
const NOT_AN_EXPRESSION: TokenSet = TokenSet::new(&[
    T::Newline,
    T::RBrace,
    T::RParen,
    T::RBracket,
    T::Eof,
    T::Comma,
    T::Semicolon,
    T::StrMid,
    T::StrEnd,
]);

const EXPRESSION_START: TokenSet = TokenSet::new(&[
    T::Ident,
    T::Underscore,
    T::Int,
    T::Float,
    T::Str,
    T::StrStart,
    T::TripleStrStart,
    T::Bytes,
    T::CodePoint,
    T::Hole,
    T::LParen,
    T::LBracket,
    T::LBrace,
    T::If,
    T::Case,
    T::Atomic,
    T::Lazy,
    T::Not,
    T::Minus,
    T::Symbol,
    T::Pass,
]);

/// Whether the token `n` ahead can begin an expression.
pub(crate) fn at_expr_start(p: &Parser, n: usize) -> bool {
    EXPRESSION_START.contains(p.nth(n))
}

/// Where an expression stands, for the one place syntax depends on it.
#[derive(Clone, Copy, Default)]
struct Context {
    /// The subject of `case`: a `{` after it opens the arms, never a
    /// trailing closure.
    no_trailing_closure: bool,
}

/// The level of `not`, between comparison and `and`: `not x == y` is
/// `not (x == y)`.
const NOT_POWER: u8 = 5;

/// The left and right binding power of a binary operator.
fn binding_power(kind: T) -> Option<(u8, u8)> {
    Some(match kind {
        T::Or => (1, 2),
        T::And => (3, 4),
        T::EqEq | T::BangEq | T::Lt | T::LtEq | T::Gt | T::GtEq | T::Is => (7, 8),
        T::DotDot => (9, 10),
        T::Plus | T::Minus | T::PlusPercent | T::MinusPercent => (11, 12),
        T::Star | T::Slash | T::Percent | T::StarPercent => (13, 14),
        _ => return None,
    })
}

pub(crate) fn expr(p: &mut Parser) {
    expr_bp(p, 0, Context::default());
}

fn expr_bp(p: &mut Parser, min_power: u8, cx: Context) {
    if !p.enter() {
        return;
    }
    let start = p.checkpoint();
    match p.current() {
        T::Not => {
            p.start(S::PrefixExpr);
            p.bump();
            expr_bp(p, NOT_POWER, cx);
            p.finish_node();
        }
        T::Lazy => {
            // `lazy` takes the whole expression to its right (§6.10).
            p.start(S::LazyExpr);
            p.bump();
            expr_bp(p, 0, cx);
            p.finish_node();
            return;
        }
        _ => unary(p, cx),
    }
    // The left power of the last operator that does not chain.
    let mut unchained = None;
    loop {
        let op = p.current();
        let Some((left, right)) = binding_power(op) else {
            return;
        };
        if left < min_power {
            return;
        }
        if unchained == Some(left) {
            p.error(match op {
                T::DotDot => "ranges cannot be chained",
                _ => "comparisons cannot be chained; use `and`",
            });
        }
        match op {
            T::Is => {
                p.start_at(start, S::IsExpr);
                p.bump();
                ty(p);
            }
            T::DotDot => {
                p.start_at(start, S::RangeExpr);
                p.bump();
                // `a..` is an open range (§7.4).
                if at_expr_start(p, 0) {
                    expr_bp(p, right, cx);
                }
            }
            _ => {
                p.start_at(start, S::BinExpr);
                p.bump();
                expr_bp(p, right, cx);
            }
        }
        p.finish_node();
        if matches!(left, 7 | 9) {
            unchained = Some(left);
        }
    }
}

/// Prefixes and unary `-`, which apply to the whole postfix expression
/// after them (§8.5).
fn unary(p: &mut Parser, cx: Context) {
    if !p.enter() {
        return;
    }
    match p.current() {
        T::Minus => {
            p.start(S::PrefixExpr);
            p.bump();
            unary(p, cx);
            p.finish_node();
        }
        T::Symbol => {
            p.start(S::PrefixExpr);
            p.bump();
            while p.at(T::Symbol) && p.nth_is_joined(0) {
                p.bump();
            }
            unary(p, cx);
            p.finish_node();
        }
        _ => postfix(p, cx),
    }
}

fn postfix(p: &mut Parser, cx: Context) {
    let start = p.checkpoint();
    if !primary(p) {
        return;
    }
    loop {
        match p.current() {
            T::LParen => {
                p.start_at(start, S::CallExpr);
                args(p, T::LParen);
                if !cx.no_trailing_closure && closure_ahead(p) {
                    closure(p);
                }
            }
            T::LBrace if !cx.no_trailing_closure && closure_ahead(p) => {
                p.start_at(start, S::CallExpr);
                closure(p);
            }
            T::LBracket => {
                p.start_at(start, S::BracketExpr);
                args(p, T::LBracket);
            }
            T::Dot | T::QuestionDot => {
                p.start_at(start, S::FieldExpr);
                p.bump();
                p.expect(T::Ident, "a field name");
            }
            _ => return,
        }
        p.finish_node();
    }
}

/// Whether the `{` at the current token opens a closure: `{ ->` or
/// `{ params ->` (D.4). Any other `{` opens a block.
pub(crate) fn closure_ahead(p: &Parser) -> bool {
    if !p.at(T::LBrace) {
        return false;
    }
    let mut n = 1;
    loop {
        match p.nth(n) {
            T::Arrow => return true,
            T::LParen | T::LBracket => n = p.skip_balanced(n),
            T::RBrace | T::LBrace | T::Newline | T::Equals | T::Eof => return false,
            _ => n += 1,
        }
    }
}

/// A primary expression; false if there was none.
fn primary(p: &mut Parser) -> bool {
    match p.current() {
        T::Int | T::Float | T::Str | T::Bytes | T::CodePoint | T::Hole => {
            p.start(S::Literal);
            p.bump();
            p.finish_node();
        }
        T::StrStart | T::TripleStrStart => interpolated_string(p),
        T::Ident => {
            p.start(S::NameRef);
            p.bump();
            p.finish_node();
        }
        T::Underscore => {
            p.start(S::Placeholder);
            p.bump();
            p.finish_node();
        }
        T::Pass => {
            p.start(S::PassExpr);
            p.bump();
            p.finish_node();
        }
        T::LParen => paren_or_record(p),
        T::LBracket => list_map_or_grid(p),
        T::LBrace if closure_ahead(p) => closure(p),
        T::LBrace => block(p),
        T::If => if_expr(p),
        T::Case => case_expr(p),
        T::Atomic => {
            p.start(S::AtomicExpr);
            p.bump();
            if p.at(T::LBrace) {
                block(p);
            } else {
                p.error("expected a block");
            }
            p.finish_node();
        }
        // After a unary `-` or a prefix.
        T::Not | T::Lazy => expr_bp(p, NOT_POWER, Context::default()),
        _ => {
            if p.at_set(NOT_AN_EXPRESSION) {
                p.error("expected an expression");
            } else {
                p.bump_error("expected an expression");
            }
            return false;
        }
    }
    true
}

/// A string literal where the grammar asks for one (`test`, `embed`, C
/// libraries); interpolation is accepted and left to later checks.
pub(crate) fn string_literal(p: &mut Parser) {
    match p.current() {
        T::Str => {
            p.start(S::Literal);
            p.bump();
            p.finish_node();
        }
        T::StrStart | T::TripleStrStart => interpolated_string(p),
        _ => p.error("expected a string"),
    }
}

fn interpolated_string(p: &mut Parser) {
    p.start(S::StrExpr);
    p.bump();
    loop {
        expr(p);
        if p.eat(T::StrMid) {
            continue;
        }
        p.expect(T::StrEnd, "the end of the interpolation");
        break;
    }
    p.finish_node();
}

/// An argument list in parentheses or brackets, with its delimiters.
fn args(p: &mut Parser, open: T) -> (usize, bool, bool) {
    p.start(S::ArgList);
    p.bump();
    let mut labeled = false;
    let (count, trailing_comma) = if open == T::LParen {
        delimited(p, T::RParen, "`)`", "an argument", |p| labeled |= arg(p))
    } else {
        delimited(p, T::RBracket, "`]`", "an argument", |p| {
            labeled |= bracket_arg(p)
        })
    };
    p.finish_node();
    (count, labeled, trailing_comma)
}

/// `expr`, `label: expr` or `..expr`; true if labeled or spread.
fn arg(p: &mut Parser) -> bool {
    if p.at(T::DotDot) {
        p.start(S::SpreadArg);
        p.bump();
        expr(p);
        p.finish_node();
        true
    } else if label_ahead(p) {
        p.start(S::LabeledArg);
        p.start(S::Label);
        p.bump();
        while p.at(T::Dot) {
            p.bump();
            p.bump();
        }
        p.finish_node();
        p.bump();
        expr(p);
        p.finish_node();
        true
    } else {
        expr(p);
        false
    }
}

/// Whether a label follows: `name ("." name)* ":"`. A keyword can be a
/// label (§2.5).
fn label_ahead(p: &Parser) -> bool {
    let name = |kind: T| kind == T::Ident || kind.is_keyword();
    if !name(p.current()) {
        return false;
    }
    let mut n = 1;
    while p.nth(n) == T::Dot && p.nth(n + 1) == T::Ident {
        n += 2;
    }
    p.nth(n) == T::Colon
}

/// An argument of bracket application, which may be a type or an
/// expression (§6.5). Function types, unions and `is` clauses are parsed
/// as types; anything else as an expression, which name resolution
/// reinterprets where it names a type.
fn bracket_arg(p: &mut Parser) -> bool {
    if p.at(T::Is) {
        is_clause(p);
        return false;
    }
    if p.at(T::LParen) && p.nth(p.skip_balanced(0)) == T::Arrow {
        ty(p);
        return false;
    }
    let start = p.checkpoint();
    let labeled = arg(p);
    if p.at(T::Pipe) {
        p.start_at(start, S::UnionType);
        while p.eat(T::Pipe) {
            ty::atom(p);
        }
        p.finish_node();
    }
    labeled
}

/// `( )` is the unit record, `(expr)` a parenthesized expression, anything
/// else a record.
fn paren_or_record(p: &mut Parser) {
    let start = p.checkpoint();
    let (count, labeled, trailing_comma) = args(p, T::LParen);
    let kind = if count == 1 && !labeled && !trailing_comma {
        S::ParenExpr
    } else {
        S::RecordExpr
    };
    p.start_at(start, kind);
    p.finish_node();
}

/// `[…]`: a list, a map (`[k: v]`, `[:]`) or a grid (`[a, b; c, d]`).
fn list_map_or_grid(p: &mut Parser) {
    let start = p.checkpoint();
    p.bump();
    let mut kind = S::ListExpr;
    p.nested(|p| kind = list_map_or_grid_body(p));
    if !p.eat(T::RBracket) {
        p.recover("expected `]`", TokenSet::new(&[]));
        p.eat(T::RBracket);
    }
    p.start_at(start, kind);
    p.finish_node();
}

/// The elements after the `[`, and the kind they make.
fn list_map_or_grid_body(p: &mut Parser) -> S {
    if p.at(T::RBracket) {
        S::ListExpr
    } else if p.at(T::Colon) && p.nth(1) == T::RBracket {
        p.bump();
        S::MapExpr
    } else {
        let first = p.checkpoint();
        expr(p);
        if p.at(T::Colon) {
            map_entry_rest(p, first);
            while p.eat(T::Comma) {
                if p.at(T::RBracket) {
                    break;
                }
                let entry = p.checkpoint();
                expr(p);
                map_entry_rest(p, entry);
            }
            S::MapExpr
        } else {
            let mut row = first;
            let mut grid = false;
            loop {
                if p.eat(T::Comma) {
                    if p.at(T::RBracket) {
                        break;
                    }
                } else if p.at(T::Semicolon) {
                    p.start_at(row, S::GridRow);
                    p.finish_node();
                    p.bump();
                    row = p.checkpoint();
                    grid = true;
                } else {
                    break;
                }
                expr(p);
            }
            if grid {
                p.start_at(row, S::GridRow);
                p.finish_node();
                S::GridExpr
            } else {
                S::ListExpr
            }
        }
    }
}

/// The `: value` of a map entry whose key starts at `key`.
fn map_entry_rest(p: &mut Parser, key: crate::green::Checkpoint) {
    p.start_at(key, S::MapEntry);
    if p.expect(T::Colon, "`:`") {
        expr(p);
    }
    p.finish_node();
}

pub(crate) fn block(p: &mut Parser) {
    if !p.enter() {
        return;
    }
    p.start(S::Block);
    p.bump();
    statements(p);
    p.expect(T::RBrace, "`}`");
    p.finish_node();
}

/// `{ params -> statements }`
fn closure(p: &mut Parser) {
    p.start(S::Closure);
    p.bump();
    if !p.at(T::Arrow) {
        p.start(S::ClosureParams);
        loop {
            p.start(S::ClosureParam);
            pattern(p, false);
            if p.eat(T::Colon) {
                ty(p);
            }
            p.finish_node();
            if !p.eat(T::Comma) {
                break;
            }
        }
        p.finish_node();
    }
    p.expect(T::Arrow, "`->`");
    statements(p);
    p.expect(T::RBrace, "`}`");
    p.finish_node();
}

fn if_expr(p: &mut Parser) {
    p.start(S::IfExpr);
    p.bump();
    expr(p);
    if p.at(T::LBrace) {
        block(p);
    } else {
        p.error("expected a block");
    }
    if p.eat(T::Else) {
        match p.current() {
            T::If => if_expr(p),
            T::LBrace => block(p),
            _ => p.error("expected `if` or a block"),
        }
    }
    p.finish_node();
}

fn case_expr(p: &mut Parser) {
    p.start(S::CaseExpr);
    p.bump();
    expr_bp(
        p,
        0,
        Context {
            no_trailing_closure: true,
        },
    );
    if p.expect(T::LBrace, "`{`") {
        loop {
            p.eat_newlines();
            if p.at(T::RBrace) || p.at(T::Eof) {
                break;
            }
            let before = p.position();
            arm(p);
            if p.position() == before {
                p.bump_error("expected a case arm");
            } else if !p.at(T::Newline) && !p.at(T::RBrace) {
                p.recover("expected a newline or `}`", TokenSet::new(&[]));
            }
        }
        p.expect(T::RBrace, "`}`");
    }
    p.finish_node();
}

/// `pattern (where guard)? -> body`, or `pass` alone (§7.2).
fn arm(p: &mut Parser) {
    p.start(S::CaseArm);
    if p.at(T::Pass) && matches!(p.nth(1), T::Newline | T::RBrace) {
        p.start(S::PassExpr);
        p.bump();
        p.finish_node();
    } else {
        pattern(p, true);
        if p.at(T::Where) {
            p.start(S::ArmGuard);
            p.bump();
            expr(p);
            p.finish_node();
        }
        p.expect(T::Arrow, "`->`");
        expr(p);
    }
    p.finish_node();
}
