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

//! The grammar of Specification Appendix D, one function per rule:
//! declarations and statements here, expressions, patterns and types in
//! the submodules.

mod expr;
mod pattern;
mod ty;

pub(crate) use expr::{block, expr};
pub(crate) use pattern::pattern;
pub(crate) use ty::ty;

use crate::kind::SyntaxKind as S;
use crate::parser::{Parser, TokenSet};
use crate::token::TokenKind as T;

const CLOSERS: TokenSet = TokenSet::new(&[T::RParen, T::RBracket, T::RBrace, T::Eof]);

/// A module: declarations, one per line (D.2).
pub(crate) fn module(p: &mut Parser) {
    loop {
        p.eat_newlines();
        if p.at(T::Eof) {
            return;
        }
        let before = p.position();
        declaration(p);
        if p.position() == before {
            p.bump_error("expected a declaration");
            continue;
        }
        if !p.at(T::Newline) && !p.at(T::Eof) {
            p.recover(
                "expected a newline after the declaration",
                TokenSet::new(&[]),
            );
        }
    }
}

fn declaration(p: &mut Parser) {
    let mut n = 0;
    while matches!(p.nth(n), T::Pub | T::Opaque | T::Distinct) {
        n += 1;
    }
    match p.nth(n) {
        T::Type => type_decl(p),
        T::Form => form_decl(p),
        T::Fn => fn_decl(p),
        T::Import if n == 0 => import(p),
        T::Let if n == 0 => let_decl(p),
        T::Embed if n == 0 => embed_decl(p),
        T::Test if n == 0 => test_decl(p),
        _ => p.recover("expected a declaration", TokenSet::new(&[])),
    }
}

fn modifiers(p: &mut Parser) {
    while matches!(p.current(), T::Pub | T::Opaque | T::Distinct) {
        p.bump();
    }
}

/// Parses a comma-separated list up to `close`, which it consumes. Returns
/// the number of elements and whether a comma followed the last one.
/// Newlines between elements are skipped, for lists in braces.
pub(crate) fn delimited(
    p: &mut Parser,
    close: T,
    closer: &str,
    what: &str,
    mut element: impl FnMut(&mut Parser),
) -> (usize, bool) {
    let mut count = 0;
    let mut trailing_comma = false;
    loop {
        p.eat_newlines();
        if p.at(close) || p.at_set(CLOSERS) {
            break;
        }
        let before = p.position();
        element(p);
        if p.position() == before && !p.at(T::Comma) {
            p.bump_error(format!("expected {what}"));
        }
        count += 1;
        p.eat_newlines();
        trailing_comma = p.eat(T::Comma);
        if trailing_comma || p.at(close) || p.at_set(CLOSERS) {
            continue;
        }
        p.recover(
            format!("expected `,` or {closer}"),
            TokenSet::new(&[T::Comma]),
        );
        trailing_comma = p.eat(T::Comma);
        if !trailing_comma {
            // The error is reported; a missing closer would only repeat it.
            p.eat(close);
            return (count, false);
        }
    }
    p.expect(close, closer);
    (count, trailing_comma)
}

/// `name ("." name)*`
fn path(p: &mut Parser) {
    p.start(S::Path);
    p.expect(T::Ident, "a module name");
    while p.at(T::Dot) && p.nth(1) == T::Ident {
        p.bump();
        p.bump();
    }
    p.finish_node();
}

fn import(p: &mut Parser) {
    if p.nth(1) == T::Ident && p.nth_text(1) == "cLib" && p.nth(2) == T::LParen {
        return c_import(p);
    }
    p.start(S::Import);
    p.bump();
    path(p);
    if p.eat(T::As) {
        p.expect(T::Ident, "a name");
    } else if p.at(T::Dot) && p.nth(1) == T::LBrace {
        p.bump();
        p.start(S::ImportItems);
        p.bump();
        delimited(p, T::RBrace, "`}`", "an import", |p| {
            p.start(S::ImportItem);
            p.expect(T::Ident, "a name");
            if p.eat(T::As) {
                p.expect(T::Ident, "a name");
            }
            p.finish_node();
        });
        p.finish_node();
    }
    p.finish_node();
}

/// `import cLib("…").{ sig, … } is …` (§16.4)
fn c_import(p: &mut Parser) {
    p.start(S::CImport);
    p.bump();
    p.bump();
    p.bump();
    expr::string_literal(p);
    p.expect(T::RParen, "`)`");
    p.expect(T::Dot, "`.`");
    if p.expect(T::LBrace, "`{`") {
        delimited(p, T::RBrace, "`}`", "a C function", |p| {
            p.start(S::CSig);
            p.expect(T::Ident, "a function name");
            param_list(p);
            p.expect(T::Arrow, "`->`");
            ty(p);
            if p.at(T::Is) {
                is_clause(p);
            }
            p.finish_node();
        });
    }
    if p.at(T::Is) {
        is_clause(p);
    }
    p.finish_node();
}

fn type_decl(p: &mut Parser) {
    p.start(S::TypeDecl);
    modifiers(p);
    p.bump();
    p.expect(T::Ident, "a type name");
    if p.at(T::LBracket) {
        type_params(p);
    }
    if p.at(T::LParen) {
        p.start(S::FieldList);
        p.bump();
        delimited(p, T::RParen, "`)`", "a field", |p| {
            if p.at(T::DotDot) {
                p.start(S::Spread);
                p.bump();
                ty(p);
            } else {
                p.start(S::Field);
                p.expect(T::Ident, "a field name");
                p.expect(T::Colon, "`:`");
                ty(p);
                if p.eat(T::Equals) {
                    expr(p);
                }
            }
            p.finish_node();
        });
        p.finish_node();
    } else if p.eat(T::Equals) {
        ty(p);
    }
    clauses(p);
    p.finish_node();
}

/// `where`, `is` and `on` clauses, each on the declaration's line or a
/// following one.
fn clauses(p: &mut Parser) {
    loop {
        let (kind, _) = p.nth_past_newlines(0);
        match kind {
            T::Where => {
                p.eat_newlines();
                where_clause(p);
            }
            T::Is => {
                p.eat_newlines();
                is_clause(p);
            }
            T::On => {
                p.eat_newlines();
                p.start(S::OnClause);
                p.bump();
                ty(p);
                expr(p);
                p.finish_node();
            }
            _ => return,
        }
    }
}

fn type_params(p: &mut Parser) {
    p.start(S::TypeParams);
    p.bump();
    delimited(p, T::RBracket, "`]`", "a type parameter", |p| {
        p.start(S::TypeParam);
        p.expect(T::Ident, "a type parameter");
        if p.eat(T::Colon) {
            ty(p);
        }
        p.finish_node();
    });
    p.finish_node();
}

/// `where expr, …` or `where { item … }` (§3.10).
fn where_clause(p: &mut Parser) {
    p.start(S::WhereClause);
    p.bump();
    if p.eat(T::LBrace) {
        items(p, expr);
        p.expect(T::RBrace, "`}`");
    } else {
        expr(p);
        while p.eat(T::Comma) {
            expr(p);
        }
    }
    p.finish_node();
}

/// Items in braces, separated by commas or newlines, up to the `}`.
fn items(p: &mut Parser, item: fn(&mut Parser)) {
    loop {
        p.eat_newlines();
        if p.at_set(CLOSERS) {
            return;
        }
        let before = p.position();
        item(p);
        if p.position() == before {
            p.bump_error("expected an item");
        } else if !p.eat(T::Comma) && !p.at(T::Newline) && !p.at_set(CLOSERS) {
            p.recover("expected `,` or a newline", TokenSet::new(&[T::Comma]));
            p.eat(T::Comma);
        }
    }
}

/// `is Marker` or `is { Marker, … }` (§3.11).
pub(crate) fn is_clause(p: &mut Parser) {
    p.start(S::IsClause);
    p.bump();
    if p.eat(T::LBrace) {
        items(p, marker);
        p.expect(T::RBrace, "`}`");
    } else {
        marker(p);
    }
    p.finish_node();
}

fn marker(p: &mut Parser) {
    p.start(S::Marker);
    p.eat(T::Not);
    ty(p);
    p.finish_node();
}

fn form_decl(p: &mut Parser) {
    p.start(S::FormDecl);
    modifiers(p);
    p.bump();
    p.expect(T::Ident, "a form name");
    if p.at(T::LBracket) {
        type_params(p);
    }
    if p.eat(T::Equals) {
        ty(p);
    } else {
        if p.at(T::Where) {
            where_clause(p);
        }
        if p.expect(T::LBrace, "`{` or `=`") {
            items(p, form_fn);
            p.expect(T::RBrace, "`}`");
        }
    }
    p.finish_node();
}

fn form_fn(p: &mut Parser) {
    p.start(S::FormFn);
    p.expect(T::Ident, "a function name");
    if p.at(T::LBracket) {
        type_params(p);
    }
    param_list(p);
    p.expect(T::Arrow, "`->`");
    ty(p);
    p.finish_node();
}

pub(crate) fn fn_decl(p: &mut Parser) {
    p.start(S::FnDecl);
    modifiers(p);
    p.bump();
    p.expect(T::Ident, "a function name");
    if p.at(T::LBracket) {
        type_params(p);
    }
    param_list(p);
    if p.at(T::Arrow) {
        p.start(S::ReturnType);
        p.bump();
        ty(p);
        p.finish_node();
    }
    if p.nth_past_newlines(0).0 == T::Where {
        p.eat_newlines();
        where_clause(p);
    }
    if p.at_word("prefix") && matches!(p.nth(1), T::Str) {
        p.start(S::PrefixClause);
        p.bump();
        p.bump();
        p.finish_node();
    }
    if p.at(T::LBrace) {
        block(p);
    }
    p.finish_node();
}

fn param_list(p: &mut Parser) {
    p.start(S::ParamList);
    if p.expect(T::LParen, "`(`") {
        delimited(p, T::RParen, "`)`", "a parameter", |p| {
            p.start(S::Param);
            p.expect(T::Ident, "a parameter name");
            p.expect(T::Colon, "`:`");
            ty(p);
            if p.eat(T::Equals) {
                expr(p);
            }
            p.finish_node();
        });
    }
    p.finish_node();
}

pub(crate) fn let_decl(p: &mut Parser) {
    p.start(S::LetDecl);
    p.bump();
    pattern(p, false);
    if p.eat(T::Colon) {
        ty(p);
    }
    p.expect(T::Equals, "`=`");
    expr(p);
    if p.at(T::Else) {
        p.start(S::LetElse);
        p.bump();
        if p.at(T::LBrace) {
            expr(p);
        } else {
            p.error("expected a block or a closure");
        }
        p.finish_node();
    }
    p.finish_node();
}

/// `var`, `ref` and `ext` bindings.
fn binding(p: &mut Parser, kind: S) {
    p.start(kind);
    p.bump();
    p.expect(T::Ident, "a name");
    if p.eat(T::Colon) {
        ty(p);
    }
    p.expect(T::Equals, "`=`");
    expr(p);
    p.finish_node();
}

fn embed_decl(p: &mut Parser) {
    p.start(S::EmbedDecl);
    p.bump();
    p.expect(T::Ident, "a name");
    if p.eat(T::Colon) {
        ty(p);
    }
    if p.at_word("from") {
        p.bump();
    } else {
        p.error("expected `from`");
    }
    expr::string_literal(p);
    p.finish_node();
}

fn test_decl(p: &mut Parser) {
    p.start(S::TestDecl);
    p.bump();
    expr::string_literal(p);
    if p.at(T::LBrace) {
        block(p);
    } else {
        p.error("expected the test's block");
    }
    p.finish_node();
}

/// Statements up to the closing `}`, which is left to the caller (D.3).
pub(crate) fn statements(p: &mut Parser) {
    loop {
        p.eat_newlines();
        if p.at_set(CLOSERS) {
            return;
        }
        let before = p.position();
        statement(p);
        if p.position() == before {
            p.bump_error("expected a statement");
        } else if !p.at(T::Newline) && !p.at_set(CLOSERS) {
            p.recover("expected a newline or `}`", TokenSet::new(&[]));
        }
    }
}

fn statement(p: &mut Parser) {
    match p.current() {
        T::Let => let_decl(p),
        T::Var => binding(p, S::VarDecl),
        T::Ref | T::Ext => binding(p, S::RefDecl),
        T::Fn => fn_decl(p),
        T::For => {
            p.start(S::ForStmt);
            p.bump();
            pattern(p, false);
            p.expect(T::In, "`in`");
            expr(p);
            if p.at(T::LBrace) {
                block(p);
            } else {
                p.error("expected the loop's block");
            }
            p.finish_node();
        }
        T::Emit => {
            p.start(S::EmitStmt);
            p.bump();
            let qualified = p.at(T::Ident) && matches!(p.nth_text(0), "ok" | "fail" | "retry");
            if qualified && expr::at_expr_start(p, 1) {
                p.bump();
            }
            expr(p);
            p.finish_node();
        }
        T::Return => {
            p.start(S::ReturnStmt);
            p.bump();
            if expr::at_expr_start(p, 0) {
                expr(p);
            }
            p.finish_node();
        }
        T::On => {
            p.start(S::OnStmt);
            p.bump();
            ty(p);
            expr(p);
            p.finish_node();
        }
        T::Ident if p.nth(1) == T::Equals => {
            p.start(S::Assign);
            p.bump();
            p.bump();
            expr(p);
            p.finish_node();
        }
        _ => expr(p),
    }
}
