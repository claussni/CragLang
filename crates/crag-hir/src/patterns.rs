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

//! The names a pattern binds (§6.9).

use crag_syntax::{LeafKind, SyntaxKind as S, SyntaxNode, SyntaxToken, TokenKind as T};

/// A name a pattern may bind.
pub(crate) struct Binding {
    pub token: SyntaxToken,
    /// A bare name, which is a type if a type of that name is visible, and
    /// a new binding otherwise.
    pub maybe_type: bool,
}

impl Binding {
    pub fn name(&self) -> &str {
        self.token.text()
    }
}

/// The names `pattern` may bind, in source order. At the top of a `case`
/// arm (`arm`), a bare name is always a type or tag and binds nothing. The
/// alternatives of an or-pattern bind the same names, so each name is
/// listed once for all of them; anywhere else a name listed twice is bound
/// twice.
pub(crate) fn bindings(pattern: &SyntaxNode, arm: bool, out: &mut Vec<Binding>) {
    let mut bind = |token, maybe_type| out.push(Binding { token, maybe_type });
    match pattern.kind() {
        S::NamePat if !arm => idents(pattern).take(1).for_each(|t| bind(t, true)),
        S::BindPat => {
            idents(pattern).take(1).for_each(|t| bind(t, false));
            for child in pattern.children() {
                bindings(&child, arm, out);
            }
        }
        S::RestPat => idents(pattern).for_each(|t| bind(t, false)),
        // `name:` alone binds the field's name.
        S::PatField => match pattern.children().next() {
            None => idents(pattern).take(1).for_each(|t| bind(t, false)),
            Some(child) => bindings(&child, false, out),
        },
        // The name in front of a record pattern is its type.
        S::RecordPat | S::ListPat => {
            for child in pattern.children() {
                bindings(&child, false, out);
            }
        }
        S::OrPat => {
            let mut all: Vec<Binding> = Vec::new();
            for alternative in pattern.children() {
                let mut names = Vec::new();
                bindings(&alternative, arm, &mut names);
                let new: Vec<Binding> = names
                    .into_iter()
                    .filter(|b| all.iter().all(|a| a.name() != b.name()))
                    .collect();
                all.extend(new);
            }
            out.extend(all);
        }
        _ => {}
    }
}

fn idents(node: &SyntaxNode) -> impl Iterator<Item = SyntaxToken> + use<> {
    node.tokens()
        .filter(|t| t.kind() == LeafKind::Token(T::Ident))
}
