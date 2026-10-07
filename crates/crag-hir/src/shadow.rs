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

//! The no-shadowing rule (Implementation Plan §11.4.5): a binding may not
//! take a name already in scope, whether a binding of an enclosing scope, a
//! module-level value, or a visible type or form (§5.4, §6.9). Functions
//! are not bindings, so a binding may share a name with them.
//!
//! The check walks the syntax of the bodies. A binding is in scope from
//! its declaration to the end of its block, a local function from its own
//! declaration on, so it can call itself (§5.6.4).

use std::ops::Range;

use crag_db::Db;
use crag_syntax::{LeafKind, SyntaxKind as S, SyntaxNode, SyntaxToken, TokenKind as T};

use crate::input::{ModuleId, Program, parse};
use crate::items::{ItemId, Name};
use crate::patterns;
use crate::scope::{ModuleScope, Resolution, module_scope};

/// A binding that takes a name already in scope.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Redeclaration<'db> {
    pub name: String,
    pub range: Range<u32>,
    pub previous: Previous<'db>,
}

/// What first had the name.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Previous<'db> {
    /// A binding of the same body, at this range of the file.
    Local(Range<u32>),
    /// A module-level value, a type or a form.
    Item(ItemId<'db>),
}

#[crag_db::tracked(returns(ref))]
pub fn check_shadowing<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<Redeclaration<'db>> {
    let root = SyntaxNode::new_root(parse(db, *module.file(db)).green.clone());
    let mut walker = Walker {
        db,
        scope: module_scope(db, program, module),
        locals: Vec::new(),
        errors: Vec::new(),
    };
    for decl in root.children() {
        match decl.kind() {
            S::FnDecl => walker.function(&decl),
            // The names of a module-level `let` are items, which the
            // module's scope checks.
            S::LetDecl => decl.children().skip(1).for_each(|n| walker.node(&n)),
            S::Import | S::CImport => {}
            _ => walker.children(&decl),
        }
    }
    walker.errors
}

struct Walker<'a, 'db> {
    db: &'db dyn Db,
    scope: &'a ModuleScope<'db>,
    /// The bindings of the enclosing scopes, innermost last.
    locals: Vec<Vec<(String, Range<u32>)>>,
    errors: Vec<Redeclaration<'db>>,
}

impl<'db> Walker<'_, 'db> {
    fn node(&mut self, node: &SyntaxNode) {
        match node.kind() {
            S::Block => self.scoped(|w| w.children(node)),
            S::FnDecl => {
                if let Some(name) = ident(node) {
                    self.bind(&name);
                }
                self.function(node);
            }
            S::Closure => self.scoped(|w| {
                for child in node.children() {
                    if child.kind() != S::ClosureParams {
                        w.node(&child);
                        continue;
                    }
                    for param in child.children() {
                        if let Some(pattern) = param.children().next() {
                            w.pattern(&pattern, false);
                        }
                    }
                }
            }),
            // The value and the `else` block come before the names.
            S::LetDecl => {
                let mut children = node.children();
                let pattern = children.next();
                children.for_each(|n| self.node(&n));
                if let Some(pattern) = pattern {
                    self.pattern(&pattern, false);
                }
            }
            S::VarDecl | S::RefDecl => {
                self.children(node);
                if let Some(name) = ident(node) {
                    self.bind(&name);
                }
            }
            S::ForStmt => {
                let mut children = node.children();
                let pattern = children.next();
                let rest: Vec<SyntaxNode> = children.collect();
                for child in rest.iter().filter(|n| n.kind() != S::Block) {
                    self.node(child);
                }
                self.scoped(|w| {
                    if let Some(pattern) = &pattern {
                        w.pattern(pattern, false);
                    }
                    for child in rest.iter().filter(|n| n.kind() == S::Block) {
                        w.node(child);
                    }
                });
            }
            S::CaseArm => self.scoped(|w| {
                let mut children = node.children();
                if let Some(pattern) = children.next() {
                    w.pattern(&pattern, true);
                }
                children.for_each(|n| w.node(&n));
            }),
            _ => self.children(node),
        }
    }

    fn children(&mut self, node: &SyntaxNode) {
        for child in node.children() {
            self.node(&child);
        }
    }

    /// A function's parameters and body, in a scope of their own. Default
    /// values may use the parameters before them.
    fn function(&mut self, node: &SyntaxNode) {
        self.scoped(|w| {
            for child in node.children() {
                if child.kind() != S::ParamList {
                    w.node(&child);
                    continue;
                }
                for param in child.children() {
                    w.children(&param);
                    if let Some(name) = ident(&param) {
                        w.bind(&name);
                    }
                }
            }
        });
    }

    fn pattern(&mut self, pattern: &SyntaxNode, arm: bool) {
        let mut bindings = Vec::new();
        patterns::bindings(pattern, arm, &mut bindings);
        for binding in bindings {
            if !(binding.maybe_type && self.scope.is_type(self.name(binding.name()))) {
                self.bind(&binding.token);
            }
        }
    }

    fn bind(&mut self, token: &SyntaxToken) {
        let name = token.text();
        if let Some(previous) = self.previous(name) {
            self.errors.push(Redeclaration {
                name: name.to_string(),
                range: token.range(),
                previous,
            });
        }
        if let Some(scope) = self.locals.last_mut() {
            scope.push((name.to_string(), token.range()));
        }
    }

    fn previous(&self, name: &str) -> Option<Previous<'db>> {
        let local = self.locals.iter().rev().flat_map(|s| s.iter().rev());
        if let Some((_, range)) = local.into_iter().find(|(n, _)| n == name) {
            return Some(Previous::Local(range.clone()));
        }
        match self.scope.resolve(self.name(name))? {
            Resolution::Type(id)
            | Resolution::Form(id)
            | Resolution::Value {
                value: Some(id), ..
            } => Some(Previous::Item(*id)),
            Resolution::Value { value: None, .. } => None,
        }
    }

    fn scoped(&mut self, walk: impl FnOnce(&mut Self)) {
        self.locals.push(Vec::new());
        walk(self);
        self.locals.pop();
    }

    fn name(&self, text: &str) -> Name<'db> {
        Name::new(self.db, text.to_string())
    }
}

/// The first identifier among the direct children of `node`.
fn ident(node: &SyntaxNode) -> Option<SyntaxToken> {
    node.tokens()
        .find(|t| t.kind() == LeafKind::Token(T::Ident))
}
