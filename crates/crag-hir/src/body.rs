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

//! The body queries (Implementation Plan §11.4.6).
//!
//! `lower_body` reads a body from the syntax tree, with its source map and
//! errors; it reruns on every edit of the file. `hir_body` is the body
//! alone, which holds no positions, so it stays equal, and stops
//! recomputation of what reads it, when an edit leaves the body as it was.

use crag_db::Db;
use crag_syntax::{LeafKind, SyntaxKind as S, SyntaxNode, TokenKind as T};

use crate::hir::Body;
use crate::input::{ModuleId, Program, parse};
use crate::items::{ItemId, ItemKind, TestId, item_tree};
use crate::literal;
use crate::lower::{BodySourceMap, LowerError, Lowerer, let_parts};
use crate::scope::{Resolution, module_scope};

/// What has a body: a function, a module-level `let` (through any of the
/// values it binds), a test, or a type or form declaration, whose types,
/// and a type's defaults, are lowered like one.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Owner<'db> {
    Item(ItemId<'db>),
    Test(TestId<'db>),
}

impl<'db> Owner<'db> {
    pub fn module(self, db: &'db dyn Db) -> ModuleId {
        match self {
            Owner::Item(id) => *id.module(db),
            Owner::Test(id) => *id.module(db),
        }
    }
}

/// The owners of a module's bodies in source order, each `let` once.
pub fn owners<'db>(db: &'db dyn Db, module: ModuleId) -> Vec<Owner<'db>> {
    let tree = item_tree(db, module);
    let mut owners: Vec<(u32, Owner)> = Vec::new();
    for item in &tree.items {
        let kind = *item.id.kind(db);
        let first_of_let = kind == ItemKind::Value && owners.iter().all(|(d, _)| *d != item.decl);
        if matches!(kind, ItemKind::Function | ItemKind::Type | ItemKind::Form) || first_of_let {
            owners.push((item.decl, Owner::Item(item.id)));
        }
    }
    owners.extend(tree.tests.iter().map(|t| (t.decl, Owner::Test(t.id))));
    owners.sort_by_key(|&(decl, _)| decl);
    owners.into_iter().map(|(_, owner)| owner).collect()
}

/// A body with where its nodes come from and what went wrong lowering it.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct LoweredBody<'db> {
    pub body: Body<'db>,
    pub source_map: BodySourceMap,
    pub errors: Vec<LowerError<'db>>,
}

#[crag_db::tracked(returns(ref))]
pub fn lower_body<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> LoweredBody<'db> {
    let module = owner.module(db);
    let tree = item_tree(db, module);
    let root = SyntaxNode::new_root(parse(db, *module.file(db)).green.clone());
    let decl = match owner {
        Owner::Item(id) => tree.items.iter().find(|i| i.id == id).map(|i| i.decl),
        Owner::Test(id) => tree.tests.iter().find(|t| t.id == id).map(|t| t.decl),
    };
    let Some(node) = decl.and_then(|d| root.children().nth(d as usize)) else {
        return LoweredBody::default();
    };
    let scope = module_scope(db, program, module);
    let prefixes = prefixes(db, program, module);
    let mut lower = Lowerer::new(db, program, scope, prefixes);
    if let Some(name) = crate::lower::ident(&node) {
        lower.map.name = name.range();
    }
    match node.kind() {
        S::FnDecl => {
            let (params, result, root) = lower.function(&node);
            lower.body.params = params;
            lower.body.result = result;
            lower.body.root = root;
        }
        S::LetDecl => {
            let parts = let_parts(&node);
            lower.body.root = parts.value.map(|v| lower.boundary(&v));
            let ty = parts.ty.map(|t| lower.type_node(&t));
            if let Some(pattern) = parts.pattern {
                lower.body.pattern = Some((lower.module_pattern(&pattern), ty));
            }
        }
        S::TypeDecl => {
            lower.body.type_decl = Some(lower.type_decl(&node));
        }
        S::FormDecl => {
            lower.body.form = Some(lower.form_decl(&node));
        }
        S::TestDecl => {
            lower.body.root = node
                .children()
                .find(|n| n.kind() == S::Block)
                .map(|b| lower.expr(&b));
        }
        _ => {}
    }
    LoweredBody {
        body: lower.body,
        source_map: lower.map,
        errors: lower.errors,
    }
}

/// A body without positions: the firewall in front of inference.
#[crag_db::tracked(returns(ref))]
pub fn hir_body<'db>(db: &'db dyn Db, program: Program, owner: Owner<'db>) -> Body<'db> {
    lower_body(db, program, owner).body.clone()
}

/// The prefixes declared by the functions in a module's scope (§8.5),
/// longest first.
#[crag_db::tracked(returns(ref))]
pub fn prefixes<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(String, ItemId<'db>)> {
    let mut prefixes = Vec::new();
    for resolution in module_scope(db, program, module).names.values() {
        let Resolution::Value { functions, .. } = resolution else {
            continue;
        };
        for &id in functions {
            let tree = item_tree(db, *id.module(db));
            let Some(item) = tree.items.iter().find(|i| i.id == id) else {
                continue;
            };
            let signature = SyntaxNode::new_root(item.signature.clone());
            let Some(clause) = signature.children().find(|n| n.kind() == S::PrefixClause) else {
                continue;
            };
            let text = clause
                .tokens()
                .find(|t| t.kind() == LeafKind::Token(T::Str))
                .and_then(|t| literal::string(&[t.text()]).ok());
            if let Some([literal::Piece::Text(prefix)]) = text.as_deref() {
                prefixes.push((prefix.clone(), id));
            }
        }
    }
    prefixes.sort_by(|(a, _), (b, _)| b.len().cmp(&a.len()).then(a.cmp(b)));
    prefixes
}
