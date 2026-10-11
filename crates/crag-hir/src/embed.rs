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

//! The resources of `embed` declarations (Implementation Plan §11.6.10,
//! Specification §18.4.1).
//!
//! An `embed`'s source is a string literal, so parsing alone finds every
//! resource: the driver reads the sources of a program's modules and gives
//! the database what it read as inputs, which it reads again when they
//! change. Compile-time code never reads a file.

use std::ops::Range;
use std::sync::Arc;

use crag_db::Db;
use crag_syntax::{LeafKind, SyntaxKind as S, SyntaxNode, TokenKind as T};

use crate::input::{ModuleId, Program};
use crate::items::{ItemId, ItemKind, item_tree};
use crate::literal;

/// The source an `embed` declaration names, as its string literal gives
/// it, and the literal's range; or why the literal gives none. None when
/// the declaration has no literal, which parsing reported.
pub(crate) fn source_of(node: &SyntaxNode) -> Option<(Result<String, String>, Range<u32>)> {
    let literal = node
        .children()
        .find(|n| matches!(n.kind(), S::Literal | S::StrExpr))?;
    let range = literal.range();
    let token = literal.tokens().find(|t| !t.is_trivia());
    let source = match token {
        Some(t) if literal.kind() == S::Literal && t.kind() == LeafKind::Token(T::Str) => {
            literal::string(&[t.text()]).map(|pieces| {
                pieces
                    .into_iter()
                    .filter_map(|p| match p {
                        literal::Piece::Text(t) => Some(t),
                        literal::Piece::Hole(_) => None,
                    })
                    .collect()
            })
        }
        _ => Err("the source of an `embed` is a string literal, never computed".into()),
    };
    Some((source, range))
}

/// The sources the `embed` declarations of a module name, as written, in
/// source order. Those whose literal gives none are left out.
pub fn embed_sources(db: &dyn Db, module: ModuleId) -> Vec<String> {
    item_tree(db, module)
        .items
        .iter()
        .filter(|i| *i.id.kind(db) == ItemKind::Embed)
        .filter_map(|i| source_of(&SyntaxNode::new_root(i.signature.clone())))
        .filter_map(|(source, _)| source.ok())
        .collect()
}

/// The content of the resource an `embed` names, as the driver read it,
/// or why there is none.
pub fn embed_content<'db>(
    db: &'db dyn Db,
    program: Program,
    item: ItemId<'db>,
) -> Result<&'db Arc<[u8]>, String> {
    let module = *item.module(db);
    let signature = item_tree(db, module)
        .items
        .iter()
        .find(|i| i.id == item)
        .map(|i| i.signature.clone())
        .ok_or("no such `embed`")?;
    let (source, _) = source_of(&SyntaxNode::new_root(signature)).ok_or("no source")?;
    let source = source?;
    content(db, program, module, &source)
}

/// What the driver read for a source of a module.
pub(crate) fn content<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
    source: &str,
) -> Result<&'db Arc<[u8]>, String> {
    let resource = program
        .resources(db)
        .iter()
        .find(|(m, s, _)| *m == module && s == source)
        .map(|r| r.2)
        .ok_or_else(|| format!("`{source}` was not read"))?;
    resource.content(db).as_ref().map_err(Clone::clone)
}
