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

//! What the language server answers, from the compiler's queries on a
//! snapshot (Implementation Plan §11.8.1). Each request maps its position
//! to a token of the syntax tree, then to the HIR node there through the
//! body's source map, and asks name resolution or inference about it.

use std::ops::Range;

use crag_db::Db;
use crag_hir::{
    Expr, ItemId, ItemKind, LoweredBody, ModuleId, Owner, Program, Resolution, Stmt, TypeRef,
    TypeTarget, item_tree, lower_body, module_scope, owners, parse,
};
use crag_syntax::{LeafKind, SyntaxKind, SyntaxNode, SyntaxToken, TokenKind, TriviaKind};
use crag_types::{Callee, Ty, TyKind, body_types};

/// A module's place for the protocol.
#[derive(Clone, Debug)]
pub struct FileEntry {
    pub module: ModuleId,
    pub uri: String,
    /// Whether edits may change it: not a bundled `std` module.
    pub editable: bool,
}

/// The modules the server knows, for a request.
#[derive(Clone, Debug, Default)]
pub struct Files {
    pub entries: Vec<FileEntry>,
    pub package: Option<String>,
}

impl Files {
    pub fn uri(&self, module: ModuleId) -> Option<&FileEntry> {
        self.entries.iter().find(|e| e.module == module)
    }
}

/// What a name at a position stands for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Target<'db> {
    Item(ItemId<'db>),
    /// A local binding of a body, by its index.
    Local(Owner<'db>, u32),
}

/// A range in a module.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Place {
    pub module: ModuleId,
    pub range: Range<u32>,
}

fn root(db: &dyn Db, module: ModuleId) -> SyntaxNode {
    SyntaxNode::new_root(parse(db, *module.file(db)).green.clone())
}

fn text(db: &dyn Db, module: ModuleId) -> &str {
    module.file(db).text(db)
}

fn is_name(token: &SyntaxToken) -> bool {
    token.kind() == LeafKind::Token(TokenKind::Ident)
}

/// The name token at `offset`, or the one ending there, as when the
/// cursor stands right after a name.
pub fn name_at(db: &dyn Db, module: ModuleId, offset: u32) -> Option<SyntaxToken> {
    let root = root(db, module);
    let at = root.token_at(offset).filter(is_name);
    at.or_else(|| {
        offset
            .checked_sub(1)
            .and_then(|o| root.token_at(o))
            .filter(is_name)
    })
}

/// The index of an owner's declaration among the module's declarations.
fn owner_decl(db: &dyn Db, owner: Owner<'_>) -> Option<u32> {
    let tree = item_tree(db, owner.module(db));
    match owner {
        Owner::Item(id) => tree.items.iter().find(|i| i.id == id).map(|i| i.decl),
        Owner::Test(id) => tree.tests.iter().find(|t| t.id == id).map(|t| t.decl),
    }
}

/// The declaration of an item: its index among the module's declarations.
fn item_decl(db: &dyn Db, item: ItemId<'_>) -> Option<u32> {
    let tree = item_tree(db, *item.module(db));
    if let Some(i) = tree.items.iter().find(|i| i.id == item) {
        return Some(i.decl);
    }
    if let Some(slot) = tree.slots.iter().find(|s| s.id == item) {
        return tree
            .items
            .iter()
            .find(|i| i.id == slot.form)
            .map(|i| i.decl);
    }
    tree.imports.iter().find_map(|import| match import {
        crag_hir::Import::C {
            functions, decl, ..
        } => functions.iter().any(|f| f.id == item).then_some(*decl),
        _ => None,
    })
}

/// The body whose declaration holds `offset`.
pub fn owner_at<'db>(db: &'db dyn Db, module: ModuleId, offset: u32) -> Option<Owner<'db>> {
    let decls: Vec<SyntaxNode> = root(db, module).children().collect();
    owners(db, module).into_iter().find(|&owner| {
        owner_decl(db, owner)
            .and_then(|d| decls.get(d as usize))
            .is_some_and(|n| n.range().start <= offset && offset <= n.range().end)
    })
}

fn contains(range: &Range<u32>, inner: &Range<u32>) -> bool {
    range.start <= inner.start && inner.end <= range.end
}

/// The item a call's callee resolves to, by inference.
fn callee_item<'db>(callee: Option<&Callee<'db>>) -> Option<ItemId<'db>> {
    match callee? {
        Callee::Function(item) => Some(*item),
        Callee::Instance(instance) => Some(instance.function),
        _ => None,
    }
}

/// The call whose callee is `expr`, if any.
fn call_of(lowered: &LoweredBody<'_>, expr: usize) -> Option<usize> {
    lowered
        .body
        .exprs
        .iter()
        .position(|e| matches!(e, Expr::Call { callee, .. } if callee.index() == expr))
}

/// The item a name expression stands for: through the call it is the
/// callee of, among overloads.
fn name_item<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
    lowered: &LoweredBody<'db>,
    expr: usize,
    resolution: &Resolution<'db>,
) -> Option<ItemId<'db>> {
    match resolution {
        Resolution::Type(item) | Resolution::Form(item) => Some(*item),
        Resolution::Value { value, functions } => {
            if functions.len() > 1
                && let Some(call) = call_of(lowered, expr)
            {
                let types = body_types(db, program, owner);
                if let Some(item) = callee_item(types.callee(crag_hir::ExprId(call as u32))) {
                    return Some(item);
                }
            }
            value.or_else(|| functions.first().copied())
        }
    }
}

/// What the name token at `offset` stands for.
pub fn target_at<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
    offset: u32,
) -> Option<(Target<'db>, Range<u32>)> {
    let token = name_at(db, module, offset)?;
    let range = token.range();
    let owner = owner_at(db, module, range.start)?;
    let lowered = lower_body(db, program, owner);
    let map = &lowered.source_map;
    if contains(&map.name, &range)
        && let Owner::Item(item) = owner
    {
        return Some((Target::Item(item), range));
    }
    if let Some(b) = map
        .bindings
        .iter()
        .position(|r| contains(r, &range) && r.len() <= range.len() + 1)
    {
        return Some((Target::Local(owner, b as u32), range));
    }
    // The innermost expression or type around the name.
    let mut best: Option<(u32, Target<'db>)> = None;
    let mut consider = |len: u32, target: Option<Target<'db>>| {
        if let Some(target) = target
            && best.is_none_or(|(l, _)| len < l)
        {
            best = Some((len, target));
        }
    };
    let types = body_types(db, program, owner);
    let name_text = token.text();
    for (i, r) in map.exprs.iter().enumerate() {
        if !contains(r, &range) {
            continue;
        }
        let target = match &lowered.body.exprs[i] {
            Expr::Name { local: Some(b), .. } => Some(Target::Local(owner, b.0)),
            Expr::Name {
                item: Some(resolution),
                ..
            } => name_item(db, program, owner, lowered, i, resolution).map(Target::Item),
            Expr::MethodCall {
                name, functions, ..
            }
            | Expr::Field {
                name, functions, ..
            }
            | Expr::TypedCall {
                name, functions, ..
            } if name.text(db) == name_text => {
                let callee = callee_item(types.callee(crag_hir::ExprId(i as u32)));
                callee
                    .or_else(|| functions.first().copied())
                    .map(Target::Item)
            }
            _ => None,
        };
        consider(r.len() as u32, target);
    }
    for (i, r) in map.types.iter().enumerate() {
        if contains(r, &range)
            && let TypeRef::Named {
                target: TypeTarget::Item(item),
                ..
            } = &lowered.body.types[i]
        {
            consider(r.len() as u32, Some(Target::Item(*item)));
        }
    }
    best.map(|(_, t)| (t, range))
}

/// The name of an item's declaration.
pub fn definition<'db>(db: &'db dyn Db, program: Program, target: Target<'db>) -> Option<Place> {
    match target {
        Target::Local(owner, binding) => {
            let lowered = lower_body(db, program, owner);
            let range = lowered.source_map.bindings.get(binding as usize)?.clone();
            Some(Place {
                module: owner.module(db),
                range,
            })
        }
        Target::Item(item) => {
            let module = *item.module(db);
            let decl = item_decl(db, item)?;
            let node = root(db, module).children().nth(decl as usize)?;
            let name = item.name(db).text(db);
            let token = node
                .descendant_tokens()
                .find(|t| is_name(t) && t.text() == name)?;
            Some(Place {
                module,
                range: token.range(),
            })
        }
    }
}

/// Every use of a target, with its declaration first when `declaration`.
pub fn references<'db>(
    db: &'db dyn Db,
    program: Program,
    files: &Files,
    target: Target<'db>,
    declaration: bool,
) -> Vec<Place> {
    let mut out = Vec::new();
    if declaration && let Some(place) = definition(db, program, target) {
        out.push(place);
    }
    let owners_to_scan: Vec<Owner<'db>> = match target {
        Target::Local(owner, _) => vec![owner],
        Target::Item(_) => files
            .entries
            .iter()
            .flat_map(|e| owners(db, e.module))
            .collect(),
    };
    for owner in owners_to_scan {
        let module = owner.module(db);
        let lowered = lower_body(db, program, owner);
        let map = &lowered.source_map;
        let mut found = |range: Range<u32>| {
            let place = Place { module, range };
            if !out.contains(&place) {
                out.push(place);
            }
        };
        match target {
            Target::Local(_, binding) => {
                for (i, e) in lowered.body.exprs.iter().enumerate() {
                    match e {
                        Expr::Name { local: Some(b), .. } if b.0 == binding => {
                            found(map.exprs[i].clone());
                        }
                        Expr::Block { stmts, .. } => {
                            for stmt in stmts {
                                if let Stmt::Assign { binding: b, value } = stmt
                                    && b.0 == binding
                                    && let Some(range) =
                                        assigned_name(db, module, map.exprs[value.index()].start)
                                {
                                    found(range);
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            Target::Item(item) => {
                let name = item.name(db).text(db).clone();
                let types = body_types(db, program, owner);
                for (i, e) in lowered.body.exprs.iter().enumerate() {
                    let range = &map.exprs[i];
                    match e {
                        Expr::Name {
                            item: Some(resolution),
                            local: None,
                            ..
                        } if name_item(db, program, owner, lowered, i, resolution)
                            == Some(item) =>
                        {
                            found(range.clone());
                        }
                        Expr::MethodCall {
                            receiver,
                            name: n,
                            functions,
                            ..
                        }
                        | Expr::Field {
                            receiver,
                            name: n,
                            functions,
                            ..
                        } if n.text(db) == &name => {
                            let callee = callee_item(types.callee(crag_hir::ExprId(i as u32)));
                            let hit = callee == Some(item)
                                || (callee.is_none() && functions.as_slice() == [item]);
                            if hit
                                && let Some(at) = name_after(
                                    db,
                                    module,
                                    map.exprs[receiver.index()].end,
                                    range,
                                    &name,
                                )
                            {
                                found(at);
                            }
                        }
                        _ => {}
                    }
                }
                for (i, t) in lowered.body.types.iter().enumerate() {
                    if let TypeRef::Named {
                        target: TypeTarget::Item(target),
                        ..
                    } = t
                        && *target == item
                    {
                        let start = map.types[i].start;
                        found(start..start + name.len() as u32);
                    }
                }
            }
        }
    }
    out
}

/// The name an assignment assigns, from the start of its value: the name
/// before the `=` before it.
fn assigned_name(db: &dyn Db, module: ModuleId, value: u32) -> Option<Range<u32>> {
    let root = root(db, module);
    let tokens: Vec<SyntaxToken> = root
        .descendant_tokens()
        .filter(|t| !t.is_trivia() && t.range().end <= value)
        .collect();
    let [.., name, equals] = tokens.as_slice() else {
        return None;
    };
    (equals.kind() == LeafKind::Token(TokenKind::Equals) && is_name(name)).then(|| name.range())
}

/// The first name token `name` after `after` within `within`: the method
/// of a method call after its receiver.
fn name_after(
    db: &dyn Db,
    module: ModuleId,
    after: u32,
    within: &Range<u32>,
    name: &str,
) -> Option<Range<u32>> {
    root(db, module)
        .descendant_tokens()
        .find(|t| {
            is_name(t)
                && t.text() == name
                && t.range().start >= after
                && t.range().end <= within.end
        })
        .map(|t| t.range())
}

/// Whether a name may be a new name: an identifier that is no keyword.
pub fn valid_name(name: &str) -> bool {
    let mut chars = name.chars();
    let first = chars.next().is_some_and(|c| c.is_alphabetic() || c == '_');
    first
        && chars.all(|c| c.is_alphanumeric() || c == '_')
        && name != "_"
        && TokenKind::keyword(name).is_none()
}

/// The declaration's text without its body, on one line: a signature.
fn signature_text(db: &dyn Db, item: ItemId<'_>) -> Option<String> {
    let module = *item.module(db);
    let decl = item_decl(db, item)?;
    let node = root(db, module).children().nth(decl as usize)?;
    let end = node
        .children()
        .find(|c| c.kind() == SyntaxKind::Block)
        .map_or(node.range().end, |b| b.range().start);
    let text = &text(db, module)[node.range().start as usize..end as usize];
    let mut out = String::new();
    for word in text.split_whitespace() {
        if !out.is_empty() {
            out.push(' ');
        }
        out.push_str(word);
    }
    Some(out)
}

/// The comment lines right above a declaration: its documentation.
fn documentation(db: &dyn Db, item: ItemId<'_>) -> Option<String> {
    let module = *item.module(db);
    let decl = item_decl(db, item)?;
    let root = root(db, module);
    let node = root.children().nth(decl as usize)?;
    let mut lines = Vec::new();
    let mut newlines = 0;
    let before: Vec<SyntaxToken> = root
        .descendant_tokens()
        .take_while(|t| t.range().end <= node.range().start)
        .collect();
    for token in before.iter().rev() {
        match token.kind() {
            LeafKind::Trivia(TriviaKind::LineComment) => {
                if newlines > 1 {
                    break;
                }
                lines.push(token.text().trim_start_matches('/').trim().to_string());
                newlines = 0;
            }
            LeafKind::Trivia(TriviaKind::Newline) | LeafKind::Token(TokenKind::Newline) => {
                newlines += 1;
            }
            LeafKind::Trivia(TriviaKind::Whitespace) => {}
            _ => break,
        }
    }
    lines.reverse();
    (!lines.is_empty()).then(|| lines.join("\n"))
}

/// Hover text: the type of what is under the cursor, or an item's
/// signature and documentation, as Markdown.
pub fn hover(
    db: &dyn Db,
    program: Program,
    module: ModuleId,
    offset: u32,
) -> Option<(String, Range<u32>)> {
    if let Some((target, range)) = target_at(db, program, module, offset) {
        match target {
            Target::Item(item) => {
                let mut out = format!("```crag\n{}\n```", signature_text(db, item)?);
                if let Some(doc) = documentation(db, item) {
                    out += &format!("\n\n{doc}");
                }
                return Some((out, range));
            }
            Target::Local(owner, binding) => {
                let types = body_types(db, program, owner);
                let ty = types.binding(crag_hir::BindingId(binding))?;
                let name = name_at(db, module, offset)?;
                return Some((
                    format!("```crag\n{}: {}\n```", name.text(), ty.display(db)),
                    range,
                ));
            }
        }
    }
    // Any other expression: its type.
    let owner = owner_at(db, module, offset)?;
    let lowered = lower_body(db, program, owner);
    let types = body_types(db, program, owner);
    let (i, range) = lowered
        .source_map
        .exprs
        .iter()
        .enumerate()
        .filter(|(_, r)| r.start <= offset && offset < r.end)
        .min_by_key(|(_, r)| r.len())?;
    let ty = types.expr(crag_hir::ExprId(i as u32))?;
    Some((format!("```crag\n{}\n```", ty.display(db)), range.clone()))
}

/// A completion: its label, the protocol's kind, and a detail.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Completion {
    pub label: String,
    pub kind: u32,
    pub detail: String,
}

mod kind {
    pub const FUNCTION: u32 = 3;
    pub const FIELD: u32 = 5;
    pub const VARIABLE: u32 = 6;
    pub const INTERFACE: u32 = 8;
    pub const VALUE: u32 = 12;
    pub const STRUCT: u32 = 22;
}

/// Whether a function whose first parameter has type `param` can be called
/// on a value of type `receiver` with `.` (§6.3): roughly, since generic
/// parameters accept by their shape.
fn accepts<'db>(db: &'db dyn Db, program: Program, param: Ty<'db>, receiver: Ty<'db>) -> bool {
    match (param.kind(db), receiver.kind(db)) {
        (TyKind::Param(..), _) => true,
        (TyKind::Builtin(a, _), TyKind::Builtin(b, _)) if a == b => true,
        (TyKind::Named(a, _), TyKind::Named(b, _)) if a == b => true,
        _ => crag_types::is_subtype(db, program, receiver, param),
    }
}

/// Completions at `offset`: after `.` the fields of the value before it and
/// the functions callable on it, else the names in scope.
pub fn completion(db: &dyn Db, program: Program, module: ModuleId, offset: u32) -> Vec<Completion> {
    let source = text(db, module);
    let mut start = (offset as usize).min(source.len());
    while start > 0 && !source.is_char_boundary(start) {
        start -= 1;
    }
    let word_start = source[..start]
        .char_indices()
        .rev()
        .take_while(|(_, c)| c.is_alphanumeric() || *c == '_')
        .last()
        .map_or(start, |(i, _)| i);
    let dot = source[..word_start].ends_with('.') && !source[..word_start].ends_with("..");
    let scope = module_scope(db, program, module);
    let mut out = Vec::new();
    let owner = owner_at(db, module, word_start as u32);
    if dot {
        let dot_at = word_start as u32 - 1;
        let receiver = owner.and_then(|owner| {
            let lowered = lower_body(db, program, owner);
            let types = body_types(db, program, owner);
            lowered
                .source_map
                .exprs
                .iter()
                .enumerate()
                .filter(|(_, r)| r.end == dot_at)
                .max_by_key(|(_, r)| r.len())
                .and_then(|(i, _)| {
                    // An unfinished `p.` is no expression inference visits;
                    // a name in it still has its binding's type.
                    types
                        .expr(crag_hir::ExprId(i as u32))
                        .or(match &lowered.body.exprs[i] {
                            Expr::Name { local: Some(b), .. } => types.binding(*b),
                            _ => None,
                        })
                })
        });
        if let Some(ty) = receiver
            && let Some(fields) = crag_types::fields_of(db, program, ty)
        {
            for (name, ty) in fields {
                out.push(Completion {
                    label: name.text(db).clone(),
                    kind: kind::FIELD,
                    detail: ty.display(db),
                });
            }
        }
        for resolution in scope.names.values() {
            let Resolution::Value { functions, .. } = resolution else {
                continue;
            };
            for &function in functions {
                let sig = crag_types::signature(db, program, function);
                let Some(first) = sig.params.first() else {
                    continue;
                };
                if receiver.is_none_or(|ty| accepts(db, program, first.ty, ty)) {
                    out.push(Completion {
                        label: function.name(db).text(db).clone(),
                        kind: kind::FUNCTION,
                        detail: signature_text(db, function).unwrap_or_default(),
                    });
                }
            }
        }
    } else {
        if let Some(owner) = owner {
            let lowered = lower_body(db, program, owner);
            for (i, binding) in lowered.body.bindings.iter().enumerate() {
                let declared = lowered
                    .source_map
                    .bindings
                    .get(i)
                    .is_some_and(|r| r.end <= word_start as u32);
                if let (Some(name), true) = (binding.name, declared) {
                    out.push(Completion {
                        label: name.text(db).clone(),
                        kind: kind::VARIABLE,
                        detail: String::new(),
                    });
                }
            }
        }
        for (name, resolution) in &scope.names {
            let (kind, item) = match resolution {
                Resolution::Type(item) => (kind::STRUCT, Some(*item)),
                Resolution::Form(item) => (kind::INTERFACE, Some(*item)),
                Resolution::Value { value: Some(v), .. } => (kind::VALUE, Some(*v)),
                Resolution::Value { functions, .. } => (kind::FUNCTION, functions.first().copied()),
            };
            out.push(Completion {
                label: name.text(db).clone(),
                kind,
                detail: item.and_then(|i| signature_text(db, i)).unwrap_or_default(),
            });
        }
    }
    out.sort_by(|a, b| a.label.cmp(&b.label).then(a.detail.cmp(&b.detail)));
    out.dedup_by(|a, b| a.label == b.label && a.kind == b.kind && a.detail == b.detail);
    out
}

/// A declaration of a module, for the outline.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    pub kind: u32,
    pub range: Range<u32>,
    pub selection: Range<u32>,
}

/// The module's declarations: types, forms, functions, values and tests.
pub fn symbols(db: &dyn Db, program: Program, module: ModuleId) -> Vec<Symbol> {
    let decls: Vec<SyntaxNode> = root(db, module).children().collect();
    let tree = item_tree(db, module);
    let mut out = Vec::new();
    for item in &tree.items {
        let Some(node) = decls.get(item.decl as usize) else {
            continue;
        };
        let kind = match item.id.kind(db) {
            ItemKind::Type => 23,
            ItemKind::Form => 11,
            ItemKind::Function => 12,
            ItemKind::Value | ItemKind::Embed => 14,
            ItemKind::Slot => continue,
        };
        let selection =
            definition(db, program, Target::Item(item.id)).map_or(node.range(), |p| p.range);
        out.push(Symbol {
            name: item.id.name(db).text(db).clone(),
            kind,
            range: node.range(),
            selection,
        });
    }
    for test in &tree.tests {
        if let Some(node) = decls.get(test.decl as usize) {
            out.push(Symbol {
                name: format!("test {}", test.id.label(db)),
                kind: 24,
                range: node.range(),
                selection: node.range(),
            });
        }
    }
    out.sort_by_key(|s| s.range.start);
    out
}
