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

//! Lowering syntax to HIR (Implementation Plan §11.4.6), one case per
//! syntax kind.
//!
//! Names are resolved while lowering: against the bindings in scope, then
//! against the module's scope. A binding is in scope from its declaration
//! to the end of its block, a local function from its own declaration on
//! (§5.6.4), and a new binding may not take a name already in scope (§5.4).
//!
//! A `_` argument makes a partial application (§6.6). The smallest
//! argument around a `_` that is not the `_` itself becomes a closure, or
//! the whole statement if there is no such argument. Its supplied
//! arguments are evaluated once, before the closure is made, so they are
//! bound first, unless they are literals, closures or names that cannot
//! change.

use std::ops::Range;

use crag_db::Db;
use crag_syntax::{LeafKind, SyntaxKind as S, SyntaxNode, SyntaxToken, TokenKind as T};

use crate::body::Owner;
use crate::hir::*;
use crate::input::Program;
use crate::items::{ItemId, ItemKind, Name, form_slots};
use crate::literal::{self, Literal, Piece};
use crate::scope::{ModuleScope, Resolution};
use crate::shadow::{Previous, Redeclaration};

/// Where every node of a body comes from.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct BodySourceMap {
    pub exprs: Vec<Range<u32>>,
    pub pats: Vec<Range<u32>>,
    pub types: Vec<Range<u32>>,
    pub bindings: Vec<Range<u32>>,
    /// The name of the declaration the body belongs to.
    pub name: Range<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum LowerError<'db> {
    /// A name that is neither a binding nor an item in scope.
    Unresolved {
        name: String,
        range: Range<u32>,
    },
    /// A name where a type is expected, or at the top of a `case` arm
    /// (§6.9), that names no type.
    UnknownType {
        name: String,
        range: Range<u32>,
    },
    Redeclared(Redeclaration<'db>),
    /// An alternative of an or-pattern that does not bind a name the
    /// others bind.
    NotInEveryAlternative {
        name: String,
        range: Range<u32>,
    },
    /// A record literal element without a name.
    UnnamedField {
        range: Range<u32>,
    },
    Literal {
        message: String,
        range: Range<u32>,
    },
    /// A run of prefix symbols that no declared prefixes make up (§8.5).
    UnknownPrefix {
        text: String,
        range: Range<u32>,
    },
    /// An operator whose function is not in scope (§6.2).
    NoOperator {
        function: &'static str,
        range: Range<u32>,
    },
    /// An assignment to a binding that is not a `var` (§5.2).
    NotAVar {
        name: String,
        range: Range<u32>,
    },
    /// A `var` assigned inside a closure that captures it (§6.4.1).
    VarWrittenInClosure {
        name: String,
        range: Range<u32>,
    },
    /// A spread that is not the first entry of a field list, or a second
    /// one (§3.8).
    MisplacedSpread {
        range: Range<u32>,
    },
    /// An expression where a type is expected.
    ExpectedType {
        range: Range<u32>,
    },
    /// A type where a value is expected: in the brackets after a value.
    ExpectedValue {
        range: Range<u32>,
    },
    /// A marker other than `Pure` on a function or a function type, or a
    /// marker on another type in parentheses (§3.14).
    Marker {
        range: Range<u32>,
    },
}

pub(crate) struct Lowerer<'a, 'db> {
    pub db: &'db dyn Db,
    pub scope: &'a ModuleScope<'db>,
    /// The declared prefixes in scope, longest first.
    pub prefixes: &'a [(String, ItemId<'db>)],
    pub body: Body<'db>,
    pub map: BodySourceMap,
    pub errors: Vec<LowerError<'db>>,
    scopes: Vec<Vec<(Name<'db>, BindingId)>>,
    /// The closure depth at which each binding was declared.
    depths: Vec<u32>,
    closure_depth: u32,
    type_scopes: Vec<(Name<'db>, u32)>,
    /// The `_`s of each partial application being lowered, innermost last.
    holes: Vec<Vec<BindingId>>,
    program: Program,
    /// The functions the forms of a generic function's bounds require,
    /// which its body calls by name (§4.2).
    slots: Vec<(Name<'db>, ItemId<'db>)>,
}

/// The state of one pattern while it is lowered.
struct PatCtx<'db> {
    kind: BindingKind,
    /// Whether new bindings are checked against the names in scope. The
    /// names of a module-level `let` are items, checked by the scope.
    check: bool,
    bound: Vec<(Name<'db>, BindingId)>,
    /// Bindings from this index on may be bound again by the next
    /// alternative of an or-pattern.
    reuse_from: Option<usize>,
    /// The names bound by the alternatives being lowered.
    alternatives: Vec<Vec<Name<'db>>>,
}

impl<'a, 'db> Lowerer<'a, 'db> {
    pub fn new(
        db: &'db dyn Db,
        program: Program,
        scope: &'a ModuleScope<'db>,
        prefixes: &'a [(String, ItemId<'db>)],
    ) -> Self {
        Lowerer {
            db,
            scope,
            prefixes,
            body: Body::default(),
            map: BodySourceMap::default(),
            errors: Vec::new(),
            scopes: vec![Vec::new()],
            depths: Vec::new(),
            closure_depth: 0,
            type_scopes: Vec::new(),
            holes: Vec::new(),
            program,
            slots: Vec::new(),
        }
    }

    // Arenas.

    fn alloc_expr(&mut self, expr: Expr<'db>, range: Range<u32>) -> ExprId {
        self.body.exprs.push(expr);
        self.map.exprs.push(range);
        ExprId(self.body.exprs.len() as u32 - 1)
    }

    fn alloc_pat(&mut self, pat: Pat<'db>, range: Range<u32>) -> PatId {
        self.body.pats.push(pat);
        self.map.pats.push(range);
        PatId(self.body.pats.len() as u32 - 1)
    }

    fn alloc_type(&mut self, ty: TypeRef<'db>, range: Range<u32>) -> TypeRefId {
        self.body.types.push(ty);
        self.map.types.push(range);
        TypeRefId(self.body.types.len() as u32 - 1)
    }

    fn alloc_binding(
        &mut self,
        name: Option<Name<'db>>,
        kind: BindingKind,
        range: Range<u32>,
    ) -> BindingId {
        self.body.bindings.push(Binding { name, kind });
        self.map.bindings.push(range);
        self.depths.push(self.closure_depth);
        BindingId(self.body.bindings.len() as u32 - 1)
    }

    fn name(&self, text: &str) -> Name<'db> {
        Name::new(self.db, text.to_string())
    }

    // Scopes.

    fn scoped<R>(&mut self, lower: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push(Vec::new());
        let types = self.type_scopes.len();
        let result = lower(self);
        self.type_scopes.truncate(types);
        self.scopes.pop();
        result
    }

    /// A closure, a local function or a `lazy` block: a scope whose code
    /// runs apart from the code around it.
    fn closure_scope<R>(&mut self, lower: impl FnOnce(&mut Self) -> R) -> R {
        self.closure_depth += 1;
        let result = self.scoped(lower);
        self.closure_depth -= 1;
        result
    }

    fn local(&self, name: Name<'db>) -> Option<BindingId> {
        self.scopes
            .iter()
            .rev()
            .flat_map(|s| s.iter().rev())
            .find(|(n, _)| *n == name)
            .map(|&(_, id)| id)
    }

    fn declare(&mut self, name: Name<'db>, binding: BindingId) {
        self.scopes.last_mut().unwrap().push((name, binding));
    }

    /// What `name` already refers to, which a new binding may not take.
    fn previous(&self, name: Name<'db>) -> Option<Previous<'db>> {
        if let Some(id) = self.local(name) {
            return Some(Previous::Local(self.map.bindings[id.index()].clone()));
        }
        match self.scope.resolve(name)? {
            Resolution::Type(id)
            | Resolution::Form(id)
            | Resolution::Value {
                value: Some(id), ..
            } => Some(Previous::Item(*id)),
            Resolution::Value { value: None, .. } => None,
        }
    }

    fn check_new(&mut self, name: Name<'db>, range: &Range<u32>) {
        if let Some(previous) = self.previous(name) {
            self.errors.push(LowerError::Redeclared(Redeclaration {
                name: name.text(self.db).clone(),
                range: range.clone(),
                previous,
            }));
        }
    }

    /// A binding named by `token`, declared in the current scope.
    fn bind_token(&mut self, token: &SyntaxToken, kind: BindingKind) -> BindingId {
        let name = self.name(token.text());
        self.check_new(name, &token.range());
        let binding = self.alloc_binding(Some(name), kind, token.range());
        self.declare(name, binding);
        binding
    }

    // Functions.

    /// Type parameters, parameters, result type and block of a function.
    /// Declares the type parameters of a function or type, if it has any.
    fn type_params(&mut self, node: &SyntaxNode) {
        if let Some(params) = child(node, S::TypeParams) {
            let mut bounds = Vec::new();
            for param in params.children() {
                if let Some(token) = ident(&param) {
                    let name = self.name(token.text());
                    self.body.type_params.push(name);
                    let index = self.body.type_params.len() as u32 - 1;
                    self.type_scopes.push((name, index));
                    if let Some(bound) = param.children().next() {
                        bounds.push((index, bound));
                    }
                }
            }
            // A bound may name any of the parameters.
            for (index, bound) in bounds {
                let ty = self.type_node(&bound);
                self.body.requirements.push(Requirement {
                    param: Some(index),
                    ty,
                });
            }
        }
    }

    /// The entries of a `where` clause of requirements (§4.4).
    fn requirements(&mut self, node: &SyntaxNode) {
        if let Some(clause) = child(node, S::WhereClause) {
            for entry in clause.children() {
                let ty = self.type_node(&entry);
                self.body.requirements.push(Requirement { param: None, ty });
            }
        }
    }

    /// A form declaration: its type parameters, requirements and functions,
    /// or the forms it stands for.
    pub fn form_decl(&mut self, node: &SyntaxNode) -> FormDecl<'db> {
        self.type_params(node);
        self.requirements(node);
        let mut decl = FormDecl::default();
        for entry in node.children() {
            match entry.kind() {
                S::FormFn => {
                    let Some(token) = ident(&entry) else {
                        continue;
                    };
                    let name = self.name(token.text());
                    let generic = child(&entry, S::TypeParams).is_some();
                    let params = child(&entry, S::ParamList)
                        .into_iter()
                        .flat_map(|list| list.children().collect::<Vec<_>>())
                        .map(|param| {
                            let name = ident(&param).map(|t| self.name(t.text()));
                            let ty = self.type_or_missing(param.children().next(), &param);
                            (name, ty)
                        })
                        .collect();
                    let result = entry
                        .children()
                        .filter(|n| !matches!(n.kind(), S::TypeParams | S::ParamList))
                        .last();
                    let result = self.type_or_missing(result, &entry);
                    decl.slots.push(SlotDecl {
                        name,
                        params,
                        result,
                        generic,
                    });
                }
                S::TypeParams | S::WhereClause => {}
                _ => decl.alias = Some(self.type_node(&entry)),
            }
        }
        decl
    }

    /// The functions the forms of the requirements and parameter types
    /// require, through the requirements of those forms.
    fn slots_of_bounds(&self, params: &[Param]) -> Vec<(Name<'db>, ItemId<'db>)> {
        let db = self.db;
        let form_of = |body: &Body<'db>, ty: TypeRefId| match body.type_ref(ty) {
            TypeRef::Named {
                target: TypeTarget::Item(item),
                ..
            } if *item.kind(db) == ItemKind::Form => Some(*item),
            _ => None,
        };
        let mut forms: Vec<ItemId<'db>> = self
            .body
            .requirements
            .iter()
            .map(|r| r.ty)
            .chain(params.iter().map(|p| p.ty))
            .filter_map(|ty| form_of(&self.body, ty))
            .collect();
        let mut i = 0;
        while i < forms.len() {
            let body = crate::body::hir_body(db, self.program, Owner::Item(forms[i]));
            let alias = body.form.as_ref().and_then(|f| f.alias);
            for ty in body.requirements.iter().map(|r| r.ty).chain(alias) {
                if let Some(form) = form_of(body, ty)
                    && !forms.contains(&form)
                {
                    forms.push(form);
                }
            }
            i += 1;
        }
        let mut slots = Vec::new();
        for form in forms {
            for slot in form_slots(db, form) {
                if !slots.iter().any(|&(_, s)| s == slot) {
                    slots.push((*slot.name(db), slot));
                }
            }
        }
        slots
    }

    /// What `name` refers to in the module's scope, with the functions the
    /// bounds of a generic function require.
    fn resolve(&self, name: Name<'db>) -> Option<Resolution<'db>> {
        let slots: Vec<ItemId<'db>> = self
            .slots
            .iter()
            .filter(|(n, _)| *n == name)
            .map(|&(_, s)| s)
            .collect();
        match self.scope.resolve(name).cloned() {
            Some(Resolution::Value {
                value,
                mut functions,
            }) => {
                functions.extend(slots);
                Some(Resolution::Value { value, functions })
            }
            None if !slots.is_empty() => Some(Resolution::Value {
                value: None,
                functions: slots,
            }),
            other => other,
        }
    }

    pub fn type_decl(&mut self, node: &SyntaxNode) -> TypeDecl<'db> {
        self.type_params(node);
        let modifier = |kind| node.tokens().any(|t| t.kind() == LeafKind::Token(kind));
        let mut decl = TypeDecl {
            distinct: modifier(T::Distinct),
            opaque: modifier(T::Opaque),
            ..TypeDecl::default()
        };
        if let Some(list) = child(node, S::FieldList) {
            decl.record = true;
            for (i, entry) in list.children().enumerate() {
                let mut nodes = entry.children();
                match entry.kind() {
                    S::Spread => {
                        let ty = self.type_or_missing(nodes.next(), &entry);
                        if i > 0 || decl.parent.is_some() {
                            self.errors.push(LowerError::MisplacedSpread {
                                range: entry.range(),
                            });
                        } else {
                            decl.parent = Some(ty);
                        }
                    }
                    S::Field => {
                        let ty = self.type_or_missing(nodes.next(), &entry);
                        let default = nodes.next().map(|n| self.boundary(&n));
                        if let Some(token) = ident(&entry) {
                            let name = self.name(token.text());
                            decl.fields.push(FieldDecl { name, ty, default });
                        }
                    }
                    _ => {}
                }
            }
        } else {
            decl.alias = node
                .children()
                .find(|n| !matches!(n.kind(), S::TypeParams) && !is_clause(n.kind()))
                .map(|t| self.type_node(&t));
        }
        decl
    }

    /// Whether an `is` clause among a node's children marks it `Pure`;
    /// other markers are errors.
    pub(crate) fn pure_marker(&mut self, node: &SyntaxNode) -> bool {
        let Some(clause) = child(node, S::IsClause) else {
            return false;
        };
        let mut pure = false;
        for marker in clause.children().filter(|n| n.kind() == S::Marker) {
            let negated = marker.tokens().any(|t| t.kind() == LeafKind::Token(T::Not));
            let named = marker
                .children()
                .next()
                .filter(|t| t.kind() == S::NamedType && child(t, S::TypeArgs).is_none())
                .and_then(|t| first_token(&t))
                .is_some_and(|t| t.text() == "Pure");
            if named && !negated {
                pure = true;
            } else {
                self.errors.push(LowerError::Marker {
                    range: marker.range(),
                });
            }
        }
        pure
    }

    pub fn function(
        &mut self,
        node: &SyntaxNode,
    ) -> (Vec<Param>, Option<TypeRefId>, Option<ExprId>) {
        self.type_params(node);
        let mut params = Vec::new();
        for param in child(node, S::ParamList)
            .into_iter()
            .flat_map(|list| list.children().collect::<Vec<_>>())
        {
            let mut nodes = param.children();
            let ty = self.type_or_missing(nodes.next(), &param);
            // A default may use the parameters before it.
            let default = nodes.next().map(|n| self.boundary(&n));
            let binding = match ident(&param) {
                Some(token) => self.bind_token(&token, BindingKind::Param),
                None => self.alloc_binding(None, BindingKind::Param, param.range()),
            };
            params.push(Param {
                binding,
                ty,
                default,
            });
        }
        let result = child(node, S::ReturnType)
            .and_then(|r| r.children().next())
            .map(|t| self.type_node(&t));
        // Local functions cannot be generic yet; inference says so.
        if self.closure_depth == 0 {
            self.requirements(node);
            self.slots = self.slots_of_bounds(&params);
        }
        let body = child(node, S::Block).map(|b| self.expr(&b));
        (params, result, body)
    }

    // Statements.

    /// The statements of a block or closure body, in a scope of their own.
    fn block(&mut self, node: &SyntaxNode, statements: Vec<SyntaxNode>) -> ExprId {
        self.scoped(|this| {
            let mut stmts = Vec::new();
            let mut tail = None;
            let count = statements.len();
            for (i, statement) in statements.into_iter().enumerate() {
                if is_statement(statement.kind()) {
                    if let Some(stmt) = this.statement(&statement) {
                        stmts.push(stmt);
                    }
                } else {
                    let expr = this.boundary(&statement);
                    if i + 1 == count {
                        tail = Some(expr);
                    } else {
                        stmts.push(Stmt::Expr(expr));
                    }
                }
            }
            this.alloc_expr(Expr::Block { stmts, tail }, node.range())
        })
    }

    fn statement(&mut self, node: &SyntaxNode) -> Option<Stmt> {
        Some(match node.kind() {
            S::LetDecl => {
                let parts = let_parts(node);
                let value = self.boundary_or_missing(parts.value.as_ref(), node);
                let otherwise = parts.otherwise.map(|n| self.boundary(&n));
                let ty = parts.ty.map(|t| self.type_node(&t));
                let pat = self.pattern_or_missing(parts.pattern.as_ref(), node, BindingKind::Let);
                match otherwise {
                    Some(otherwise) => Stmt::LetElse {
                        pat,
                        ty,
                        value,
                        otherwise,
                    },
                    None => Stmt::Let { pat, ty, value },
                }
            }
            S::VarDecl | S::RefDecl => {
                let kind = match first_token(node).map(|t| t.kind()) {
                    Some(LeafKind::Token(T::Var)) => BindingKind::Var,
                    Some(LeafKind::Token(T::Ext)) => BindingKind::Ext,
                    _ => BindingKind::Ref,
                };
                let mut nodes = node.children();
                let has_type = node.tokens().any(|t| t.kind() == LeafKind::Token(T::Colon));
                let ty = if has_type {
                    nodes.next().map(|t| self.type_node(&t))
                } else {
                    None
                };
                let value = self.boundary_or_missing(nodes.next().as_ref(), node);
                let binding = match ident(node) {
                    Some(token) => self.bind_token(&token, kind),
                    None => self.alloc_binding(None, kind, node.range()),
                };
                Stmt::Bind { binding, ty, value }
            }
            S::Assign => {
                let value = self.boundary_or_missing(node.children().next().as_ref(), node);
                let token = ident(node)?;
                let name = self.name(token.text());
                let range = token.range();
                let text = token.text().to_string();
                let Some(binding) = self.local(name) else {
                    self.errors.push(match self.scope.resolve(name) {
                        Some(_) => LowerError::NotAVar { name: text, range },
                        None => LowerError::Unresolved { name: text, range },
                    });
                    return Some(Stmt::Expr(value));
                };
                if self.body.binding(binding).kind != BindingKind::Var {
                    self.errors.push(LowerError::NotAVar { name: text, range });
                } else if self.depths[binding.index()] < self.closure_depth {
                    self.errors
                        .push(LowerError::VarWrittenInClosure { name: text, range });
                }
                Stmt::Assign { binding, value }
            }
            S::ForStmt => {
                let nodes: Vec<SyntaxNode> = node.children().collect();
                let iterable = nodes.iter().skip(1).find(|n| n.kind() != S::Block).cloned();
                let iterable = self.expr_or_missing(iterable.as_ref(), node);
                let block = nodes.iter().skip(1).find(|n| n.kind() == S::Block).cloned();
                self.scoped(|this| {
                    let pat = this.pattern_or_missing(nodes.first(), node, BindingKind::Let);
                    let body = this.expr_or_missing(block.as_ref(), node);
                    Stmt::For {
                        pat,
                        iterable,
                        body,
                    }
                })
            }
            S::EmitStmt => {
                let kind = node.tokens().find_map(|t| match t.text() {
                    "ok" if t.kind() == LeafKind::Token(T::Ident) => Some(EmitKind::Ok),
                    "fail" if t.kind() == LeafKind::Token(T::Ident) => Some(EmitKind::Fail),
                    "retry" if t.kind() == LeafKind::Token(T::Ident) => Some(EmitKind::Retry),
                    _ => None,
                });
                let value = self.boundary_or_missing(node.children().next().as_ref(), node);
                Stmt::Emit { kind, value }
            }
            S::ReturnStmt => Stmt::Return(node.children().next().map(|n| self.boundary(&n))),
            S::OnStmt => {
                let mut nodes = node.children();
                let ty = self.type_or_missing(nodes.next(), node);
                let handler = self.boundary_or_missing(nodes.next().as_ref(), node);
                Stmt::On { ty, handler }
            }
            S::FnDecl => {
                let binding = match ident(node) {
                    Some(token) => self.bind_token(&token, BindingKind::Fn),
                    None => self.alloc_binding(None, BindingKind::Fn, node.range()),
                };
                let (params, result, body) = self.closure_scope(|this| this.function(node));
                let pure = self.pure_marker(node);
                Stmt::Fn {
                    binding,
                    function: LocalFn {
                        generic: child(node, S::TypeParams).is_some()
                            || child(node, S::WhereClause).is_some(),
                        params,
                        result,
                        pure,
                        body,
                    },
                }
            }
            _ => return None,
        })
    }

    // Expressions.

    /// An expression where a partial application may end: an argument or a
    /// statement.
    pub fn boundary(&mut self, node: &SyntaxNode) -> ExprId {
        self.holes.push(Vec::new());
        let expr = self.expr(node);
        let holes = self.holes.pop().unwrap();
        if holes.is_empty() {
            return expr;
        }
        let range = node.range();
        let mut supplied = Vec::new();
        self.hoist(expr, &mut supplied);
        let params = holes
            .iter()
            .map(|&binding| ClosureParam {
                pat: self.alloc_pat(Pat::Bind { binding, sub: None }, range.clone()),
                ty: None,
            })
            .collect();
        let closure = self.alloc_expr(Expr::Closure { params, body: expr }, range.clone());
        if supplied.is_empty() {
            closure
        } else {
            self.alloc_expr(
                Expr::Block {
                    stmts: supplied,
                    tail: Some(closure),
                },
                range,
            )
        }
    }

    fn boundary_or_missing(&mut self, node: Option<&SyntaxNode>, parent: &SyntaxNode) -> ExprId {
        match node {
            Some(node) => self.boundary(node),
            None => self.alloc_expr(Expr::Missing, parent.range()),
        }
    }

    fn expr_or_missing(&mut self, node: Option<&SyntaxNode>, parent: &SyntaxNode) -> ExprId {
        match node {
            Some(node) => self.expr(node),
            None => self.alloc_expr(Expr::Missing, parent.range()),
        }
    }

    /// Binds the supplied arguments of calls in a partial application,
    /// before the closure (§6.6). Returns whether `expr` contains a `_`.
    fn hoist(&mut self, expr: ExprId, supplied: &mut Vec<Stmt>) -> bool {
        let mut node = self.body.expr(expr).clone();
        let has_hole = match &mut node {
            Expr::Call {
                callee,
                args,
                fields,
            } => {
                let mut children = vec![callee];
                children.extend(args.iter_mut());
                children.extend(field_values(fields));
                self.hoist_children(children, supplied)
            }
            Expr::MethodCall {
                receiver,
                args,
                fields,
                ..
            } => {
                let mut children = vec![receiver];
                children.extend(args.iter_mut());
                children.extend(field_values(fields));
                self.hoist_children(children, supplied)
            }
            Expr::TypedCall { args, fields, .. } => {
                let mut children: Vec<&mut ExprId> = args.iter_mut().collect();
                children.extend(field_values(fields));
                self.hoist_children(children, supplied)
            }
            Expr::Field { receiver, .. } => self.hoist_children(vec![receiver], supplied),
            Expr::Index { base, args } => {
                let mut children = vec![base];
                children.extend(args.iter_mut());
                self.hoist_children(children, supplied)
            }
            _ => {
                let children = self.children(expr);
                let mut any = false;
                for child in children {
                    any |= self.hoist(child, supplied);
                }
                any || self.is_hole(expr)
            }
        };
        self.body.exprs[expr.index()] = node;
        has_hole
    }

    fn hoist_children(&mut self, children: Vec<&mut ExprId>, supplied: &mut Vec<Stmt>) -> bool {
        let mut any = false;
        for child in children {
            if self.hoist(*child, supplied) {
                any = true;
            } else if self.changes(*child) {
                let range = self.map.exprs[child.index()].clone();
                let binding = self.alloc_binding(None, BindingKind::Supplied, range.clone());
                let pat = self.alloc_pat(Pat::Bind { binding, sub: None }, range.clone());
                supplied.push(Stmt::Let {
                    pat,
                    ty: None,
                    value: *child,
                });
                let name = self.name("_");
                *child = self.alloc_expr(
                    Expr::Name {
                        name,
                        local: Some(binding),
                        item: None,
                    },
                    range,
                );
            }
        }
        any
    }

    fn is_hole(&self, expr: ExprId) -> bool {
        matches!(self.body.expr(expr), Expr::Name { local: Some(b), .. }
            if self.body.binding(*b).kind == BindingKind::Hole)
    }

    /// Whether evaluating the expression again could give another value or
    /// do something: anything but literals, closures and names of what
    /// cannot change.
    fn changes(&self, expr: ExprId) -> bool {
        match self.body.expr(expr) {
            Expr::Literal(_) | Expr::Closure { .. } | Expr::Missing => false,
            Expr::Name { local, .. } => {
                local.is_some_and(|b| self.body.binding(b).kind == BindingKind::Var)
            }
            _ => true,
        }
    }

    /// The direct subexpressions a partial application's `_` may sit in,
    /// outside calls. Blocks, closures and the branches of `if` and `case`
    /// run later or not at all, so nothing in them is supplied.
    fn children(&self, expr: ExprId) -> Vec<ExprId> {
        match self.body.expr(expr) {
            Expr::Str(parts) => parts
                .iter()
                .filter_map(|p| match p {
                    StrPart::Expr(e) => Some(*e),
                    StrPart::Text(_) => None,
                })
                .collect(),
            Expr::And(a, b) | Expr::Or(a, b) => vec![*a, *b],
            Expr::Not(a) => vec![*a],
            Expr::Range { start, end } => std::iter::once(*start).chain(*end).collect(),
            Expr::Is { expr, .. } => vec![*expr],
            Expr::TypeArgs { base, .. } => vec![*base],
            Expr::Record(fields) => fields.iter().map(field_value).collect(),
            Expr::List(items) => items.clone(),
            Expr::Map(entries) => entries.iter().flat_map(|&(k, v)| [k, v]).collect(),
            Expr::Grid(rows) => rows.iter().flatten().copied().collect(),
            _ => Vec::new(),
        }
    }

    pub fn expr(&mut self, node: &SyntaxNode) -> ExprId {
        let range = node.range();
        let expr = match node.kind() {
            S::Literal => match self.literal(node) {
                Some(Some(literal)) => Expr::Literal(literal),
                Some(None) => Expr::Hole,
                None => Expr::Missing,
            },
            S::StrExpr => self.interpolation(node),
            S::NameRef => match ident(node) {
                Some(token) => self.value_name(&token),
                None => Expr::Missing,
            },
            S::Placeholder => match self.holes.last_mut() {
                Some(_) => {
                    let binding = self.alloc_binding(None, BindingKind::Hole, range.clone());
                    self.holes.last_mut().unwrap().push(binding);
                    let name = self.name("_");
                    Expr::Name {
                        name,
                        local: Some(binding),
                        item: None,
                    }
                }
                None => Expr::Missing,
            },
            S::ParenExpr => {
                let inner = node
                    .children()
                    .next()
                    .and_then(|list| list.children().next());
                return self.expr_or_missing(inner.as_ref(), node);
            }
            S::RecordExpr => {
                let args = node.children().next();
                let (positional, fields) = self.args(args.as_ref());
                for arg in positional {
                    let range = self.map.exprs[arg.index()].clone();
                    self.errors.push(LowerError::UnnamedField { range });
                }
                Expr::Record(fields.unwrap_or_default())
            }
            S::ListExpr => Expr::List(node.children().map(|n| self.expr(&n)).collect()),
            S::MapExpr => Expr::Map(
                node.children()
                    .map(|entry| {
                        let mut nodes = entry.children();
                        let key = self.expr_or_missing(nodes.next().as_ref(), &entry);
                        let value = self.expr_or_missing(nodes.next().as_ref(), &entry);
                        (key, value)
                    })
                    .collect(),
            ),
            S::GridExpr => Expr::Grid(
                node.children()
                    .map(|row| row.children().map(|n| self.expr(&n)).collect())
                    .collect(),
            ),
            S::Block => {
                return self.block(node, node.children().collect());
            }
            S::Closure => self.closure_scope(|this| {
                let mut params = Vec::new();
                if let Some(list) = child(node, S::ClosureParams) {
                    for param in list.children() {
                        let mut nodes = param.children();
                        let pattern = nodes.next();
                        let ty = nodes.next().map(|t| this.type_node(&t));
                        let pat =
                            this.pattern_or_missing(pattern.as_ref(), &param, BindingKind::Param);
                        params.push(ClosureParam { pat, ty });
                    }
                }
                let statements = node
                    .children()
                    .filter(|n| n.kind() != S::ClosureParams)
                    .collect();
                let body = this.block(node, statements);
                Expr::Closure { params, body }
            }),
            S::IfExpr => {
                let mut nodes = node.children();
                let condition = self.expr_or_missing(nodes.next().as_ref(), node);
                let then = self.expr_or_missing(nodes.next().as_ref(), node);
                let otherwise = nodes.next().map(|n| self.expr(&n));
                Expr::If {
                    condition,
                    then,
                    otherwise,
                }
            }
            S::CaseExpr => {
                let mut nodes = node.children();
                let subject = self.expr_or_missing(nodes.next().as_ref(), node);
                let arms = nodes
                    .filter(|n| n.kind() == S::CaseArm)
                    .map(|arm| self.arm(&arm))
                    .collect();
                Expr::Case { subject, arms }
            }
            S::PassExpr => Expr::Pass,
            S::AtomicExpr => {
                let block = node.children().next();
                Expr::Atomic(self.expr_or_missing(block.as_ref(), node))
            }
            S::LazyExpr => {
                let inner = node.children().next();
                // A `lazy` runs later, like a closure (§7.1).
                let inner = self.closure_scope(|this| this.expr_or_missing(inner.as_ref(), node));
                Expr::Lazy(inner)
            }
            S::BinExpr => return self.binary(node),
            S::PrefixExpr => return self.prefix(node),
            S::RangeExpr => {
                let mut nodes = node.children();
                let start = self.expr_or_missing(nodes.next().as_ref(), node);
                let end = nodes.next().map(|n| self.expr(&n));
                Expr::Range { start, end }
            }
            S::IsExpr => {
                let mut nodes = node.children();
                let expr = self.expr_or_missing(nodes.next().as_ref(), node);
                let ty = self.type_or_missing(nodes.next(), node);
                Expr::Is { expr, ty }
            }
            S::CallExpr => self.call(node),
            S::FieldExpr => {
                let receiver = node.children().next();
                let receiver = self.expr_or_missing(receiver.as_ref(), node);
                match ident(node) {
                    Some(token) => {
                        let name = self.name(token.text());
                        Expr::Field {
                            receiver,
                            name,
                            functions: self.functions(name),
                            optional: optional(node),
                        }
                    }
                    None => Expr::Missing,
                }
            }
            S::BracketExpr => self.bracket(node),
            _ => Expr::Missing,
        };
        self.alloc_expr(expr, range)
    }

    fn arm(&mut self, node: &SyntaxNode) -> Arm {
        self.scoped(|this| {
            let nodes: Vec<SyntaxNode> = node.children().collect();
            if let [only] = nodes.as_slice()
                && only.kind() == S::PassExpr
            {
                let range = only.range();
                return Arm {
                    pat: this.alloc_pat(Pat::Wildcard, range.clone()),
                    guard: None,
                    body: this.alloc_expr(Expr::Pass, range),
                };
            }
            let pat = match nodes.first() {
                Some(pattern) => {
                    let mut cx = PatCtx::new(BindingKind::Let, true);
                    let pat = this.pattern(pattern, true, &mut cx);
                    this.declare_all(&cx);
                    pat
                }
                None => this.alloc_pat(Pat::Missing, node.range()),
            };
            let guard = nodes
                .iter()
                .find(|n| n.kind() == S::ArmGuard)
                .map(|g| this.expr_or_missing(g.children().next().as_ref(), g));
            let body = nodes
                .iter()
                .skip(1)
                .rfind(|n| n.kind() != S::ArmGuard)
                .cloned();
            let body = this.boundary_or_missing(body.as_ref(), node);
            Arm { pat, guard, body }
        })
    }

    /// A literal's value; `Some(None)` for `???`, `None` when it was
    /// reported.
    fn literal(&mut self, node: &SyntaxNode) -> Option<Option<Literal>> {
        let token = first_token(node)?;
        let LeafKind::Token(kind) = token.kind() else {
            return None;
        };
        self.literal_token(kind, &token)
            .map(Some)
            .or_else(|| (kind == T::Hole).then_some(None))
    }

    fn literal_token(&mut self, kind: T, token: &SyntaxToken) -> Option<Literal> {
        let text = token.text();
        let value = match kind {
            T::Int => literal::int(text).map(Literal::Int),
            T::Float => literal::float(text).map(Literal::Float),
            T::Str => literal::string(&[text]).map(|pieces| Literal::Str(texts(&pieces))),
            T::Bytes => literal::bytes(text).map(Literal::Bytes),
            T::CodePoint => literal::code_point(text).map(Literal::CodePoint),
            _ => return None,
        };
        match value {
            Ok(value) => Some(value),
            Err(message) => {
                self.errors.push(LowerError::Literal {
                    message,
                    range: token.range(),
                });
                None
            }
        }
    }

    fn interpolation(&mut self, node: &SyntaxNode) -> Expr<'db> {
        let tokens: Vec<SyntaxToken> = node
            .tokens()
            .filter(|t| {
                matches!(
                    t.kind(),
                    LeafKind::Token(T::StrStart | T::TripleStrStart | T::StrMid | T::StrEnd)
                )
            })
            .collect();
        let exprs: Vec<ExprId> = node.children().map(|n| self.expr(&n)).collect();
        // A string cut short by a syntax error was reported.
        let complete = tokens.last().map(|t| t.kind()) == Some(LeafKind::Token(T::StrEnd))
            && tokens.len() == exprs.len() + 1;
        if !complete {
            return Expr::Missing;
        }
        let texts: Vec<&str> = tokens.iter().map(|t| t.text()).collect();
        match literal::string(&texts) {
            Ok(pieces) => Expr::Str(
                pieces
                    .into_iter()
                    .map(|p| match p {
                        Piece::Text(t) => StrPart::Text(t),
                        Piece::Hole(i) => StrPart::Expr(exprs[i]),
                    })
                    .collect(),
            ),
            Err(message) => {
                self.errors.push(LowerError::Literal {
                    message,
                    range: node.range(),
                });
                Expr::Missing
            }
        }
    }

    fn value_name(&mut self, token: &SyntaxToken) -> Expr<'db> {
        let name = self.name(token.text());
        let local = self.local(name);
        let item = self.resolve(name);
        if local.is_none() && item.is_none() {
            self.errors.push(LowerError::Unresolved {
                name: token.text().to_string(),
                range: token.range(),
            });
            return Expr::Missing;
        }
        Expr::Name { name, local, item }
    }

    /// The functions in scope named `name`.
    fn functions(&self, name: Name<'db>) -> Vec<ItemId<'db>> {
        match self.resolve(name) {
            Some(Resolution::Value { functions, .. }) => functions,
            _ => Vec::new(),
        }
    }

    /// A call of the operator function `function` (§6.2).
    fn operator(&mut self, function: &'static str, args: Vec<ExprId>, range: Range<u32>) -> ExprId {
        let name = self.name(function);
        let functions = self.functions(name);
        let callee = if functions.is_empty() {
            self.errors.push(LowerError::NoOperator {
                function,
                range: range.clone(),
            });
            Expr::Missing
        } else {
            Expr::Name {
                name,
                local: None,
                item: Some(Resolution::Value {
                    value: None,
                    functions,
                }),
            }
        };
        let callee = self.alloc_expr(callee, range.clone());
        self.alloc_expr(
            Expr::Call {
                callee,
                args,
                fields: None,
            },
            range,
        )
    }

    fn binary(&mut self, node: &SyntaxNode) -> ExprId {
        let range = node.range();
        let mut nodes = node.children();
        let lhs = self.expr_or_missing(nodes.next().as_ref(), node);
        let rhs = self.expr_or_missing(nodes.next().as_ref(), node);
        let op = node
            .tokens()
            .find_map(|t| match t.kind() {
                LeafKind::Token(kind) => Some(kind),
                LeafKind::Trivia(_) => None,
            })
            .unwrap_or(T::Error);
        let function = match op {
            T::And => return self.alloc_expr(Expr::And(lhs, rhs), range),
            T::Or => return self.alloc_expr(Expr::Or(lhs, rhs), range),
            T::Plus => "add",
            T::Minus => "subtract",
            T::Star => "multiply",
            T::Slash => "divide",
            T::Percent => "remainder",
            T::PlusPercent => "addWrapping",
            T::MinusPercent => "subtractWrapping",
            T::StarPercent => "multiplyWrapping",
            T::EqEq | T::BangEq => "equals",
            T::Lt => "lessThan",
            T::LtEq => "lessOrEqual",
            T::Gt => "greaterThan",
            T::GtEq => "greaterOrEqual",
            _ => return self.alloc_expr(Expr::Missing, range),
        };
        let call = self.operator(function, vec![lhs, rhs], range.clone());
        if op == T::BangEq {
            return self.alloc_expr(Expr::Not(call), range);
        }
        call
    }

    /// `not`, unary `-`, or a run of prefix symbols, each applied to what
    /// follows it (§8.5).
    fn prefix(&mut self, node: &SyntaxNode) -> ExprId {
        let range = node.range();
        let operand = node.children().next();
        let operand = self.expr_or_missing(operand.as_ref(), node);
        let tokens: Vec<SyntaxToken> = node.tokens().filter(|t| !t.is_trivia()).collect();
        match tokens.first().map(|t| t.kind()) {
            Some(LeafKind::Token(T::Not)) => self.alloc_expr(Expr::Not(operand), range),
            Some(LeafKind::Token(T::Minus)) => self.operator("negate", vec![operand], range),
            _ => {
                let text: String = tokens.iter().map(|t| t.text()).collect();
                let Some(functions) = self.split_prefixes(&text) else {
                    self.errors.push(LowerError::UnknownPrefix { text, range });
                    return operand;
                };
                // The prefix next to the operand applies first.
                functions.into_iter().rev().fold(operand, |arg, id| {
                    let name = *id.name(self.db);
                    let callee = self.alloc_expr(
                        Expr::Name {
                            name,
                            local: None,
                            item: Some(Resolution::Value {
                                value: None,
                                functions: vec![id],
                            }),
                        },
                        range.clone(),
                    );
                    self.alloc_expr(
                        Expr::Call {
                            callee,
                            args: vec![arg],
                            fields: None,
                        },
                        range.clone(),
                    )
                })
            }
        }
    }

    /// The declared prefixes `text` consists of, matched longest first.
    fn split_prefixes(&self, mut text: &str) -> Option<Vec<ItemId<'db>>> {
        let mut functions = Vec::new();
        while !text.is_empty() {
            let (prefix, id) = self
                .prefixes
                .iter()
                .find(|(p, _)| text.starts_with(p.as_str()))?;
            functions.push(*id);
            text = &text[prefix.len()..];
        }
        Some(functions)
    }

    /// Positional arguments, and the field list of the named arguments and
    /// spreads if there are any.
    fn args(&mut self, list: Option<&SyntaxNode>) -> (Vec<ExprId>, Option<Vec<FieldArg<'db>>>) {
        let mut positional = Vec::new();
        let mut fields: Option<Vec<FieldArg>> = None;
        for arg in list
            .into_iter()
            .flat_map(|l| l.children().collect::<Vec<_>>())
        {
            match arg.kind() {
                S::LabeledArg => {
                    let path = child(&arg, S::Label)
                        .map(|label| {
                            label
                                .tokens()
                                .filter(|t| !t.is_trivia() && t.kind() != LeafKind::Token(T::Dot))
                                .map(|t| self.name(t.text()))
                                .collect()
                        })
                        .unwrap_or_default();
                    let value = arg.children().find(|n| n.kind() != S::Label);
                    let value = self.argument(value.as_ref(), &arg);
                    fields
                        .get_or_insert_default()
                        .push(FieldArg::Field { path, value });
                }
                S::SpreadArg => {
                    let value = self.argument(arg.children().next().as_ref(), &arg);
                    fields.get_or_insert_default().push(FieldArg::Spread(value));
                }
                _ => positional.push(self.argument(Some(&arg), &arg)),
            }
        }
        (positional, fields)
    }

    /// An argument: a partial application ends here, unless the argument is
    /// a `_` itself, which belongs to the call around it.
    fn argument(&mut self, node: Option<&SyntaxNode>, parent: &SyntaxNode) -> ExprId {
        match node {
            Some(node) if node.kind() == S::Placeholder => self.expr(node),
            Some(node) => self.boundary(node),
            None => self.alloc_expr(Expr::Missing, parent.range()),
        }
    }

    fn call(&mut self, node: &SyntaxNode) -> Expr<'db> {
        let callee = node.children().next();
        let list = child(node, S::ArgList);
        let trailing = node.children().skip(1).find(|n| n.kind() == S::Closure);
        // `x.f(…)` and `T.f(…)`: the receiver comes before the arguments.
        if let Some(field) = callee.as_ref().filter(|c| c.kind() == S::FieldExpr)
            && let Some(token) = ident(field)
        {
            let name = self.name(token.text());
            let functions = self.functions(name);
            let receiver = field.children().next();
            if let Some(ty) = receiver.as_ref().and_then(|r| self.type_receiver(r)) {
                let (mut args, fields) = self.args(list.as_ref());
                args.extend(trailing.map(|c| self.expr(&c)));
                return Expr::TypedCall {
                    ty,
                    name,
                    functions,
                    args,
                    fields,
                };
            }
            let receiver = self.expr_or_missing(receiver.as_ref(), field);
            let (mut args, fields) = self.args(list.as_ref());
            args.extend(trailing.map(|c| self.expr(&c)));
            return Expr::MethodCall {
                receiver,
                name,
                functions,
                optional: optional(field),
                args,
                fields,
            };
        }
        let callee = self.expr_or_missing(callee.as_ref(), node);
        let (mut args, fields) = self.args(list.as_ref());
        args.extend(trailing.map(|c| self.expr(&c)));
        Expr::Call {
            callee,
            args,
            fields,
        }
    }

    /// The type in front of `T.f(…)`: a name that is a type and no binding.
    fn type_receiver(&mut self, node: &SyntaxNode) -> Option<TypeRefId> {
        if node.kind() != S::NameRef {
            return None;
        }
        let name = self.name(ident(node)?.text());
        if self.local(name).is_some() || !self.scope.is_type(name) {
            return None;
        }
        Some(self.type_node(node))
    }

    fn bracket(&mut self, node: &SyntaxNode) -> Expr<'db> {
        let base_node = node.children().next();
        let args: Vec<SyntaxNode> = child(node, S::ArgList)
            .map(|l| l.children().collect())
            .unwrap_or_default();
        let types = base_node.as_ref().is_some_and(|b| self.takes_type_args(b));
        let base = self.expr_or_missing(base_node.as_ref(), node);
        if types {
            let args = args.iter().map(|a| self.type_arg(a)).collect();
            return Expr::TypeArgs { base, args };
        }
        let args = args
            .iter()
            .map(|arg| {
                if is_type_only(arg.kind()) {
                    self.errors
                        .push(LowerError::ExpectedValue { range: arg.range() });
                }
                self.argument(Some(arg), arg)
            })
            .collect();
        Expr::Index { base, args }
    }

    /// Whether brackets after `node` hold type arguments: after a type, a
    /// form or functions, rather than a value (§6.5).
    fn takes_type_args(&self, node: &SyntaxNode) -> bool {
        if node.kind() != S::NameRef {
            return false;
        }
        let Some(token) = ident(node) else {
            return false;
        };
        let name = self.name(token.text());
        if self.local(name).is_some() {
            return false;
        }
        match self.scope.resolve(name) {
            Some(Resolution::Type(_) | Resolution::Form(_)) => true,
            Some(Resolution::Value { value, .. }) => value.is_none(),
            None => false,
        }
    }

    // Patterns.

    fn pattern_or_missing(
        &mut self,
        node: Option<&SyntaxNode>,
        parent: &SyntaxNode,
        kind: BindingKind,
    ) -> PatId {
        let mut cx = PatCtx::new(kind, true);
        let pat = match node {
            Some(node) => self.pattern(node, false, &mut cx),
            None => self.alloc_pat(Pat::Missing, parent.range()),
        };
        self.declare_all(&cx);
        pat
    }

    /// The pattern of a module-level `let`, whose names are the module's.
    pub fn module_pattern(&mut self, node: &SyntaxNode) -> PatId {
        let mut cx = PatCtx::new(BindingKind::Module, false);
        self.pattern(node, false, &mut cx)
    }

    fn declare_all(&mut self, cx: &PatCtx<'db>) {
        for &(name, binding) in &cx.bound {
            self.declare(name, binding);
        }
    }

    fn pattern(&mut self, node: &SyntaxNode, arm: bool, cx: &mut PatCtx<'db>) -> PatId {
        let range = node.range();
        let pat = match node.kind() {
            S::WildcardPat => Pat::Wildcard,
            S::NamePat => match ident(node) {
                // At the top of an arm a bare name is a type or tag; elsewhere
                // it is one if a type of that name is visible (§6.9).
                Some(token) if arm || self.scope.is_type(self.name(token.text())) => {
                    Pat::Type(self.type_node(node))
                }
                Some(token) => Pat::Bind {
                    binding: self.pattern_binding(&token, cx),
                    sub: None,
                },
                None => Pat::Missing,
            },
            S::BindPat => {
                let binding = match ident(node) {
                    Some(token) => self.pattern_binding(&token, cx),
                    None => self.alloc_binding(None, cx.kind, range.clone()),
                };
                let sub = node.children().next().map(|n| self.pattern(&n, arm, cx));
                Pat::Bind { binding, sub }
            }
            S::TypePat => Pat::Type(self.type_node(node)),
            S::LiteralPat => match self.pattern_literals(node).as_slice() {
                [literal] => Pat::Literal(literal.clone()),
                _ => Pat::Missing,
            },
            S::RangePat => match self.pattern_literals(node).as_slice() {
                [start, end] => Pat::Range {
                    start: start.clone(),
                    end: end.clone(),
                },
                _ => Pat::Missing,
            },
            S::RecordPat => {
                let ty = ident(node).map(|_| self.type_node(node));
                let fields = node
                    .children()
                    .filter(|n| n.kind() != S::TypeArgs)
                    .map(|field| self.pat_field(&field, cx))
                    .collect();
                Pat::Record { ty, fields }
            }
            S::ListPat => {
                let mut before = Vec::new();
                let mut after = Vec::new();
                let mut rest = None;
                for item in node.children() {
                    if item.kind() == S::RestPat {
                        rest = Some(ident(&item).map(|t| self.pattern_binding(&t, cx)));
                    } else if rest.is_none() {
                        before.push(self.pattern(&item, false, cx));
                    } else {
                        after.push(self.pattern(&item, false, cx));
                    }
                }
                Pat::List {
                    before,
                    rest,
                    after,
                }
            }
            S::OrPat => {
                let outer = cx.reuse_from;
                cx.reuse_from = Some(outer.unwrap_or(cx.bound.len()));
                let mut first: Option<Vec<Name>> = None;
                let mut alternatives = Vec::new();
                for alternative in node.children() {
                    cx.alternatives.push(Vec::new());
                    alternatives.push(self.pattern(&alternative, arm, cx));
                    let names = cx.alternatives.pop().unwrap();
                    for outer in &mut cx.alternatives {
                        outer.extend(names.iter().copied());
                    }
                    match &first {
                        None => first = Some(names),
                        Some(first) => {
                            let missing = first
                                .iter()
                                .filter(|n| !names.contains(n))
                                .chain(names.iter().filter(|n| !first.contains(n)));
                            for name in missing {
                                self.errors.push(LowerError::NotInEveryAlternative {
                                    name: name.text(self.db).clone(),
                                    range: alternative.range(),
                                });
                            }
                        }
                    }
                }
                cx.reuse_from = outer;
                Pat::Or(alternatives)
            }
            _ => Pat::Missing,
        };
        self.alloc_pat(pat, range)
    }

    fn pat_field(&mut self, node: &SyntaxNode, cx: &mut PatCtx<'db>) -> PatField<'db> {
        if node.kind() != S::PatField {
            return PatField {
                name: None,
                pat: self.pattern(node, false, cx),
            };
        }
        let token = first_token(node);
        let name = token.as_ref().map(|t| self.name(t.text()));
        let pat = match node.children().next() {
            Some(sub) => self.pattern(&sub, false, cx),
            // `name:` alone binds the field's name.
            None => match &token {
                Some(token) if token.kind() == LeafKind::Token(T::Ident) => {
                    let binding = self.pattern_binding(token, cx);
                    self.alloc_pat(Pat::Bind { binding, sub: None }, token.range())
                }
                _ => self.alloc_pat(Pat::Missing, node.range()),
            },
        };
        PatField { name, pat }
    }

    fn pattern_literals(&mut self, node: &SyntaxNode) -> Vec<PatLiteral> {
        let tokens: Vec<SyntaxToken> = node
            .tokens()
            .filter(|t| {
                matches!(
                    t.kind(),
                    LeafKind::Token(
                        T::Minus | T::Int | T::Float | T::Str | T::Bytes | T::CodePoint
                    )
                )
            })
            .collect();
        let mut literals = Vec::new();
        let mut negative = false;
        for token in &tokens {
            match token.kind() {
                LeafKind::Token(T::Minus) => negative = true,
                LeafKind::Token(kind) => {
                    if let Some(literal) = self.literal_token(kind, token) {
                        literals.push(PatLiteral { negative, literal });
                    }
                    negative = false;
                }
                LeafKind::Trivia(_) => {}
            }
        }
        literals
    }

    /// The binding a pattern makes for `token`: a new one, or within an
    /// or-pattern the one an earlier alternative made.
    fn pattern_binding(&mut self, token: &SyntaxToken, cx: &mut PatCtx<'db>) -> BindingId {
        let name = self.name(token.text());
        for frame in &mut cx.alternatives {
            frame.push(name);
        }
        let earlier = cx.bound.iter().position(|(n, _)| *n == name);
        if let Some(i) = earlier {
            if cx.reuse_from.is_some_and(|from| i >= from) {
                return cx.bound[i].1;
            }
            let previous = Previous::Local(self.map.bindings[cx.bound[i].1.index()].clone());
            self.errors.push(LowerError::Redeclared(Redeclaration {
                name: token.text().to_string(),
                range: token.range(),
                previous,
            }));
        } else if cx.check {
            self.check_new(name, &token.range());
        }
        let binding = self.alloc_binding(Some(name), cx.kind, token.range());
        cx.bound.push((name, binding));
        binding
    }

    // Types.

    fn type_or_missing(&mut self, node: Option<SyntaxNode>, parent: &SyntaxNode) -> TypeRefId {
        match node {
            Some(node) => self.type_node(&node),
            None => self.alloc_type(TypeRef::Missing, parent.range()),
        }
    }

    /// A type, from type syntax or from an expression that bracket
    /// application reads as one (§6.5).
    pub fn type_node(&mut self, node: &SyntaxNode) -> TypeRefId {
        let range = node.range();
        let ty = match node.kind() {
            // A name with type arguments; as an expression, `List[Int]` is
            // a bracket application of a name.
            S::NamedType | S::NameRef | S::NamePat | S::TypePat | S::RecordPat => {
                let args = child(node, S::TypeArgs)
                    .map(|a| a.children().map(|n| self.type_arg(&n)).collect())
                    .unwrap_or_default();
                self.named_type(node, args)
            }
            S::BracketExpr => match node.children().next() {
                Some(base) if base.kind() == S::NameRef => {
                    let args = child(node, S::ArgList)
                        .map(|a| a.children().map(|n| self.type_arg(&n)).collect())
                        .unwrap_or_default();
                    self.named_type(&base, args)
                }
                _ => self.not_a_type(node),
            },
            S::InferType | S::Placeholder => TypeRef::Infer,
            S::UnitType => TypeRef::Unit,
            S::ParenType => {
                let inner = self.type_or_missing(node.children().next(), node);
                if child(node, S::IsClause).is_none() {
                    return inner;
                }
                let pure = self.pure_marker(node);
                match self.body.types[inner.index()].clone() {
                    TypeRef::Fn { params, result, .. } => TypeRef::Fn {
                        params,
                        result,
                        pure,
                    },
                    other => {
                        if pure {
                            self.errors.push(LowerError::Marker {
                                range: range.clone(),
                            });
                        }
                        other
                    }
                }
            }
            S::ParenExpr => {
                let inner = node.children().next().and_then(|l| l.children().next());
                return self.type_or_missing(inner, node);
            }
            S::RecordExpr => {
                let mut fields = Vec::new();
                for arg in node
                    .children()
                    .next()
                    .into_iter()
                    .flat_map(|l| l.children().collect::<Vec<_>>())
                {
                    match arg.kind() {
                        S::LabeledArg => {
                            let label = child(&arg, S::Label).and_then(|l| first_token(&l));
                            let value = arg.children().find(|n| n.kind() != S::Label);
                            let ty = self.type_or_missing(value, &arg);
                            if let Some(label) = label {
                                let name = self.name(label.text());
                                fields.push(TypeField::Field { name, ty });
                            }
                        }
                        S::SpreadArg => {
                            let ty = self.type_or_missing(arg.children().next(), &arg);
                            fields.push(TypeField::Spread(ty));
                        }
                        _ => {
                            self.not_a_type(&arg);
                        }
                    }
                }
                TypeRef::Record {
                    fields,
                    open: false,
                }
            }
            S::RecordType => {
                let mut fields = Vec::new();
                let mut open = false;
                for entry in node.children() {
                    match entry.kind() {
                        S::TypeField => {
                            let name = first_token(&entry).map(|t| self.name(t.text()));
                            let ty = self.type_or_missing(entry.children().next(), &entry);
                            if let Some(name) = name {
                                fields.push(TypeField::Field { name, ty });
                            }
                        }
                        S::SpreadType => {
                            let ty = self.type_or_missing(entry.children().next(), &entry);
                            fields.push(TypeField::Spread(ty));
                        }
                        S::OpenRow => open = true,
                        _ => {}
                    }
                }
                TypeRef::Record { fields, open }
            }
            S::FnType => {
                let params = child(node, S::FnTypeParams)
                    .map(|p| p.children().map(|t| self.type_node(&t)).collect())
                    .unwrap_or_default();
                let result = node.children().find(|n| n.kind() != S::FnTypeParams);
                let result = self.type_or_missing(result, node);
                TypeRef::Fn {
                    params,
                    result,
                    pure: false,
                }
            }
            S::UnionType => TypeRef::Union(node.children().map(|t| self.type_node(&t)).collect()),
            _ => self.not_a_type(node),
        };
        self.alloc_type(ty, range)
    }

    fn not_a_type(&mut self, node: &SyntaxNode) -> TypeRef<'db> {
        self.errors.push(LowerError::ExpectedType {
            range: node.range(),
        });
        TypeRef::Missing
    }

    fn type_arg(&mut self, node: &SyntaxNode) -> TypeArg {
        match node.kind() {
            S::Literal => match first_token(node) {
                Some(token) if token.kind() == LeafKind::Token(T::Int) => {
                    match self.literal_token(T::Int, &token) {
                        Some(Literal::Int(n)) => TypeArg::Int(n),
                        _ => TypeArg::Type(self.alloc_type(TypeRef::Missing, node.range())),
                    }
                }
                _ => TypeArg::Type(self.type_node(node)),
            },
            S::IsClause => TypeArg::Is(
                node.descendants()
                    .filter(|n| n.kind() == S::Marker)
                    .map(|marker| {
                        let negated = marker.tokens().any(|t| t.kind() == LeafKind::Token(T::Not));
                        let ty = self.type_or_missing(marker.children().next(), &marker);
                        (negated, ty)
                    })
                    .collect(),
            ),
            _ => TypeArg::Type(self.type_node(node)),
        }
    }

    /// The type named by the first identifier of `node`: a type parameter,
    /// or a type or form in scope.
    fn named_type(&mut self, node: &SyntaxNode, args: Vec<TypeArg>) -> TypeRef<'db> {
        let Some(token) = ident(node) else {
            return TypeRef::Missing;
        };
        let name = self.name(token.text());
        let param = self.type_scopes.iter().rev().find(|(n, _)| *n == name);
        let target = match (param, self.scope.resolve(name)) {
            (Some(&(_, index)), _) => TypeTarget::Param(index),
            (None, Some(Resolution::Type(id) | Resolution::Form(id))) => TypeTarget::Item(*id),
            _ => {
                self.errors.push(LowerError::UnknownType {
                    name: token.text().to_string(),
                    range: token.range(),
                });
                TypeTarget::Unresolved
            }
        };
        TypeRef::Named { name, target, args }
    }
}

impl<'db> PatCtx<'db> {
    fn new(kind: BindingKind, check: bool) -> Self {
        PatCtx {
            kind,
            check,
            bound: Vec::new(),
            reuse_from: None,
            alternatives: Vec::new(),
        }
    }
}

/// The parts of a `let`: its pattern, type, value and `else` part.
pub(crate) struct LetParts {
    pub pattern: Option<SyntaxNode>,
    pub ty: Option<SyntaxNode>,
    pub value: Option<SyntaxNode>,
    pub otherwise: Option<SyntaxNode>,
}

pub(crate) fn let_parts(node: &SyntaxNode) -> LetParts {
    let mut parts = LetParts {
        pattern: None,
        ty: None,
        value: None,
        otherwise: None,
    };
    let mut after = None;
    for element in node.children_with_tokens() {
        match element {
            crag_syntax::SyntaxElement::Token(token) => match token.kind() {
                LeafKind::Token(T::Colon) => after = Some(T::Colon),
                LeafKind::Token(T::Equals) => after = Some(T::Equals),
                _ => {}
            },
            crag_syntax::SyntaxElement::Node(child) => match (child.kind(), after) {
                (S::LetElse, _) => parts.otherwise = child.children().next(),
                (_, None) => parts.pattern = Some(child),
                (_, Some(T::Colon)) => parts.ty = Some(child),
                _ => parts.value = Some(child),
            },
        }
    }
    parts
}

fn field_values<'f>(fields: &'f mut Option<Vec<FieldArg>>) -> impl Iterator<Item = &'f mut ExprId> {
    fields.iter_mut().flatten().map(|f| match f {
        FieldArg::Field { value, .. } => value,
        FieldArg::Spread(value) => value,
    })
}

fn field_value(field: &FieldArg) -> ExprId {
    match field {
        FieldArg::Field { value, .. } | FieldArg::Spread(value) => *value,
    }
}

fn texts(pieces: &[Piece]) -> String {
    pieces
        .iter()
        .filter_map(|p| match p {
            Piece::Text(t) => Some(t.as_str()),
            Piece::Hole(_) => None,
        })
        .collect()
}

fn is_statement(kind: S) -> bool {
    matches!(
        kind,
        S::LetDecl
            | S::VarDecl
            | S::RefDecl
            | S::Assign
            | S::ForStmt
            | S::EmitStmt
            | S::ReturnStmt
            | S::OnStmt
            | S::FnDecl
            | S::Error
    )
}

/// Kinds bracket application parses only as types.
fn is_clause(kind: S) -> bool {
    matches!(kind, S::WhereClause | S::IsClause | S::OnClause)
}

fn is_type_only(kind: S) -> bool {
    matches!(kind, S::FnType | S::UnionType | S::IsClause)
}

fn optional(field: &SyntaxNode) -> bool {
    field
        .tokens()
        .any(|t| t.kind() == LeafKind::Token(T::QuestionDot))
}

fn child(node: &SyntaxNode, kind: S) -> Option<SyntaxNode> {
    node.children().find(|n| n.kind() == kind)
}

pub(crate) fn ident(node: &SyntaxNode) -> Option<SyntaxToken> {
    node.tokens()
        .find(|t| t.kind() == LeafKind::Token(T::Ident))
}

fn first_token(node: &SyntaxNode) -> Option<SyntaxToken> {
    node.tokens().find(|t| !t.is_trivia())
}
