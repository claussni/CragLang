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

//! Escape and bindings-only analysis (Implementation Plan §11.5.8).
//!
//! Each binding and each closure gets a level: Local when it is used only
//! in its frame, Scoped when a task captures it that ends before the scope
//! does, and Escaping when it is returned, stored, emitted, captured by an
//! escaping closure, or passed to a function whose use of it is unknown. A
//! call passes an argument at the level the callee's summary gives its
//! parameter; a function's summary is the level of its parameters, solved
//! with its group's errors and effects (§11.5.2). The levels of a body
//! grow from Local until nothing changes.
//!
//! The levels decide where closure conversion places a closure (§11.5.9)
//! and check the bindings-only values: refs, `ext` cells and the closures
//! and `lazy` values that carry them are never Escaping (§3.12, §9.2), and
//! an escaping closure captures no `var` (§6.4.1).

use std::collections::{HashMap, HashSet};

use crag_db::Db;
use crag_hir::{
    BindingId, BindingKind, Body, Expr, ExprId, FieldArg, ItemId, PRELUDE, Pat, PatId, Program,
    Stmt, c_function, hir_body,
};

use crate::def::signature;
use crate::generic::mentions;
use crate::result::{Callee, ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

#[derive(
    Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, crag_db::SalsaValue,
)]
pub enum EscapeLevel {
    #[default]
    Local,
    Scoped,
    Escaping,
}

/// What escape analysis found in a body.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Escapes {
    /// The level of each parameter of a function: its summary.
    pub params: Vec<EscapeLevel>,
    /// The level of each closure literal, `lazy` expression and local
    /// function body, by its expression.
    pub closures: Vec<(ExprId, EscapeLevel)>,
    /// The bindings each of these captures, sorted: those it uses that it
    /// does not declare, its inner frames' included, which closure
    /// conversion puts into its environment (§11.5.9).
    pub captures: Vec<(ExprId, Vec<BindingId>)>,
}

/// The summary of a function without a body: a C function may keep what
/// it is passed; a prelude operation calls the functions passed to it and
/// gives back only what its result can hold, and an access function keeps
/// only the value it places in its cell (§9.3).
pub fn intrinsic_escapes<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
) -> Option<Vec<EscapeLevel>> {
    let sig = signature(db, program, function);
    if c_function(db, function).is_some() {
        return Some(vec![EscapeLevel::Escaping; sig.params.len()]);
    }
    if hir_body(db, program, crag_hir::Owner::Item(function))
        .root
        .is_some()
    {
        return None;
    }
    let prelude = function.module(db).path(db) == PRELUDE;
    let result = sig.result;
    Some(
        sig.params
            .iter()
            .map(|p| match p.ty.kind(db) {
                TyKind::Builtin(Builtin::Ref | Builtin::Ext, _) | TyKind::Fn { .. } if prelude => {
                    EscapeLevel::Local
                }
                _ => {
                    // A value that the result's type parameters can hold
                    // may come back.
                    let shared = result.is_some_and(|r| {
                        let in_param = |i: u32| {
                            let index = i;
                            mentions(db, p.ty, function, &|j| j == index)
                        };
                        mentions(db, r, function, &in_param)
                    });
                    match shared || !prelude {
                        true => EscapeLevel::Escaping,
                        false => EscapeLevel::Local,
                    }
                }
            })
            .collect(),
    )
}

/// What is bindings-only, for messages.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum BindingsOnly {
    Ref,
    Ext,
    Closure,
    Lazy,
}

pub struct Walked<'db> {
    pub escapes: Escapes,
    pub errors: Vec<TypeError<'db>>,
}

pub struct EscapeWalker<'a, 'db> {
    db: &'db dyn Db,
    body: &'a Body<'db>,
    bindings: &'a [Option<Ty<'db>>],
    callees: HashMap<ExprId, &'a Callee<'db>>,
    summary_of: &'a dyn Fn(ItemId<'db>) -> Vec<EscapeLevel>,
    signature_of: &'a dyn Fn(ItemId<'db>) -> Vec<Option<crag_hir::Name<'db>>>,
    levels: Vec<EscapeLevel>,
    /// Of closures and `lazy` expressions; a local function's is its
    /// binding's.
    frames: HashMap<ExprId, EscapeLevel>,
    /// The bindings each frame declares, and those it captures.
    declared: HashMap<ExprId, HashSet<BindingId>>,
    captures: HashMap<ExprId, HashSet<BindingId>>,
    /// The value each simple `let` binds, and the body of each local
    /// function by its binding.
    values: HashMap<BindingId, ExprId>,
    local_fns: HashMap<ExprId, BindingId>,
    /// The frames being walked, innermost last.
    stack: Vec<ExprId>,
    changed: bool,
    report: Option<Vec<TypeError<'db>>>,
}

impl<'a, 'db> EscapeWalker<'a, 'db> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        db: &'db dyn Db,
        body: &'a Body<'db>,
        bindings: &'a [Option<Ty<'db>>],
        callees: &'a [(ExprId, Callee<'db>)],
        summary_of: &'a dyn Fn(ItemId<'db>) -> Vec<EscapeLevel>,
        signature_of: &'a dyn Fn(ItemId<'db>) -> Vec<Option<crag_hir::Name<'db>>>,
    ) -> Self {
        let mut walker = EscapeWalker {
            db,
            body,
            bindings,
            callees: callees.iter().map(|(e, c)| (*e, c)).collect(),
            summary_of,
            signature_of,
            levels: vec![EscapeLevel::Local; body.bindings.len()],
            frames: HashMap::new(),
            declared: HashMap::new(),
            captures: HashMap::new(),
            values: HashMap::new(),
            local_fns: HashMap::new(),
            stack: Vec::new(),
            changed: false,
            report: None,
        };
        walker.find_frames();
        walker
    }

    /// The levels of the body, grown until nothing changes, and then the
    /// errors of its bindings-only values.
    pub fn walk_body(mut self) -> Walked<'db> {
        let Some(root) = self.body.root else {
            return Walked {
                escapes: Escapes::default(),
                errors: Vec::new(),
            };
        };
        loop {
            self.changed = false;
            self.walk(root, EscapeLevel::Escaping);
            if !self.changed {
                break;
            }
        }
        self.report = Some(Vec::new());
        self.walk(root, EscapeLevel::Escaping);
        let mut errors = self.report.take().unwrap_or_default();
        // An escaping closure captures no `var` (§6.4.1).
        let mut frames: Vec<ExprId> = self.declared.keys().copied().collect();
        frames.sort();
        for frame in frames {
            if self.frame_level(frame) != EscapeLevel::Escaping {
                continue;
            }
            let mut vars: Vec<BindingId> = self
                .captures
                .get(&frame)
                .into_iter()
                .flatten()
                .copied()
                .filter(|&b| self.body.binding(b).kind == BindingKind::Var)
                .collect();
            vars.sort();
            for var in vars {
                if let Some(name) = self.body.binding(var).name {
                    errors.push(TypeError {
                        site: Site::Expr(frame),
                        kind: ErrorKind::EscapingVar { name },
                    });
                }
            }
        }
        let params = self
            .body
            .params
            .iter()
            .map(|p| self.levels[p.binding.index()])
            .collect();
        let mut closures: Vec<(ExprId, EscapeLevel)> = self
            .declared
            .keys()
            .map(|&f| (f, self.frame_level(f)))
            .collect();
        closures.sort();
        let captures = closures
            .iter()
            .map(|&(frame, _)| {
                let mut bindings: Vec<BindingId> = self
                    .captures
                    .get(&frame)
                    .into_iter()
                    .flatten()
                    .copied()
                    .collect();
                bindings.sort();
                (frame, bindings)
            })
            .collect();
        let mut seen = HashSet::new();
        errors.retain(|e| seen.insert((e.site, format!("{:?}", e.kind))));
        Walked {
            escapes: Escapes {
                params,
                closures,
                captures,
            },
            errors,
        }
    }

    /// Finds the frames, closures, `lazy` expressions and local function
    /// bodies, with the bindings each declares, and the simple `let`s.
    fn find_frames(&mut self) {
        let body = self.body;
        for (i, expr) in body.exprs.iter().enumerate() {
            let id = ExprId(i as u32);
            match expr {
                Expr::Closure {
                    params,
                    body: inner,
                } => {
                    let mut declared = HashSet::new();
                    for p in params {
                        pat_bindings(body, p.pat, &mut declared);
                    }
                    declared.extend(declared_in(body, *inner));
                    self.declared.insert(id, declared);
                }
                Expr::Lazy(inner) => {
                    self.declared.insert(id, declared_in(body, *inner));
                }
                Expr::Block { stmts, .. } => {
                    for stmt in stmts {
                        match stmt {
                            Stmt::Let { pat, value, .. } => {
                                if let Pat::Bind { binding, sub: None } = body.pat(*pat) {
                                    self.values.insert(*binding, *value);
                                }
                            }
                            Stmt::Fn { binding, function } => {
                                if let Some(root) = function.body {
                                    let mut declared: HashSet<BindingId> =
                                        function.params.iter().map(|p| p.binding).collect();
                                    declared.extend(declared_in(body, root));
                                    self.declared.insert(root, declared);
                                    self.local_fns.insert(root, *binding);
                                }
                            }
                            _ => {}
                        }
                    }
                }
                _ => {}
            }
        }
    }

    fn frame_level(&self, frame: ExprId) -> EscapeLevel {
        match self.local_fns.get(&frame) {
            Some(binding) => self.levels[binding.index()],
            None => self.frames.get(&frame).copied().unwrap_or_default(),
        }
    }

    fn raise_frame(&mut self, frame: ExprId, level: EscapeLevel) {
        if let Some(&binding) = self.local_fns.get(&frame) {
            self.raise(binding, level);
            return;
        }
        let entry = self.frames.entry(frame).or_default();
        if level > *entry {
            *entry = level;
            self.changed = true;
        }
    }

    fn raise(&mut self, binding: BindingId, level: EscapeLevel) {
        let slot = &mut self.levels[binding.index()];
        if level > *slot {
            *slot = level;
            self.changed = true;
        }
    }

    fn error(&mut self, site: ExprId, kind: ErrorKind<'db>) {
        if let Some(errors) = &mut self.report {
            errors.push(TypeError {
                site: Site::Expr(site),
                kind,
            });
        }
    }

    /// Walks an expression whose value goes where `ctx` says.
    fn walk(&mut self, expr: ExprId, ctx: EscapeLevel) {
        self.walk_at(expr, ctx, true);
    }

    /// `report` is false where an escape is reported elsewhere: at the
    /// uses of the binding a value is bound to.
    fn walk_at(&mut self, expr: ExprId, ctx: EscapeLevel, report: bool) {
        use EscapeLevel::*;
        let body = self.body;
        match body.expr(expr) {
            Expr::Name {
                local: Some(binding),
                ..
            } => self.use_binding(*binding, expr, ctx, report),
            Expr::Closure { body: inner, .. } => {
                self.frame_value(expr, ctx, report, BindingsOnly::Closure);
                self.in_frame(expr, *inner);
            }
            Expr::Lazy(inner) => {
                self.frame_value(expr, ctx, report, BindingsOnly::Lazy);
                self.in_frame(expr, *inner);
            }
            Expr::Block { stmts, tail } => {
                for stmt in stmts {
                    self.stmt(stmt);
                }
                if let Some(tail) = tail {
                    self.walk_at(*tail, ctx, report);
                }
            }
            Expr::If {
                condition,
                then,
                otherwise,
            } => {
                self.walk(*condition, Local);
                self.walk_at(*then, ctx, report);
                if let Some(otherwise) = otherwise {
                    self.walk_at(*otherwise, ctx, report);
                }
            }
            Expr::Case { subject, arms } => {
                // The subject flows into the arms' bindings.
                let mut bound = HashSet::new();
                for arm in arms {
                    pat_bindings(body, arm.pat, &mut bound);
                }
                let level = bound
                    .iter()
                    .map(|b| self.levels[b.index()])
                    .max()
                    .unwrap_or(Local);
                self.walk_at(*subject, level, false);
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.walk(guard, Local);
                    }
                    self.walk_at(arm.body, ctx, report);
                }
            }
            Expr::Atomic(inner) => self.walk_at(*inner, ctx, report),
            Expr::Call { .. }
            | Expr::MethodCall { .. }
            | Expr::TypedCall { .. }
            | Expr::Field { .. }
                if self.callees.contains_key(&expr) =>
            {
                self.call(expr);
            }
            // Stored.
            Expr::Record(_) | Expr::List(_) | Expr::Map(_) | Expr::Grid(_) => {
                for child in body.children(expr) {
                    self.walk(child, Escaping);
                }
            }
            _ => {
                for child in body.children(expr) {
                    self.walk(child, Local);
                }
            }
        }
    }

    fn in_frame(&mut self, frame: ExprId, inner: ExprId) {
        self.stack.push(frame);
        // What a closure gives goes to its caller, which is unknown here.
        self.walk(inner, EscapeLevel::Escaping);
        self.stack.pop();
    }

    fn stmt(&mut self, stmt: &Stmt) {
        use EscapeLevel::*;
        let body = self.body;
        match stmt {
            Stmt::Expr(e) => self.walk(*e, Local),
            Stmt::Let { pat, value, .. } | Stmt::LetElse { pat, value, .. } => {
                let mut bound = HashSet::new();
                pat_bindings(body, *pat, &mut bound);
                let level = bound
                    .iter()
                    .map(|b| self.levels[b.index()])
                    .max()
                    .unwrap_or(Local);
                self.walk_at(*value, level, false);
                if let Stmt::LetElse { otherwise, .. } = stmt {
                    self.walk(*otherwise, Local);
                }
            }
            Stmt::Bind { binding, value, .. } => match body.binding(*binding).kind {
                // What a cell holds is stored (§3.12).
                BindingKind::Ref | BindingKind::Ext => self.walk(*value, Escaping),
                _ => self.walk_at(*value, self.levels[binding.index()], false),
            },
            Stmt::Assign { binding, value } => {
                self.walk_at(*value, self.levels[binding.index()], false);
            }
            Stmt::For { iterable, body, .. } => {
                self.walk(*iterable, Local);
                self.walk(*body, Local);
            }
            Stmt::Emit { value, .. } => self.walk(*value, Escaping),
            Stmt::Return(value) => {
                if let Some(value) = value {
                    self.walk(*value, Escaping);
                }
            }
            Stmt::On { handler, .. } => self.walk(*handler, Local),
            Stmt::Fn { function, .. } => {
                for default in function.params.iter().filter_map(|p| p.default) {
                    self.walk(default, Local);
                }
                if let Some(root) = function.body {
                    self.in_frame(root, root);
                }
            }
        }
    }

    /// A binding used where its value goes to `ctx`. A use inside frames
    /// that do not declare it is a capture by each of them, so it escapes
    /// when any of them does. An escape is reported where the value goes
    /// out itself; a capture's at the closure that carries it.
    fn use_binding(&mut self, binding: BindingId, site: ExprId, ctx: EscapeLevel, report: bool) {
        let mut capturing = EscapeLevel::Local;
        for frame in self.stack.clone().into_iter().rev() {
            if self
                .declared
                .get(&frame)
                .is_some_and(|d| d.contains(&binding))
            {
                break;
            }
            self.captures.entry(frame).or_default().insert(binding);
            capturing = capturing.max(self.frame_level(frame));
        }
        self.raise(binding, ctx.max(capturing));
        if report
            && ctx == EscapeLevel::Escaping
            && let Some(what) = self.bindings_only(binding, &mut HashSet::new())
        {
            self.error(site, ErrorKind::BindingsOnly { what });
        }
    }

    fn frame_value(&mut self, frame: ExprId, ctx: EscapeLevel, report: bool, what: BindingsOnly) {
        self.raise_frame(frame, ctx);
        if report && ctx == EscapeLevel::Escaping && self.carries(frame, &mut HashSet::new()) {
            self.error(frame, ErrorKind::BindingsOnly { what });
        }
    }

    /// Whether a binding is bindings-only: a cell, a value of a cell's
    /// type, or a binding of a closure that carries a ref.
    fn bindings_only(
        &self,
        binding: BindingId,
        seen: &mut HashSet<BindingId>,
    ) -> Option<BindingsOnly> {
        if !seen.insert(binding) {
            return None;
        }
        match self.body.binding(binding).kind {
            BindingKind::Ref => return Some(BindingsOnly::Ref),
            BindingKind::Ext => return Some(BindingsOnly::Ext),
            _ => {}
        }
        match self
            .bindings
            .get(binding.index())
            .copied()
            .flatten()
            .map(|t| t.kind(self.db))
        {
            Some(TyKind::Builtin(Builtin::Ref, _)) => return Some(BindingsOnly::Ref),
            Some(TyKind::Builtin(Builtin::Ext, _)) => return Some(BindingsOnly::Ext),
            _ => {}
        }
        if let Some((&root, _)) = self.local_fns.iter().find(|(_, b)| **b == binding) {
            return self
                .carries(root, &mut HashSet::new())
                .then_some(BindingsOnly::Closure);
        }
        let value = *self.values.get(&binding)?;
        match self.body.expr(value) {
            Expr::Name {
                local: Some(other), ..
            } => self.bindings_only(*other, seen),
            Expr::Closure { .. } => self
                .carries(value, &mut HashSet::new())
                .then_some(BindingsOnly::Closure),
            Expr::Lazy(_) => self
                .carries(value, &mut HashSet::new())
                .then_some(BindingsOnly::Lazy),
            _ => None,
        }
    }

    /// Whether a frame captures a bindings-only value, directly or
    /// through another closure (§3.12).
    fn carries(&self, frame: ExprId, seen: &mut HashSet<ExprId>) -> bool {
        if !seen.insert(frame) {
            return false;
        }
        self.captures
            .get(&frame)
            .into_iter()
            .flatten()
            .any(|&b| self.bindings_only(b, &mut HashSet::new()).is_some())
    }

    /// A call: each argument goes where the callee's summary says.
    fn call(&mut self, call: ExprId) {
        use EscapeLevel::*;
        let body = self.body;
        let callee = (*self.callees.get(&call).expect("a call")).clone();
        let (callee_expr, positional, fields) = call_args(body, call);
        let named: Vec<(Option<crag_hir::Name<'db>>, ExprId)> = fields
            .iter()
            .map(|f| match f {
                FieldArg::Field { path, value } if path.len() == 1 => (Some(path[0]), *value),
                FieldArg::Field { value, .. } | FieldArg::Spread(value) => (None, *value),
            })
            .collect();
        let summaries: Vec<ItemId<'db>> = match &callee {
            Callee::Function(f) => vec![*f],
            Callee::Instance(i) => vec![i.function],
            Callee::Dispatch(d) => d
                .arms
                .iter()
                .filter_map(|a| match &a.callee {
                    Callee::Function(f) => Some(*f),
                    Callee::Instance(i) => Some(i.function),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        };
        let known = !summaries.is_empty()
            && match &callee {
                Callee::Dispatch(d) => d
                    .arms
                    .iter()
                    .all(|a| matches!(a.callee, Callee::Function(_) | Callee::Instance(_))),
                _ => true,
            };
        if let Some(callee_expr) = callee_expr {
            // Called, not kept.
            self.walk(callee_expr, Local);
        }
        let stored = matches!(callee, Callee::Construct(_));
        let level_of = |this: &Self, position: Option<usize>, name: Option<crag_hir::Name<'db>>| {
            if stored || !known {
                return Escaping;
            }
            summaries
                .iter()
                .map(|&f| {
                    let names = (this.signature_of)(f);
                    let index = position
                        .or_else(|| name.and_then(|n| names.iter().position(|p| *p == Some(n))));
                    // A named argument that names no parameter builds a
                    // record, which keeps it.
                    match index {
                        Some(i) => (this.summary_of)(f).get(i).copied().unwrap_or(Escaping),
                        None => Escaping,
                    }
                })
                .max()
                .unwrap_or(Escaping)
        };
        for (i, &arg) in positional.iter().enumerate() {
            let level = level_of(self, Some(i), None);
            self.walk(arg, level);
        }
        for (name, value) in named {
            let level = level_of(self, None, name);
            self.walk(value, level);
        }
    }
}

/// The callee expression of a call, if it has one of its own, and its
/// positional arguments, the receiver first, and named ones.
fn call_args<'a, 'db>(
    body: &'a Body<'db>,
    call: ExprId,
) -> (Option<ExprId>, Vec<ExprId>, &'a [FieldArg<'db>]) {
    match body.expr(call) {
        Expr::Call {
            callee,
            args,
            fields,
        } => {
            // A declared function's name is no value to keep.
            let callee = match body.expr(*callee) {
                Expr::Name { local: None, .. } | Expr::TypeArgs { .. } => None,
                _ => Some(*callee),
            };
            (callee, args.clone(), fields.as_deref().unwrap_or_default())
        }
        Expr::TypedCall { args, fields, .. } => {
            (None, args.clone(), fields.as_deref().unwrap_or_default())
        }
        Expr::MethodCall {
            receiver,
            args,
            fields,
            ..
        } => {
            let positional = std::iter::once(*receiver)
                .chain(args.iter().copied())
                .collect();
            (None, positional, fields.as_deref().unwrap_or_default())
        }
        Expr::Field { receiver, .. } => (None, vec![*receiver], &[]),
        _ => (None, Vec::new(), &[]),
    }
}

/// The bindings a pattern binds.
fn pat_bindings(body: &Body, pat: PatId, out: &mut HashSet<BindingId>) {
    match body.pat(pat) {
        Pat::Bind { binding, sub } => {
            out.insert(*binding);
            if let Some(sub) = sub {
                pat_bindings(body, *sub, out);
            }
        }
        Pat::Record { fields, .. } => {
            for f in fields {
                pat_bindings(body, f.pat, out);
            }
        }
        Pat::List {
            before,
            rest,
            after,
        } => {
            for &p in before.iter().chain(after) {
                pat_bindings(body, p, out);
            }
            if let Some(Some(rest)) = rest {
                out.insert(*rest);
            }
        }
        Pat::Or(alternatives) => {
            for &p in alternatives {
                pat_bindings(body, p, out);
            }
        }
        Pat::Missing | Pat::Wildcard | Pat::Type(_) | Pat::Literal(_) | Pat::Range { .. } => {}
    }
}

/// The bindings declared anywhere inside an expression: by its
/// statements, closures, local functions and `case` arms.
fn declared_in(body: &Body, expr: ExprId) -> HashSet<BindingId> {
    let mut out = HashSet::new();
    let mut pending = vec![expr];
    while let Some(e) = pending.pop() {
        match body.expr(e) {
            Expr::Block { stmts, .. } => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { pat, .. }
                        | Stmt::LetElse { pat, .. }
                        | Stmt::For { pat, .. } => pat_bindings(body, *pat, &mut out),
                        Stmt::Bind { binding, .. } => {
                            out.insert(*binding);
                        }
                        Stmt::Fn { binding, function } => {
                            out.insert(*binding);
                            out.extend(function.params.iter().map(|p| p.binding));
                        }
                        _ => {}
                    }
                }
            }
            Expr::Closure { params, .. } => {
                for p in params {
                    pat_bindings(body, p.pat, &mut out);
                }
            }
            Expr::Case { arms, .. } => {
                for arm in arms {
                    pat_bindings(body, arm.pat, &mut out);
                }
            }
            _ => {}
        }
        pending.extend(body.children(e));
    }
    out
}
