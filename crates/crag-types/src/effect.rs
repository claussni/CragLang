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

//! Effects (Implementation Plan §11.5.7): what a function may do beyond
//! computing, `io`, `ref` and `signal` (§3.14).
//!
//! A function's effects are those of its body's operations and of what it
//! calls. A function that calls a closure parameter, or a slot of its
//! bounds, has an entry for it instead, which each call replaces with the
//! effects of the function actually passed or filled in. The effects of a
//! body are found by a walk over it once its calls are resolved; closures,
//! local functions and `lazy` expressions do not run where they are
//! written, so their effects count only where they are called. Recursive
//! groups solve their effects with their errors (§11.5.2).
//!
//! The walk also checks the contexts that restrict effects: `is Pure`
//! functions allow none, `atomic` blocks and `update` closures no `io`, an
//! `update` closure resolves no other ref, and an `ext` closure accesses no
//! other `ext` (§9.5, §9.6).

use std::collections::HashMap;

use crag_db::Db;
use crag_hir::{
    BindingId, BindingKind, Body, Expr, ExprId, FieldArg, ItemId, PRELUDE, Pat, Program, Stmt,
    c_function, hir_body,
};

use crate::def::signature;
use crate::generic::{Filling, Instance};
use crate::result::{Callee, ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// The effects of a function or a closure: the effects themselves, and
/// the closure parameters and slots whose effects it takes on.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct EffectSet {
    bits: u8,
    /// By the index of the function's parameter.
    params: u64,
    /// By the index of the function's slot (§11.5.3).
    slots: u64,
}

const IO: u8 = 1;
const REF: u8 = 2;
const SIGNAL: u8 = 4;
/// An `ext` access, which is `io` too; kept apart for the rule that an
/// `ext` closure accesses no other `ext` (§9.6).
const EXT: u8 = 8;

impl EffectSet {
    pub const NONE: EffectSet = EffectSet {
        bits: 0,
        params: 0,
        slots: 0,
    };

    /// What a function value of a plain function type may do (§3.14).
    pub fn all() -> EffectSet {
        EffectSet {
            bits: IO | REF | SIGNAL | EXT,
            ..EffectSet::NONE
        }
    }

    pub fn io() -> EffectSet {
        EffectSet {
            bits: IO,
            ..EffectSet::NONE
        }
    }

    fn of(bits: u8) -> EffectSet {
        EffectSet {
            bits,
            ..EffectSet::NONE
        }
    }

    /// The effects of the function passed for parameter `index`.
    pub fn param(index: usize) -> EffectSet {
        match index {
            0..64 => EffectSet {
                params: 1 << index,
                ..EffectSet::NONE
            },
            _ => EffectSet::all(),
        }
    }

    /// The effects of the function filling slot `index`.
    pub fn slot(index: usize) -> EffectSet {
        match index {
            0..64 => EffectSet {
                slots: 1 << index,
                ..EffectSet::NONE
            },
            _ => EffectSet::all(),
        }
    }

    pub fn union(self, other: EffectSet) -> EffectSet {
        EffectSet {
            bits: self.bits | other.bits,
            params: self.params | other.params,
            slots: self.slots | other.slots,
        }
    }

    pub fn is_empty(self) -> bool {
        self == EffectSet::NONE
    }

    /// Whether it has effects of its own, apart from its entries.
    pub fn has_effects(self) -> bool {
        self.bits != 0
    }

    pub fn has_io(self) -> bool {
        self.bits & IO != 0
    }

    pub fn has_ref(self) -> bool {
        self.bits & REF != 0
    }

    pub fn has_ext(self) -> bool {
        self.bits & EXT != 0
    }

    /// The effects with each entry replaced: what a call gives.
    pub fn substitute(
        self,
        params: &mut dyn FnMut(usize) -> EffectSet,
        slots: &mut dyn FnMut(usize) -> EffectSet,
    ) -> EffectSet {
        let mut out = EffectSet::of(self.bits);
        for i in 0..64 {
            if self.params & (1 << i) != 0 {
                out = out.union(params(i));
            }
            if self.slots & (1 << i) != 0 {
                out = out.union(slots(i));
            }
        }
        out
    }

    /// The effects of a function used as a value: its entries cannot be
    /// replaced, so they stand for any effect.
    pub fn closed(self) -> EffectSet {
        match self.params != 0 || self.slots != 0 {
            true => EffectSet::all(),
            false => self,
        }
    }

    /// Its effects and entries as text, as `io, param 0, slot 1`; `none`
    /// when it has neither.
    pub fn describe(self) -> String {
        let mut parts: Vec<String> = self.names().into_iter().map(String::from).collect();
        for i in 0..64 {
            if self.params & (1 << i) != 0 {
                parts.push(format!("param {i}"));
            }
        }
        for i in 0..64 {
            if self.slots & (1 << i) != 0 {
                parts.push(format!("slot {i}"));
            }
        }
        match parts.is_empty() {
            true => "none".into(),
            false => parts.join(", "),
        }
    }

    /// The names of its effects, for messages.
    pub fn names(self) -> Vec<&'static str> {
        let mut names = Vec::new();
        if self.bits & IO != 0 {
            names.push("io");
        }
        if self.bits & REF != 0 {
            names.push("ref");
        }
        if self.bits & SIGNAL != 0 {
            names.push("signal");
        }
        names
    }
}

/// A context that restricts effects (§3.14).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Restriction {
    Pure,
    Atomic,
    Update,
}

/// The effects of a function without a body: a C function does `io`
/// (§16.1), the prelude's access functions resolve their ref or access
/// their `ext` (§9.3), and every operation of the prelude calls the
/// functions passed to it. None for a function with a body.
pub fn intrinsic_effects<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
) -> Option<EffectSet> {
    if c_function(db, function).is_some() {
        return Some(EffectSet::io());
    }
    if hir_body(db, program, crag_hir::Owner::Item(function))
        .root
        .is_some()
    {
        return None;
    }
    let params = &signature(db, program, function).params;
    let mut effects = EffectSet::NONE;
    for (i, p) in params.iter().enumerate() {
        if matches!(p.ty.kind(db), TyKind::Fn { pure: false, .. }) {
            effects = effects.union(EffectSet::param(i));
        }
    }
    Some(effects.union(EffectSet::of(
        cell_access(db, program, function).map_or(0, |c| c.bits()),
    )))
}

/// The kind of cell a prelude access function reaches (§9.3).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Cell {
    Ref,
    Ext,
}

impl Cell {
    fn bits(self) -> u8 {
        match self {
            Cell::Ref => REF,
            Cell::Ext => IO | EXT,
        }
    }
}

fn cell_access<'db>(db: &'db dyn Db, program: Program, function: ItemId<'db>) -> Option<Cell> {
    if function.module(db).path(db) != PRELUDE
        || !matches!(
            function.name(db).text(db).as_str(),
            "use" | "update" | "swap" | "empty"
        )
    {
        return None;
    }
    match signature(db, program, function).params.first()?.ty.kind(db) {
        TyKind::Builtin(Builtin::Ref, _) => Some(Cell::Ref),
        TyKind::Builtin(Builtin::Ext, _) => Some(Cell::Ext),
        _ => None,
    }
}

/// One operation with effects in a body: where it is, what it does, and
/// the ref or `ext` binding it accesses directly.
#[derive(Clone, Copy)]
struct Occurrence {
    site: ExprId,
    effects: EffectSet,
    cell: Option<BindingId>,
}

/// The effects of a function body, with the errors of its restricted
/// contexts.
pub struct Walked<'db> {
    pub effects: EffectSet,
    pub errors: Vec<TypeError<'db>>,
}

/// Walks the body of a function, test or value.
pub struct Walker<'a, 'db> {
    pub db: &'db dyn Db,
    pub program: Program,
    pub body: &'a Body<'db>,
    pub exprs: &'a [Option<Ty<'db>>],
    pub bindings: &'a [Option<Ty<'db>>],
    pub callees: &'a [(ExprId, Callee<'db>)],
    /// The effects of a declared function: of its group's solution so
    /// far, or solved.
    pub effects_of: &'a dyn Fn(ItemId<'db>) -> EffectSet,
    by_expr: HashMap<ExprId, usize>,
    /// The value each simple `let` binds.
    values: HashMap<BindingId, ExprId>,
    /// The local function each binding names.
    local_fns: HashMap<BindingId, ExprId>,
    /// The effects of each closure and local function walked, with what
    /// it does where.
    deferred: HashMap<ExprId, (EffectSet, Vec<Occurrence>)>,
    errors: Vec<TypeError<'db>>,
}

impl<'a, 'db> Walker<'a, 'db> {
    pub fn new(
        db: &'db dyn Db,
        program: Program,
        body: &'a Body<'db>,
        exprs: &'a [Option<Ty<'db>>],
        bindings: &'a [Option<Ty<'db>>],
        callees: &'a [(ExprId, Callee<'db>)],
        effects_of: &'a dyn Fn(ItemId<'db>) -> EffectSet,
    ) -> Self {
        let by_expr = callees
            .iter()
            .enumerate()
            .map(|(i, (e, _))| (*e, i))
            .collect();
        let mut values = HashMap::new();
        let mut local_fns = HashMap::new();
        for expr in &body.exprs {
            let Expr::Block { stmts, .. } = expr else {
                continue;
            };
            for stmt in stmts {
                match stmt {
                    Stmt::Let { pat, value, .. } => {
                        if let Pat::Bind { binding, sub: None } = body.pat(*pat) {
                            values.insert(*binding, *value);
                        }
                    }
                    Stmt::Fn { binding, function } => {
                        if let Some(root) = function.body {
                            local_fns.insert(*binding, root);
                        }
                    }
                    _ => {}
                }
            }
        }
        Walker {
            db,
            program,
            body,
            exprs,
            bindings,
            callees,
            effects_of,
            by_expr,
            values,
            local_fns,
            deferred: HashMap::new(),
            errors: Vec::new(),
        }
    }

    /// The effects of the whole body, `is Pure` checked if it is marked
    /// so, and of every closure and local function in it, checked once.
    pub fn walk_body(mut self, pure: bool) -> Walked<'db> {
        let mut effects = EffectSet::NONE;
        if let Some(root) = self.body.root {
            let mut found = Vec::new();
            self.walk(root, &mut found);
            if pure {
                self.restrict(&found, Restriction::Pure);
            }
            effects = found
                .iter()
                .fold(EffectSet::NONE, |e, o| e.union(o.effects));
        }
        for (i, expr) in self.body.exprs.iter().enumerate() {
            if let Expr::Closure { .. } = expr {
                self.closure(ExprId(i as u32));
            }
        }
        let local: Vec<(ExprId, bool)> = self
            .body
            .exprs
            .iter()
            .flat_map(|e| match e {
                Expr::Block { stmts, .. } => stmts
                    .iter()
                    .filter_map(|s| match s {
                        Stmt::Fn { function, .. } => function.body.map(|b| (b, function.pure)),
                        _ => None,
                    })
                    .collect(),
                _ => Vec::new(),
            })
            .collect();
        for (root, pure) in local {
            self.local_fn(root, pure);
        }
        Walked {
            effects,
            errors: self.errors,
        }
    }

    /// The effects of a closure, walked once.
    pub fn closure(&mut self, closure: ExprId) -> EffectSet {
        if let Some((effects, _)) = self.deferred.get(&closure) {
            return *effects;
        }
        let Expr::Closure { body, .. } = self.body.expr(closure) else {
            return EffectSet::all();
        };
        self.deferred_walk(closure, *body, false)
    }

    fn local_fn(&mut self, root: ExprId, pure: bool) -> EffectSet {
        if let Some((effects, _)) = self.deferred.get(&root) {
            return *effects;
        }
        self.deferred_walk(root, root, pure)
    }

    fn deferred_walk(&mut self, key: ExprId, root: ExprId, pure: bool) -> EffectSet {
        // A recursive local function or closure sees itself as having no
        // more effects than the rest of its body.
        self.deferred.insert(key, (EffectSet::NONE, Vec::new()));
        let mut found = Vec::new();
        self.walk(root, &mut found);
        if pure {
            self.restrict(&found, Restriction::Pure);
        }
        let effects = found
            .iter()
            .fold(EffectSet::NONE, |e, o| e.union(o.effects));
        self.deferred.insert(key, (effects, found));
        effects
    }

    fn walk(&mut self, expr: ExprId, found: &mut Vec<Occurrence>) {
        let body = self.body;
        match body.expr(expr) {
            // Run where they are called or read.
            Expr::Closure { .. } | Expr::Lazy(_) => return,
            Expr::Block { stmts, tail } => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Fn { .. } | Stmt::On { .. } => {}
                        Stmt::Emit { value, .. } => {
                            self.walk(*value, found);
                            found.push(Occurrence {
                                site: *value,
                                effects: EffectSet::of(SIGNAL),
                                cell: None,
                            });
                        }
                        Stmt::Expr(e)
                        | Stmt::Let { value: e, .. }
                        | Stmt::Bind { value: e, .. }
                        | Stmt::Assign { value: e, .. } => self.walk(*e, found),
                        Stmt::LetElse {
                            value, otherwise, ..
                        } => {
                            self.walk(*value, found);
                            self.walk(*otherwise, found);
                        }
                        Stmt::For { iterable, body, .. } => {
                            self.walk(*iterable, found);
                            self.walk(*body, found);
                        }
                        Stmt::Return(e) => {
                            if let Some(e) = e {
                                self.walk(*e, found);
                            }
                        }
                    }
                }
                if let Some(tail) = tail {
                    self.walk(*tail, found);
                }
                return;
            }
            Expr::Atomic(inner) => {
                let mut inside = Vec::new();
                self.walk(*inner, &mut inside);
                self.restrict(&inside, Restriction::Atomic);
                found.extend(inside);
                return;
            }
            _ => {}
        }
        for child in body.children(expr) {
            self.walk(child, found);
        }
        if let Some(&i) = self.by_expr.get(&expr)
            && self.is_call(expr)
        {
            let callee = self.callees[i].1.clone();
            let effects = self.call(expr, &callee);
            if !effects.is_empty() {
                found.push(Occurrence {
                    site: expr,
                    effects,
                    cell: self.cell_of(expr, &callee),
                });
            }
        }
    }

    /// Whether a recorded callee is that of a call, not of a function
    /// named as a value.
    fn is_call(&self, expr: ExprId) -> bool {
        matches!(
            self.body.expr(expr),
            Expr::Call { .. }
                | Expr::MethodCall { .. }
                | Expr::TypedCall { .. }
                | Expr::Field { .. }
        )
    }

    /// The positional arguments of a call, its receiver first, and its
    /// named ones.
    fn args(&self, call: ExprId) -> (Vec<ExprId>, Vec<&'a FieldArg<'db>>) {
        let body = self.body;
        let (receiver, args, fields) = match body.expr(call) {
            Expr::Call { args, fields, .. } | Expr::TypedCall { args, fields, .. } => {
                (None, args.as_slice(), fields.as_deref())
            }
            Expr::MethodCall {
                receiver,
                args,
                fields,
                ..
            } => (Some(*receiver), args.as_slice(), fields.as_deref()),
            Expr::Field { receiver, .. } => (Some(*receiver), &[][..], None),
            _ => (None, &[][..], None),
        };
        let positional = receiver.into_iter().chain(args.iter().copied()).collect();
        (positional, fields.unwrap_or_default().iter().collect())
    }

    /// The arguments that go to each parameter of `function`.
    fn by_param(&self, call: ExprId, function: ItemId<'db>) -> Vec<Vec<ExprId>> {
        let params = &signature(self.db, self.program, function).params;
        let (positional, named) = self.args(call);
        let mut by_param = vec![Vec::new(); params.len()];
        for (i, arg) in positional.into_iter().enumerate() {
            if let Some(slot) = by_param.get_mut(i) {
                slot.push(arg);
            }
        }
        for field in named {
            let (path, value) = match field {
                FieldArg::Field { path, value } => (path.as_slice(), *value),
                FieldArg::Spread(value) => (&[][..], *value),
            };
            let named = match path {
                [name] => params.iter().position(|p| p.name == Some(*name)),
                _ => None,
            };
            // A named argument that names no parameter builds the last
            // one, a record (§5.6.2).
            if let Some(slot) = named
                .or(params.len().checked_sub(1))
                .and_then(|i| by_param.get_mut(i))
            {
                slot.push(value);
            }
        }
        by_param
    }

    /// The effects of a call.
    fn call(&mut self, call: ExprId, callee: &Callee<'db>) -> EffectSet {
        match callee {
            Callee::Function(f) => self.apply(call, *f, &[]),
            Callee::Instance(instance) => {
                self.apply(call, instance.function, &instance.fillings.clone())
            }
            Callee::Slot(k) => EffectSet::slot(*k as usize),
            Callee::Dispatch(dispatch) => dispatch
                .arms
                .iter()
                .map(|arm| arm.callee.clone())
                .collect::<Vec<_>>()
                .iter()
                .fold(EffectSet::NONE, |e, c| e.union(self.call(call, c))),
            Callee::Value => match self.body.expr(call) {
                Expr::Call { callee, .. } => self.value(*callee),
                _ => EffectSet::all(),
            },
            Callee::Construct(_) => EffectSet::NONE,
        }
    }

    /// The effects of calling `function` with the call's arguments and
    /// slot fillings. A call of an `is Pure` function must give it no
    /// effects through what it passes.
    fn apply(
        &mut self,
        call: ExprId,
        function: ItemId<'db>,
        fillings: &[Filling<'db>],
    ) -> EffectSet {
        let own = (self.effects_of)(function);
        let by_param = self.by_param(call, function);
        let mut args: Vec<EffectSet> = Vec::new();
        for exprs in &by_param {
            let e = exprs
                .iter()
                .fold(EffectSet::NONE, |e, &a| e.union(self.value(a)));
            args.push(e);
        }
        let mut slots: Vec<EffectSet> = Vec::new();
        for filling in fillings {
            slots.push(self.filling(filling));
        }
        let effects = own.substitute(
            &mut |i| args.get(i).copied().unwrap_or(EffectSet::NONE),
            &mut |k| slots.get(k).copied().unwrap_or_else(EffectSet::all),
        );
        if !effects.is_empty()
            && hir_body(self.db, self.program, crag_hir::Owner::Item(function)).pure
        {
            self.errors.push(TypeError {
                site: Site::Expr(call),
                kind: ErrorKind::PureCall { function },
            });
        }
        // Checked once the arguments are known: an `update` closure and
        // an `ext` closure.
        if let Some(cell) = cell_access(self.db, self.program, function) {
            let update = function.name(self.db).text(self.db) == "update";
            for exprs in by_param.iter().skip(1) {
                for &arg in exprs {
                    self.access_closure(arg, cell, update, by_param[0].first().copied());
                }
            }
        }
        effects
    }

    /// The effects of the function filling a slot.
    fn filling(&mut self, filling: &Filling<'db>) -> EffectSet {
        match filling {
            Filling::Slot(k) => EffectSet::slot(*k as usize),
            Filling::Function(Instance {
                function, fillings, ..
            }) => {
                let own = (self.effects_of)(*function);
                let mut slots = Vec::new();
                for f in fillings {
                    slots.push(self.filling(f));
                }
                own.substitute(&mut |_| EffectSet::all(), &mut |k| {
                    slots.get(k).copied().unwrap_or_else(EffectSet::all)
                })
            }
        }
    }

    /// The effects of calling a function value: a closure, a local
    /// function, a parameter, a declared function, or what its type
    /// admits.
    fn value(&mut self, expr: ExprId) -> EffectSet {
        let db = self.db;
        let body = self.body;
        match body.expr(expr) {
            Expr::Closure { .. } => return self.closure(expr),
            Expr::Record(fields) => {
                return fields.iter().fold(EffectSet::NONE, |e, f| {
                    let value = match f {
                        FieldArg::Field { value, .. } | FieldArg::Spread(value) => *value,
                    };
                    e.union(self.value(value))
                });
            }
            Expr::Name {
                local: Some(binding),
                ..
            } => {
                let binding = *binding;
                if self.is_pure(self.bindings.get(binding.index()).copied().flatten()) {
                    return EffectSet::NONE;
                }
                match body.binding(binding).kind {
                    BindingKind::Param => {
                        if let Some(i) = body.params.iter().position(|p| p.binding == binding) {
                            return EffectSet::param(i);
                        }
                    }
                    BindingKind::Fn => {
                        if let Some(&root) = self.local_fns.get(&binding) {
                            let pure = self.local_pure(root);
                            return self.local_fn(root, pure);
                        }
                    }
                    BindingKind::Let => {
                        if let Some(&value) = self.values.get(&binding) {
                            return self.value(value);
                        }
                    }
                    _ => {}
                }
            }
            Expr::Name { local: None, .. } => {
                if let Some(&i) = self.by_expr.get(&expr) {
                    let callee = self.callees[i].1.clone();
                    return match callee {
                        Callee::Function(f) => (self.effects_of)(f).closed(),
                        Callee::Instance(instance) => {
                            self.filling(&Filling::Function(instance)).closed()
                        }
                        Callee::Slot(k) => EffectSet::slot(k as usize),
                        Callee::Dispatch(dispatch) => {
                            dispatch.arms.iter().fold(EffectSet::NONE, |e, arm| {
                                e.union(match &arm.callee {
                                    Callee::Function(f) => (self.effects_of)(*f).closed(),
                                    _ => EffectSet::all(),
                                })
                            })
                        }
                        _ => EffectSet::all(),
                    };
                }
            }
            _ => {}
        }
        let ty = self.exprs.get(expr.index()).copied().flatten();
        match ty.map(|t| admits_effects(db, t)) {
            Some(false) | None => EffectSet::NONE,
            Some(true) => EffectSet::all(),
        }
    }

    fn is_pure(&self, ty: Option<Ty<'db>>) -> bool {
        ty.is_some_and(|t| matches!(t.kind(self.db), TyKind::Fn { pure: true, .. }))
    }

    fn local_pure(&self, root: ExprId) -> bool {
        self.body.exprs.iter().any(|e| match e {
            Expr::Block { stmts, .. } => stmts.iter().any(|s| {
                matches!(s, Stmt::Fn { function, .. } if function.body == Some(root) && function.pure)
            }),
            _ => false,
        })
    }

    /// The ref or `ext` binding an access function call reaches directly.
    fn cell_of(&self, call: ExprId, callee: &Callee<'db>) -> Option<BindingId> {
        let function = match callee {
            Callee::Function(f) => *f,
            Callee::Instance(i) => i.function,
            _ => return None,
        };
        cell_access(self.db, self.program, function)?;
        let (positional, _) = self.args(call);
        match self.body.expr(*positional.first()?) {
            Expr::Name {
                local: Some(binding),
                ..
            } => Some(*binding),
            _ => None,
        }
    }

    /// The rules of a closure passed to an access function: an `update`
    /// closure of a ref does no `io` and resolves no other ref (§9.5); a
    /// closure of an `ext` accesses no other `ext` (§9.6).
    fn access_closure(&mut self, arg: ExprId, cell: Cell, update: bool, receiver: Option<ExprId>) {
        let Expr::Closure { .. } = self.body.expr(arg) else {
            return;
        };
        self.closure(arg);
        let found = self
            .deferred
            .get(&arg)
            .map(|(_, f)| f.clone())
            .unwrap_or_default();
        let own = receiver.and_then(|r| match self.body.expr(r) {
            Expr::Name {
                local: Some(binding),
                ..
            } => Some(*binding),
            _ => None,
        });
        for o in found {
            match cell {
                Cell::Ref if update && o.effects.has_io() => {
                    self.restrict(&[o], Restriction::Update);
                }
                Cell::Ref
                    if update && o.effects.has_ref() && (o.cell.is_none() || o.cell != own) =>
                {
                    self.errors.push(TypeError {
                        site: Site::Expr(o.site),
                        kind: ErrorKind::SecondRef,
                    });
                }
                Cell::Ext if o.effects.has_ext() => {
                    self.errors.push(TypeError {
                        site: Site::Expr(o.site),
                        kind: ErrorKind::NestedExt,
                    });
                }
                _ => {}
            }
        }
    }

    /// Reports the effects a restricted context does not allow.
    fn restrict(&mut self, found: &[Occurrence], restriction: Restriction) {
        for o in found {
            let disallowed = match restriction {
                Restriction::Pure => o.effects.has_effects(),
                Restriction::Atomic | Restriction::Update => o.effects.has_io(),
            };
            if !disallowed {
                continue;
            }
            let effects = match restriction {
                Restriction::Pure => o.effects,
                _ => EffectSet::io(),
            };
            self.errors.push(TypeError {
                site: Site::Expr(o.site),
                kind: ErrorKind::Effect {
                    effects,
                    ext: o.effects.has_ext() && restriction != Restriction::Pure,
                    restriction,
                },
            });
        }
    }
}

/// Whether a value of `ty` may be a function with effects: a function
/// type without `Pure`, or a record or union holding one.
fn admits_effects<'db>(db: &'db dyn Db, ty: Ty<'db>) -> bool {
    match ty.kind(db) {
        TyKind::Fn { pure, .. } => !pure,
        TyKind::Record { fields, .. } => fields.iter().any(|&(_, t)| admits_effects(db, t)),
        TyKind::Union(members) => members.iter().any(|&m| admits_effects(db, m)),
        _ => false,
    }
}
