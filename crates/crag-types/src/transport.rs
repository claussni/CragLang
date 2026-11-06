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

//! What a closure literal sent as an `Expr` may hold (Specification §18.6,
//! Implementation Plan §11.10.13). Its body is `Pure` and its captures
//! `Solid`, which inference checks against `F`; here are the rest: no
//! `ref` or `ext`, as bindings or captures, no `atomic`, `embed` or `on`
//! handler, no `???`, and no capture that holds a `Secret`. A module value
//! the body reads is a capture too, and checked as one. Once the module is
//! inferred, the tree may name no private `distinct` or `opaque` type,
//! itself or through the helpers it bundles.

use crag_db::Db;
use crag_hir::{
    BindingKind, Body, Expr, ExprId, ItemId, Owner, Pat, PatId, Program, Resolution, Stmt,
    TypeRefId, hir_body,
};

use crate::def::{is_public, signature, type_def, value_type};
use crate::marker::{holds_secret, solid};
use crate::result::{Callee, ErrorKind, InferenceResult, Site, TypeError};
use crate::ty::{Ty, TyKind};
use crate::{body_types, result_type};

/// A form that code sent as an `Expr` may not hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Untransported {
    Ref,
    Ext,
    Dur,
    Atomic,
    Embed,
    On,
    Hole,
}

impl Untransported {
    pub fn text(self) -> &'static str {
        match self {
            Untransported::Ref => "a `ref` binding",
            Untransported::Ext => "an `ext` binding",
            Untransported::Dur => "a `dur` binding",
            Untransported::Atomic => "an `atomic` block",
            Untransported::Embed => "an `embed`",
            Untransported::On => "an `on` handler",
            Untransported::Hole => "`???`, which can only trap",
        }
    }
}

/// The errors of a closure literal sent as an `Expr`, its nested closures
/// and local functions included. `bindings` are the types inferred so far.
pub(crate) fn literal_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &Body<'db>,
    bindings: &[Option<Ty<'db>>],
    closure: ExprId,
) -> Vec<TypeError<'db>> {
    let mut errors = Vec::new();
    let mut error = |site, kind| errors.push(TypeError { site, kind });
    let mut pending = vec![closure];
    while let Some(e) = pending.pop() {
        let form = match body.expr(e) {
            Expr::Atomic(_) => Some(Untransported::Atomic),
            Expr::Embed => Some(Untransported::Embed),
            Expr::Hole => Some(Untransported::Hole),
            Expr::Block { stmts, .. } => {
                for stmt in stmts {
                    let (site, form) = match stmt {
                        Stmt::Bind { binding, .. } => match body.binding(*binding).kind {
                            BindingKind::Ref => (Site::Binding(*binding), Untransported::Ref),
                            BindingKind::Ext => (Site::Binding(*binding), Untransported::Ext),
                            BindingKind::Dur => (Site::Binding(*binding), Untransported::Dur),
                            _ => continue,
                        },
                        Stmt::On { handler, .. } => (Site::Expr(*handler), Untransported::On),
                        _ => continue,
                    };
                    error(site, ErrorKind::NotTransportable { form });
                }
                None
            }
            _ => None,
        };
        if let Some(form) = form {
            error(Site::Expr(e), ErrorKind::NotTransportable { form });
        }
        pending.extend(body.children(e).into_iter().rev());
    }
    for binding in body.free_bindings(closure) {
        let declared = body.binding(binding);
        let Some(name) = declared.name else {
            continue;
        };
        match declared.kind {
            kind @ (BindingKind::Ref | BindingKind::Ext | BindingKind::Dur) => {
                error(Site::Expr(closure), ErrorKind::CellCapture { name, kind });
            }
            // A local function is code, which the tree does not bundle.
            BindingKind::Fn => {
                error(Site::Expr(closure), ErrorKind::OuterFunction { name });
            }
            _ => {
                let ty = bindings.get(binding.index()).copied().flatten();
                if let Some(ty) = ty
                    && let Some(path) = holds_secret(db, program, ty)
                {
                    error(
                        Site::Expr(closure),
                        ErrorKind::SecretCapture {
                            name,
                            ty,
                            path: path.clone(),
                        },
                    );
                }
            }
        }
    }
    // A module value the body reads is a capture too, read when the
    // `Expr` is made (§18.6), so it is checked as one: a session's values
    // need not be Solid.
    for (value, at) in module_values(body, closure) {
        let Expr::Name { name, .. } = body.expr(at) else {
            continue;
        };
        let Some(ty) = value_type(db, program, value) else {
            continue;
        };
        if let Err(why) = solid(db, program, ty) {
            let kind = ErrorKind::PureCapture {
                name: *name,
                ty,
                why: why.clone(),
            };
            error(Site::Expr(at), kind);
        } else if let Some(path) = holds_secret(db, program, ty) {
            let kind = ErrorKind::SecretCapture {
                name: *name,
                ty,
                path: path.clone(),
            };
            error(Site::Expr(at), kind);
        }
    }
    errors
}

/// The private `distinct` and `opaque` types the tree of each closure
/// literal sent as an `Expr` in `owner` would name, its helpers' included:
/// a receiver can only resolve a type by its declaring module, and never
/// another module's private names (§18.6, Implementation Plan §11.10.11).
/// The types are those the tree spells: written types, type names,
/// constructions, type arguments, captures and module values, and the
/// signatures and bodies of the helpers it bundles. Each is reported once
/// per literal, where it is first named, or at the call that first
/// reaches the helper naming it.
pub(crate) fn private_type_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
) -> Vec<TypeError<'db>> {
    let result = body_types(db, program, owner);
    let body = hir_body(db, program, owner);
    let mut errors = Vec::new();
    for &closure in &result.sent {
        if !matches!(body.expr(closure), Expr::Closure { .. }) {
            continue;
        }
        let mut found = Found::default();
        for binding in body.free_bindings(closure) {
            if let Some(ty) = result.binding(binding) {
                found.ty(db, program, ty, Site::Expr(closure), None);
            }
        }
        for (value, at) in module_values(body, closure) {
            if let Some(ty) = value_type(db, program, value) {
                found.ty(db, program, ty, Site::Expr(at), None);
            }
        }
        let mut helpers = Vec::new();
        spelled(db, body, result, closure, &mut |ty, at, callee| {
            if let Some(f) = callee
                && !helpers.iter().any(|&(h, _)| h == f)
            {
                helpers.push((f, at));
            }
            if let Some(ty) = ty {
                found.ty(db, program, ty, at, None);
            }
        });
        // The helpers the tree bundles, those they reach too, each
        // reported at the call in the literal that reaches it first.
        let mut next = 0;
        while next < helpers.len() {
            let (helper, at) = helpers[next];
            next += 1;
            let owner = Owner::Item(helper);
            let sig = signature(db, program, helper);
            let mut types: Vec<Ty<'db>> = sig.params.iter().map(|p| p.ty).collect();
            types.extend(result_type(db, program, helper));
            for ty in types {
                found.ty(db, program, ty, at, Some(helper));
            }
            let hbody = hir_body(db, program, owner);
            let hresult = body_types(db, program, owner);
            let roots = hbody
                .params
                .iter()
                .filter_map(|p| p.default)
                .chain(hbody.root);
            for root in roots {
                spelled(db, hbody, hresult, root, &mut |ty, _, callee| {
                    if let Some(f) = callee
                        && !helpers.iter().any(|&(h, _)| h == f)
                    {
                        helpers.push((f, at));
                    }
                    if let Some(ty) = ty {
                        found.ty(db, program, ty, at, Some(helper));
                    }
                });
            }
        }
        errors.extend(found.errors);
    }
    errors
}

/// The private types found so far for one literal, each once.
#[derive(Default)]
struct Found<'db> {
    seen: Vec<ItemId<'db>>,
    errors: Vec<TypeError<'db>>,
}

impl<'db> Found<'db> {
    /// Reports the private `distinct` and `opaque` types `ty` names: as a
    /// tree spells a type, a named one by its reference and its arguments.
    fn ty(
        &mut self,
        db: &'db dyn Db,
        program: Program,
        ty: Ty<'db>,
        site: Site,
        helper: Option<ItemId<'db>>,
    ) {
        match ty.kind(db) {
            TyKind::Error | TyKind::Param(..) => {}
            TyKind::Builtin(_, args) => {
                for &t in args {
                    self.ty(db, program, t, site, helper);
                }
            }
            TyKind::Named(item, args) => {
                let def = type_def(db, program, *item);
                if (def.distinct || def.opaque)
                    && !is_public(db, *item)
                    && !self.seen.contains(item)
                {
                    self.seen.push(*item);
                    let kind = ErrorKind::PrivateTypeSent {
                        ty: *item,
                        opaque: def.opaque,
                        helper,
                    };
                    self.errors.push(TypeError { site, kind });
                }
                for &t in args {
                    self.ty(db, program, t, site, helper);
                }
            }
            TyKind::Record { fields, .. } => {
                for &(_, t) in fields {
                    self.ty(db, program, t, site, helper);
                }
            }
            TyKind::Fn { params, result, .. } => {
                for &t in params.iter().chain([result]) {
                    self.ty(db, program, t, site, helper);
                }
            }
            TyKind::Union(members) => {
                for &t in members {
                    self.ty(db, program, t, site, helper);
                }
            }
        }
    }
}

/// Walks what the tree of `root` spells, in a pre-order walk: `found`
/// gets each type it names with the expression that names it, and each
/// function it would bundle as a helper.
fn spelled<'db>(
    db: &'db dyn Db,
    body: &Body<'db>,
    result: &InferenceResult<'db>,
    root: ExprId,
    found: &mut dyn FnMut(Option<Ty<'db>>, Site, Option<ItemId<'db>>),
) {
    let written = |t: TypeRefId| {
        let ty = result.types.get(t.index()).copied().flatten();
        (ty, Site::Type(t))
    };
    let mut pending = vec![root];
    while let Some(e) = pending.pop() {
        let mut types: Vec<(Option<Ty<'db>>, Site)> = Vec::new();
        let mut pats: Vec<PatId> = Vec::new();
        match body.expr(e) {
            Expr::Name {
                local: None,
                item: Some(Resolution::Type(_)),
                ..
            } => types.push((result.expr(e), Site::Expr(e))),
            Expr::Is { ty, .. } => types.push(written(*ty)),
            Expr::Closure { params, .. } => {
                for p in params {
                    pats.push(p.pat);
                    types.extend(p.ty.map(written));
                }
            }
            Expr::Case { arms, .. } => pats.extend(arms.iter().map(|a| a.pat)),
            Expr::Block { stmts, .. } => {
                for stmt in stmts {
                    match stmt {
                        Stmt::Let { pat, ty, .. } => {
                            pats.push(*pat);
                            types.extend(ty.map(written));
                        }
                        Stmt::LetElse { pat, ty, rest, .. } => {
                            pats.push(*pat);
                            pats.extend(*rest);
                            types.extend(ty.map(written));
                        }
                        Stmt::Bind { ty, .. } => types.extend(ty.map(written)),
                        Stmt::For { pat, .. } => pats.push(*pat),
                        Stmt::Fn { function, .. } => {
                            types.extend(function.params.iter().map(|p| written(p.ty)));
                            types.extend(function.result.map(written));
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        while let Some(p) = pats.pop() {
            match body.pat(p) {
                Pat::Bind { sub, .. } => pats.extend(*sub),
                Pat::Type(t) => types.push(written(*t)),
                Pat::Record { ty, fields } => {
                    types.extend(ty.map(written));
                    pats.extend(fields.iter().map(|f| f.pat));
                }
                Pat::List { before, after, .. } => {
                    pats.extend(before.iter().chain(after).copied());
                }
                Pat::Or(alternatives) => pats.extend(alternatives.iter().copied()),
                _ => {}
            }
        }
        let callee = match result.callee(e) {
            Some(Callee::Construct(ty) | Callee::Refine(ty)) => {
                types.push((Some(*ty), Site::Expr(e)));
                None
            }
            Some(Callee::Function(f)) => Some(*f),
            Some(Callee::Instance(instance)) => {
                types.extend(instance.args.iter().map(|&t| (Some(t), Site::Expr(e))));
                Some(instance.function)
            }
            _ => None,
        };
        let helper = callee.filter(|&f| !is_public(db, f));
        if helper.is_some() {
            found(None, Site::Expr(e), helper);
        }
        for (ty, site) in types {
            found(ty, site, None);
        }
        pending.extend(body.children(e).into_iter().rev());
    }
}

/// The module values the body of a closure sent as an `Expr` reads, each
/// with where it is first read, in that order: its captures after those
/// of its bindings, in its environment and its tree alike (§18.6).
pub fn module_values<'db>(body: &Body<'db>, closure: ExprId) -> Vec<(ItemId<'db>, ExprId)> {
    let mut out: Vec<(ItemId<'db>, ExprId)> = Vec::new();
    let mut pending = vec![closure];
    while let Some(e) = pending.pop() {
        if let Expr::Name {
            local: None,
            item: Some(Resolution::Value {
                value: Some(value), ..
            }),
            ..
        } = body.expr(e)
            && !out.iter().any(|(v, _)| v == value)
        {
            out.push((*value, e));
        }
        pending.extend(body.children(e).into_iter().rev());
    }
    out
}
