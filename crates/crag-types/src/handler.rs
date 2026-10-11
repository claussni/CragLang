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

//! Lifecycle handlers (Implementation Plan §11.6.11, Specification §11.4):
//! `on H f` on a nominal type, checked against the form its kind `H`
//! prescribes.
//!
//! A kind is a type spreading the prelude's `LifecycleHandler`, whose
//! `where HandlerForm[F]` gives the form: a function type, or a union of
//! them, in the kind's type parameter, which is the declaring type. The
//! handler names a function, and exactly one of its overloads must fit
//! exactly one member of the form; a form marked `is Pure` takes only a
//! function without effects. A type declares at most one handler of a kind.
//!
//! The declaring type of a generic type has its own parameters as its
//! arguments, so a handler fits every instance of it: a generic function
//! whose type arguments the form fixes, or one that takes no type
//! arguments and fits whatever the parameters are.

use crag_db::Db;
use crag_hir::{Expr, ItemId, ItemKind, Owner, Program, Resolution, TypeRef, TypeTarget, hir_body};

use crate::def::{TypeLowerer, prelude_item, signature, type_header};
use crate::generic::{CallSite, Instance, bind, instantiate};
use crate::group::{function_effects, result_type};
use crate::relate::{is_subtype, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Ty, TyKind};

/// A lifecycle handler a type declares: its kind, the function, and the
/// member of the kind's form the function fits. In a generic type both
/// may name the type's parameters.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Handler<'db> {
    pub kind: ItemId<'db>,
    /// The function with its type arguments.
    pub function: Instance<'db>,
    pub form: Ty<'db>,
}

impl<'db> Handler<'db> {
    /// The type of what the function gives, errors and all, with its type
    /// arguments in place.
    pub fn result(&self, db: &'db dyn Db, program: Program) -> Option<Ty<'db>> {
        let function = &self.function;
        let result = result_type(db, program, function.function)?;
        Some(match function.args.is_empty() {
            true => result,
            false => subst(db, program, result, function.function, &function.args),
        })
    }
}

/// The handlers of a type declaration, and what is wrong with its `on`
/// clauses.
#[derive(Clone, Debug, Default, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Handlers<'db> {
    pub handlers: Vec<Handler<'db>>,
    pub errors: Vec<TypeError<'db>>,
}

/// The lifecycle handlers a type declares.
#[crag_db::tracked(returns(ref))]
pub fn type_handlers<'db>(db: &'db dyn Db, program: Program, item: ItemId<'db>) -> Handlers<'db> {
    let mut out = Handlers::default();
    if *item.kind(db) != ItemKind::Type {
        return out;
    }
    let body = hir_body(db, program, Owner::Item(item));
    let Some(decl) = &body.type_decl else {
        return out;
    };
    let mut error = |site, kind| out.errors.push(TypeError { site, kind });
    for clause in &decl.handlers {
        let at = Site::Expr(clause.handler);
        // Structural types merge, and a merged type must not end up with
        // two handlers (§11.4).
        if !decl.distinct && !decl.opaque {
            error(Site::Name, ErrorKind::HandlerOnStructural);
            continue;
        }
        let params = (0..type_header(db, program, item).params.len() as u32)
            .zip(&type_header(db, program, item).params)
            .map(|(i, &name)| Ty::new(db, TyKind::Param(Some(item), i, name)))
            .collect();
        let declaring = Ty::new(db, TyKind::Named(item, params));
        let kind = match body.type_ref(clause.kind) {
            TypeRef::Named {
                target: TypeTarget::Item(kind),
                args,
                ..
            } if args.is_empty() => *kind,
            TypeRef::Missing => continue,
            _ => {
                error(Site::Type(clause.kind), ErrorKind::NotALifecycleKind);
                continue;
            }
        };
        let Some(form) = handler_form(db, program, kind, declaring) else {
            error(Site::Type(clause.kind), ErrorKind::NotALifecycleKind);
            continue;
        };
        if out.handlers.iter().any(|h| h.kind == kind) {
            error(
                at,
                ErrorKind::SecondHandler {
                    kind: *kind.name(db),
                },
            );
            continue;
        }
        let functions = match body.expr(clause.handler) {
            Expr::Name {
                local: None,
                item: Some(Resolution::Value { functions, .. }),
                ..
            } if !functions.is_empty() => functions.clone(),
            Expr::Missing | Expr::Name { item: None, .. } => continue,
            _ => {
                error(
                    at,
                    ErrorKind::Unsupported("lifecycle handlers that are not named functions"),
                );
                continue;
            }
        };
        let name = *functions[0].name(db);
        let at_type = CallSite {
            module: *item.module(db),
            caller: None,
        };
        let mut fits = Vec::new();
        for &function in &functions {
            for &member in &form.members {
                if let Some(instance) = fit(db, program, function, member, at_type) {
                    fits.push((instance, member));
                }
            }
        }
        match &fits[..] {
            [(function, member)] => {
                let (function, member) = (function.clone(), *member);
                if form.pure && function_effects(db, program, function.function).has_effects() {
                    error(
                        at,
                        ErrorKind::HandlerNotPure {
                            kind: *kind.name(db),
                            name,
                        },
                    );
                    continue;
                }
                out.handlers.push(Handler {
                    kind,
                    function,
                    form: member,
                });
            }
            [] => error(
                at,
                ErrorKind::HandlerDoesNotFit {
                    kind: *kind.name(db),
                    name,
                    form: form.ty,
                },
            ),
            _ => error(
                at,
                ErrorKind::Ambiguous {
                    name,
                    candidates: fits.iter().map(|f| f.0.function).collect(),
                },
            ),
        }
    }
    out
}

/// The handler of a kind of the prelude, by its name, that a type
/// declares, for the type's arguments: none for a type that is not
/// nominal or declares none.
pub fn lifecycle_handler<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    kind: &str,
) -> Option<Handler<'db>> {
    let TyKind::Named(item, args) = ty.kind(db) else {
        return None;
    };
    let kind = prelude_item(db, program, kind)?;
    let handler = type_handlers(db, program, *item)
        .handlers
        .iter()
        .find(|h| h.kind == kind)?;
    if args.is_empty() {
        return Some(handler.clone());
    }
    // The fillings of the function's slots depend on its type arguments,
    // so it is instantiated again.
    let function = &handler.function;
    let function_args: Vec<Ty<'db>> = function
        .args
        .iter()
        .map(|&t| subst(db, program, t, *item, args))
        .collect();
    let at_type = CallSite {
        module: *item.module(db),
        caller: None,
    };
    Some(Handler {
        kind,
        function: instantiate(db, program, function.function, &function_args, at_type).ok()?,
        form: subst(db, program, handler.form, *item, args),
    })
}

/// The instance of `function` that fits a member of a form, if one does:
/// a generic function takes the type arguments the member fixes.
fn fit<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
    member: Ty<'db>,
    at: CallSite<'db>,
) -> Option<Instance<'db>> {
    let ty = function_type(db, program, function)?;
    let count = signature(db, program, function).type_params;
    let mut args = vec![None; count];
    // The function may give less than the form allows, such as no error
    // at all, so its result meets each member of the form's.
    if let (
        TyKind::Fn { params, result, .. },
        TyKind::Fn {
            params: form_params,
            result: form_result,
            ..
        },
    ) = (ty.kind(db), member.kind(db))
    {
        for (&p, &f) in params.iter().zip(form_params) {
            bind(db, program, function, p, f, &mut args);
        }
        for m in form_result.members(db) {
            bind(db, program, function, *result, m, &mut args);
        }
    }
    let args: Vec<Ty<'db>> = args.into_iter().collect::<Option<_>>()?;
    let ty = match count {
        0 => ty,
        _ => subst(db, program, ty, function, &args),
    };
    if !is_subtype(db, program, ty, member) {
        return None;
    }
    instantiate(db, program, function, &args, at).ok()
}

/// The form of a kind's handlers for a declaring type.
struct Form<'db> {
    ty: Ty<'db>,
    members: Vec<Ty<'db>>,
    pure: bool,
}

/// The form a lifecycle kind prescribes for the handlers of `declaring`:
/// none when `kind` spreads no `LifecycleHandler` or has no form.
fn handler_form<'db>(
    db: &'db dyn Db,
    program: Program,
    kind: ItemId<'db>,
    declaring: Ty<'db>,
) -> Option<Form<'db>> {
    let lifecycle = prelude_item(db, program, "LifecycleHandler")?;
    if type_header(db, program, kind).params.len() != 1 {
        return None;
    }
    let kind_ty = Ty::new(db, TyKind::Named(kind, vec![declaring]));
    let parent = Ty::new(db, TyKind::Named(lifecycle, Vec::new()));
    if !is_subtype(db, program, kind_ty, parent) {
        return None;
    }
    let body = hir_body(db, program, Owner::Item(kind));
    let form = body.type_decl.as_ref()?.form.as_ref()?;
    let mut lower = TypeLowerer::new(db, program, body, Some(kind));
    let ty = subst(db, program, lower.lower(form.ty), kind, &[declaring]);
    let members = ty.members(db);
    if !members
        .iter()
        .all(|m| matches!(m.kind(db), TyKind::Fn { .. }))
    {
        return None;
    }
    Some(Form {
        ty,
        members,
        pure: form.pure,
    })
}

/// The type of a function as a value, with its whole result, errors and
/// all, in its own type parameters.
fn function_type<'db>(db: &'db dyn Db, program: Program, function: ItemId<'db>) -> Option<Ty<'db>> {
    let sig = signature(db, program, function);
    let result = result_type(db, program, function)?;
    let params = sig.params.iter().map(|p| p.ty).collect();
    Some(Ty::new(
        db,
        TyKind::Fn {
            params,
            result,
            pure: false,
        },
    ))
}
