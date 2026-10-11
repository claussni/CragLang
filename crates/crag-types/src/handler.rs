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

use crag_db::Db;
use crag_hir::{Expr, ItemId, ItemKind, Owner, Program, Resolution, TypeRef, TypeTarget, hir_body};

use crate::def::{TypeLowerer, prelude_item, signature, type_header};
use crate::group::{function_effects, result_type};
use crate::relate::{is_subtype, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Ty, TyKind};

/// A lifecycle handler a type declares: its kind, the function, and the
/// member of the kind's form the function fits.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Handler<'db> {
    pub kind: ItemId<'db>,
    pub function: ItemId<'db>,
    pub form: Ty<'db>,
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
        if !type_header(db, program, item).params.is_empty() {
            error(
                at,
                ErrorKind::Unsupported("lifecycle handlers of generic types"),
            );
            continue;
        }
        let declaring = Ty::new(db, TyKind::Named(item, Vec::new()));
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
        let mut fits = Vec::new();
        for &function in &functions {
            let Some(ty) = function_type(db, program, function) else {
                continue;
            };
            for &member in &form.members {
                if is_subtype(db, program, ty, member) {
                    fits.push((function, member));
                }
            }
        }
        match fits[..] {
            [(function, member)] => {
                if form.pure && function_effects(db, program, function).has_effects() {
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
                    candidates: fits.iter().map(|f| f.0).collect(),
                },
            ),
        }
    }
    out
}

/// The handler of a kind of the prelude, by its name, that a type
/// declares: none for a type that is not nominal or declares none.
pub fn lifecycle_handler<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    kind: &str,
) -> Option<&'db Handler<'db>> {
    let TyKind::Named(item, args) = ty.kind(db) else {
        return None;
    };
    if !args.is_empty() {
        return None;
    }
    let kind = prelude_item(db, program, kind)?;
    type_handlers(db, program, *item)
        .handlers
        .iter()
        .find(|h| h.kind == kind)
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
/// all; none for a generic function.
fn function_type<'db>(db: &'db dyn Db, program: Program, function: ItemId<'db>) -> Option<Ty<'db>> {
    let sig = signature(db, program, function);
    if sig.type_params > 0 {
        return None;
    }
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
