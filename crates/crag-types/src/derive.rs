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

//! Which types the prelude's derived forms fit (Specification §19.11).
//!
//! The prelude's generic `equals`, `compare`, `hash` and `show` serve a
//! type through its structure: a record when each of its fields fits the
//! form, by functions of its own or by its structure in turn, a union when
//! each of its members does (§18.2). Function types fit none of the four,
//! an `opaque` type shows no fields outside its module, and a type that is
//! `not F` never fits `F`, through a field neither (§3.11).

use crag_db::Db;
use crag_hir::{
    ItemId, ItemKind, ModuleId, Name, Owner, PRELUDE, Program, Resolution, hir_body, item_tree,
    module_scope,
};

use crate::def::signature;
use crate::generic::form_def;
use crate::relate::{fields_of, parent};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// The form a prelude function derives, by its name, and back.
const DERIVED: [(&str, &str); 4] = [
    ("equals", "Eq"),
    ("compare", "Ordered"),
    ("hash", "Hash"),
    ("show", "Show"),
];

/// Whether a type forbids the form named `form`, itself or through a
/// parent (§3.11).
pub fn bans(db: &dyn Db, program: Program, ty: Ty<'_>, form: &str) -> bool {
    let mut current = Some(ty);
    while let Some(t) = current {
        if let TyKind::Named(item, _) = t.kind(db) {
            let body = hir_body(db, program, Owner::Item(*item));
            let banned = body.type_decl.as_ref().is_some_and(|d| {
                d.markers
                    .iter()
                    .any(|(name, negated)| *negated && name.text(db) == form)
            });
            if banned {
                return true;
            }
        }
        current = parent(db, program, t);
    }
    false
}

/// Whether one of the prelude's derived functions may serve these type
/// arguments where `at` calls it; otherwise the form and the type.
pub(crate) fn derivable<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
    args: &[Ty<'db>],
    at: ModuleId,
) -> Result<(), (&'static str, Ty<'db>)> {
    if function.module(db).path(db) != PRELUDE {
        return Ok(());
    }
    let name = function.name(db).text(db);
    let Some(&(_, form)) = DERIVED.iter().find(|(f, _)| f == name) else {
        return Ok(());
    };
    if signature(db, program, function).type_params != 1 {
        return Ok(());
    }
    match args.first() {
        Some(&ty) if !derives(db, program, form, ty, at, &mut Vec::new()) => Err((form, ty)),
        _ => Ok(()),
    }
}

/// Whether a type fits a derived form by its structure.
fn derives<'db>(
    db: &'db dyn Db,
    program: Program,
    form: &str,
    ty: Ty<'db>,
    at: ModuleId,
    seen: &mut Vec<Ty<'db>>,
) -> bool {
    if seen.contains(&ty) {
        return true;
    }
    if bans(db, program, ty, form) {
        return false;
    }
    let parts = |seen: &mut Vec<Ty<'db>>, parts: Vec<Ty<'db>>| {
        seen.push(ty);
        parts
            .into_iter()
            .all(|t| fits(db, program, form, t, at, seen))
    };
    match ty.kind(db) {
        TyKind::Error | TyKind::Param(..) => true,
        TyKind::Fn { .. } => false,
        TyKind::Union(members) => parts(seen, members.clone()),
        TyKind::Record { fields, .. } => parts(seen, fields.iter().map(|(_, t)| *t).collect()),
        TyKind::Builtin(builtin, args) => match builtin {
            Builtin::List | Builtin::Grid => parts(seen, args.clone()),
            // Maps and sets have no order.
            Builtin::Map | Builtin::Set => form != "Ordered" && parts(seen, args.clone()),
            Builtin::Ref | Builtin::Ext | Builtin::Lazy => false,
            _ => true,
        },
        TyKind::Named(item, _) => {
            // Outside its module, an opaque type exposes no fields.
            let opaque = hir_body(db, program, Owner::Item(*item))
                .type_decl
                .as_ref()
                .is_some_and(|d| d.opaque);
            if opaque && *item.module(db) != at {
                return false;
            }
            match fields_of(db, program, ty) {
                Some(fields) => parts(seen, fields.into_iter().map(|(_, t)| t).collect()),
                None => true,
            }
        }
    }
}

/// Whether a part of a type fits a derived form: by a function of its own
/// where `at` is, or by its structure.
fn fits<'db>(
    db: &'db dyn Db,
    program: Program,
    form: &str,
    ty: Ty<'db>,
    at: ModuleId,
    seen: &mut Vec<Ty<'db>>,
) -> bool {
    !bans(db, program, ty, form)
        && (own_function(db, program, form, ty, at) || derives(db, program, form, ty, at, seen))
}

/// Whether a function of the form's, not the derived one, takes exactly
/// the type where `at` is.
fn own_function(db: &dyn Db, program: Program, form: &str, ty: Ty<'_>, at: ModuleId) -> bool {
    let Some(&(slot, _)) = DERIVED.iter().find(|(_, f)| *f == form) else {
        return false;
    };
    let name = Name::new(db, slot.to_string());
    let Some(Resolution::Value { functions, .. }) = module_scope(db, program, at).resolve(name)
    else {
        return false;
    };
    functions.iter().any(|&f| {
        let sig = signature(db, program, f);
        sig.type_params == 0 && sig.params.first().is_some_and(|p| p.ty == ty)
    })
}

/// The functions of a module that would make a type fit a form it forbids:
/// one of the form's functions by name whose first parameter is the type
/// (§3.11).
pub(crate) fn ban_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(ItemId<'db>, TypeError<'db>)> {
    let scope = module_scope(db, program, module);
    let forms: Vec<ItemId<'db>> = scope
        .names
        .values()
        .filter_map(|r| match r {
            Resolution::Form(form) => Some(*form),
            _ => None,
        })
        .collect();
    let mut errors = Vec::new();
    for item in &item_tree(db, module).items {
        let function = item.id;
        if *function.kind(db) != ItemKind::Function {
            continue;
        }
        let Some(first) = signature(db, program, function)
            .params
            .first()
            .map(|p| p.ty)
        else {
            continue;
        };
        for &form in &forms {
            let slot = form_def(db, program, form)
                .slots
                .iter()
                .any(|s| s.name(db) == function.name(db));
            let name = form.name(db).text(db);
            if slot && bans(db, program, first, name) {
                let kind = ErrorKind::FitsBanned {
                    ty: first,
                    form: name.clone(),
                };
                errors.push((
                    function,
                    TypeError {
                        site: Site::Name,
                        kind,
                    },
                ));
            }
        }
    }
    errors
}
