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

use crate::def::{TypeDefKind, signature, type_def};
use crate::generic::{CallSite, Filling, Instance, form_def, own_filling};
use crate::relate::{fields_of, parent, record_subtypes, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// The form a prelude function derives, by its name, and back.
const DERIVED: [(&str, &str); 4] = [
    ("equals", "Eq"),
    ("compare", "Ordered"),
    ("hash", "Hash"),
    ("show", "Show"),
];

/// One of the prelude's derived functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Derived {
    Equals,
    Compare,
    Hash,
    Show,
}

impl Derived {
    /// The function's name.
    pub fn name(self) -> &'static str {
        match self {
            Derived::Equals => "equals",
            Derived::Compare => "compare",
            Derived::Hash => "hash",
            Derived::Show => "show",
        }
    }

    /// How many values it takes.
    pub fn arity(self) -> usize {
        match self {
            Derived::Equals | Derived::Compare => 2,
            Derived::Hash | Derived::Show => 1,
        }
    }
}

/// The prelude's generic function the form derives, which serves every
/// type by its structure.
fn derived_function<'db>(db: &'db dyn Db, program: Program, op: Derived) -> Option<ItemId<'db>> {
    let module = *crag_hir::module_index(db, program).modules.get(PRELUDE)?;
    let name = Name::new(db, op.name().to_string());
    let Some(Resolution::Value { functions, .. }) = module_scope(db, program, module).resolve(name)
    else {
        return None;
    };
    functions.iter().copied().find(|&f| {
        let sig = signature(db, program, f);
        sig.type_params == 1
            && sig
                .params
                .first()
                .is_some_and(|p| matches!(p.ty.kind(db), TyKind::Param(..)))
    })
}

/// A named type's own function of a derived form, as the module that
/// declares the type sees it: the most specific function there that takes
/// the type, unless that is the prelude's derived one (§19.11).
pub fn own_derived<'db>(
    db: &'db dyn Db,
    program: Program,
    op: Derived,
    ty: Ty<'db>,
) -> Option<Instance<'db>> {
    let TyKind::Named(item, _) = ty.kind(db) else {
        return None;
    };
    let result = signature(db, program, derived_function(db, program, op)?).result?;
    let at = CallSite {
        module: *item.module(db),
        caller: None,
    };
    match own_filling(db, program, op.name(), &vec![ty; op.arity()], result, at)? {
        Filling::Function(instance) => Some(instance),
        Filling::Slot(_) => None,
    }
}

/// Whether the derived function of a form, for a type, meets a part of a
/// value with a function of its own: a field, a member, an element, a
/// map's value, or a subtype's value of a record type. Without one, it
/// walks the value by its structure alone (Plan §11.6.5). Map keys and set
/// members are found by their structure, so they count only for `show`.
pub fn reaches_own<'db>(db: &'db dyn Db, program: Program, op: Derived, ty: Ty<'db>) -> bool {
    reaches(db, program, op, ty, &mut Vec::new())
}

fn reaches<'db>(
    db: &'db dyn Db,
    program: Program,
    op: Derived,
    ty: Ty<'db>,
    seen: &mut Vec<Ty<'db>>,
) -> bool {
    if seen.contains(&ty) {
        return false;
    }
    seen.push(ty);
    let any = |tys: Vec<Ty<'db>>, seen: &mut Vec<Ty<'db>>| {
        tys.into_iter()
            .any(|t| own_derived(db, program, op, t).is_some() || reaches(db, program, op, t, seen))
    };
    match ty.kind(db) {
        TyKind::Named(item, args) => match &type_def(db, program, *item).kind {
            TypeDefKind::Record { .. } => {
                let fields = fields_of(db, program, ty).unwrap_or_default();
                any(fields.into_iter().map(|(_, t)| t).collect(), seen)
                    || any(record_subtypes(db, program, ty), seen)
            }
            TypeDefKind::Refined(target) | TypeDefKind::Alias(target) => {
                any(vec![subst(db, program, *target, *item, args)], seen)
            }
            _ => false,
        },
        TyKind::Record {
            fields,
            open: false,
        } => any(fields.iter().map(|&(_, t)| t).collect(), seen),
        TyKind::Union(members) => any(members.clone(), seen),
        TyKind::Builtin(Builtin::List, args) => any(args.clone(), seen),
        TyKind::Builtin(Builtin::Map, args) => match op {
            Derived::Show => any(args.clone(), seen),
            Derived::Equals | Derived::Hash => any(args.iter().skip(1).copied().collect(), seen),
            Derived::Compare => false,
        },
        TyKind::Builtin(Builtin::Set, args) => op == Derived::Show && any(args.clone(), seen),
        _ => false,
    }
}

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
            Builtin::List => parts(seen, args.clone()),
            // Maps and sets have no order.
            Builtin::Map | Builtin::Set => form != "Ordered" && parts(seen, args.clone()),
            Builtin::Ref | Builtin::Ext | Builtin::Lazy => false,
            // A 32-bit float's bits do not order it.
            Builtin::CF32 => form != "Ordered",
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
