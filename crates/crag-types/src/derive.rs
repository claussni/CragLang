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
use crate::generic::{CallSite, Filling, form_def, own_filling};
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
pub(crate) fn derived_function<'db>(
    db: &'db dyn Db,
    program: Program,
    op: Derived,
) -> Option<ItemId<'db>> {
    let module = *crag_hir::module_index(db, program).modules.get(PRELUDE)?;
    let name = Name::new(db, op.name().to_string());
    let Some(Resolution::Value { functions, .. }) = module_scope(db, program, module).resolve(name)
    else {
        return None;
    };
    functions
        .iter()
        .copied()
        .find(|&f| derived_op(db, program, f) == Some(op))
}

/// The derived function a function is, if it is one of the prelude's.
pub fn derived_op(db: &dyn Db, program: Program, function: ItemId<'_>) -> Option<Derived> {
    if function.module(db).path(db) != PRELUDE {
        return None;
    }
    let op = match function.name(db).text(db).as_str() {
        "equals" => Derived::Equals,
        "compare" => Derived::Compare,
        "hash" => Derived::Hash,
        "show" => Derived::Show,
        _ => return None,
    };
    let sig = signature(db, program, function);
    let generic = sig.type_params == 1
        && sig
            .params
            .first()
            .is_some_and(|p| matches!(p.ty.kind(db), TyKind::Param(..)));
    generic.then_some(op)
}

/// The parts of a type's values that the derived function of a form
/// meets: the fields of a record, the subtypes of a record type, a
/// conditioned alias's target, the members of a union, the elements of a
/// list, and the entries of a map or set. Map keys and set members are
/// found by their structure, so they count only for `show`; maps and sets
/// have no order.
pub fn derived_parts<'db>(
    db: &'db dyn Db,
    program: Program,
    op: Derived,
    ty: Ty<'db>,
) -> Vec<Ty<'db>> {
    match ty.kind(db) {
        TyKind::Named(item, args) => match &type_def(db, program, *item).kind {
            TypeDefKind::Record { .. } => {
                let fields = fields_of(db, program, ty).unwrap_or_default();
                let mut parts: Vec<Ty<'db>> = fields.into_iter().map(|(_, t)| t).collect();
                parts.extend(record_subtypes(db, program, ty));
                parts
            }
            TypeDefKind::Refined(target) | TypeDefKind::Alias(target) => {
                vec![subst(db, program, *target, *item, args)]
            }
            _ => Vec::new(),
        },
        TyKind::Record {
            fields,
            open: false,
        } => fields.iter().map(|&(_, t)| t).collect(),
        TyKind::Union(members) => members.clone(),
        TyKind::Builtin(Builtin::List, args) => args.clone(),
        TyKind::Builtin(Builtin::Map, args) => match op {
            Derived::Show => args.clone(),
            Derived::Equals | Derived::Hash => args.iter().skip(1).copied().collect(),
            Derived::Compare => Vec::new(),
        },
        TyKind::Builtin(Builtin::Set, args) if op == Derived::Show => args.clone(),
        _ => Vec::new(),
    }
}

/// The parts of a type's values, at any depth, that have a function of
/// the form of their own where `at` is, each with that function: the
/// functions the derived one for the type calls (§19.11). A part with one
/// is not looked into. Only named types and type parameters have one; the
/// prelude's functions of numbers and text agree with the runtime's walk.
pub(crate) fn own_parts<'db>(
    db: &'db dyn Db,
    program: Program,
    op: Derived,
    ty: Ty<'db>,
    at: CallSite<'db>,
) -> Vec<(Ty<'db>, Filling<'db>)> {
    let Some(result) =
        derived_function(db, program, op).and_then(|f| signature(db, program, f).result)
    else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut seen = vec![ty];
    let mut pending: std::collections::VecDeque<Ty<'db>> =
        derived_parts(db, program, op, ty).into();
    while let Some(part) = pending.pop_front() {
        if seen.contains(&part) {
            continue;
        }
        seen.push(part);
        let own = match part.kind(db) {
            TyKind::Named(..) | TyKind::Param(..) => {
                own_filling(db, program, op.name(), &vec![part; op.arity()], result, at)
            }
            _ => None,
        };
        match own {
            Some(filling) => out.push((part, filling)),
            None => pending.extend(derived_parts(db, program, op, part)),
        }
    }
    out
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
