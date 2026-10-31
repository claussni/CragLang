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

//! The markers `Solid` and `Secret`, decided from types alone (§3.11,
//! Implementation Plan §11.10.12).
//!
//! A type is `Solid` when every part of it is: numbers, text and bytes
//! are; collections, records and unions are when their parts are; an
//! `is Pure` function type is, because a closure of one captures only
//! `Solid` values; a declared type is when its fields are, its conditions
//! are `Pure`, it has no `on Dispose` handler and it is not `is not Solid`.
//! `Lazy`, cells, the runtime's handles and the C types never are, and
//! neither is an open record, which may hold any fields. A named record
//! type is `Solid` only if its subtypes are, since a value of it may be
//! one of them.
//!
//! Only a declaration makes a type `Secret`; a type holds one when any
//! part of it is one.

use crag_db::Db;
use crag_hir::{ItemKind, Marker, ModuleId, Name, Owner, Program, hir_body, item_tree};

use crate::body_types;
use crate::def::{TypeDefKind, type_def, type_header};
use crate::derive::bans;
use crate::generic::{bounds, param_bound};
use crate::handler::dispose_handler;
use crate::relate::{fields_of, record_subtypes, subst};
use crate::result::{ErrorKind, Site, TypeError};
use crate::ty::{Builtin, Ty, TyKind};

/// Why a type is not `Solid`: the part that is not, reached through
/// `path`, and what that part is.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct NotSolid<'db> {
    pub path: Vec<SolidStep<'db>>,
    pub part: Ty<'db>,
    pub why: Why,
}

/// A step from a type to one of its parts.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum SolidStep<'db> {
    Field(Name<'db>),
    /// A subtype a value of a named record type may be.
    Subtype(Ty<'db>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum Why {
    /// A function type that is not `is Pure`.
    NotPure,
    /// `Lazy`, which may trap when it is read (§7.4).
    Lazy,
    /// A ref or an `ext` cell.
    Cell,
    /// A stream, hub or socket of the runtime.
    Handle,
    /// A C type (§16.1).
    C,
    /// A type with an `on Dispose` handler.
    Dispose,
    /// A type whose `where` conditions have effects.
    Condition,
    /// `is not Solid`.
    Marked,
    /// An open record, which may hold fields of any type.
    Open,
    /// A type parameter without the bound `Solid`.
    Param,
}

impl Why {
    fn predicate(self) -> &'static str {
        match self {
            Why::NotPure => "is a function that is not `is Pure`",
            Why::Lazy => "may trap when it is read",
            Why::Cell => "is a cell",
            Why::Handle => "is a handle of the runtime",
            Why::C => "is a C type",
            Why::Dispose => "has an `on Dispose` handler",
            Why::Condition => "has conditions with effects",
            Why::Marked => "is marked `not Solid`",
            Why::Open => "is an open record, so it may hold any fields",
            Why::Param => "is a type parameter without the bound `Solid`",
        }
    }
}

impl<'db> NotSolid<'db> {
    /// What the part is, and where it is in `ty`: `Holder is not Solid:
    /// its field `s` may hold a Round, whose field `f` holds () -> Int,
    /// which is a function that is not `is Pure``.
    pub fn message(&self, db: &'db dyn Db, ty: Ty<'db>) -> String {
        let mut out = format!("{} is not Solid: ", ty.display(db));
        let mut fields: Vec<&str> = Vec::new();
        let mut whose = false;
        let flush = |out: &mut String, fields: &mut Vec<&str>, whose: bool| {
            if !fields.is_empty() {
                let lead = if whose { "whose" } else { "its" };
                out.push_str(&format!("{lead} field `{}` ", fields.join(".")));
                fields.clear();
            } else if whose {
                out.push_str("which ");
            } else {
                out.push_str("it ");
            }
        };
        for step in &self.path {
            match step {
                SolidStep::Field(name) => fields.push(name.text(db)),
                SolidStep::Subtype(sub) => {
                    flush(&mut out, &mut fields, whose);
                    out.push_str(&format!("may hold a {}, ", sub.display(db)));
                    whose = true;
                }
            }
        }
        let at_part = fields.is_empty();
        flush(&mut out, &mut fields, whose);
        if at_part {
            out.push_str(self.why.predicate());
        } else {
            out.push_str(&format!(
                "holds {}, which {}",
                self.part.display(db),
                self.why.predicate()
            ));
        }
        out
    }
}

/// Whether a type is `Solid`, or the first part that is not.
#[crag_db::tracked(returns(ref))]
pub fn solid<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Result<(), NotSolid<'db>> {
    let mut walk = Walk {
        db,
        program,
        seen: Vec::new(),
        path: Vec::new(),
    };
    walk.solid(ty)
}

struct Walk<'db> {
    db: &'db dyn Db,
    program: Program,
    /// The types on the way to this part: a cycle through them holds
    /// nothing new.
    seen: Vec<Ty<'db>>,
    path: Vec<SolidStep<'db>>,
}

impl<'db> Walk<'db> {
    fn not(&self, part: Ty<'db>, why: Why) -> Result<(), NotSolid<'db>> {
        Err(NotSolid {
            path: self.path.clone(),
            part,
            why,
        })
    }

    fn all(&mut self, parts: impl IntoIterator<Item = Ty<'db>>) -> Result<(), NotSolid<'db>> {
        parts.into_iter().try_for_each(|t| self.solid(t))
    }

    fn solid(&mut self, ty: Ty<'db>) -> Result<(), NotSolid<'db>> {
        if self.seen.contains(&ty) {
            return Ok(());
        }
        self.seen.push(ty);
        let found = self.parts(ty);
        self.seen.pop();
        found
    }

    fn parts(&mut self, ty: Ty<'db>) -> Result<(), NotSolid<'db>> {
        let db = self.db;
        match ty.kind(db) {
            TyKind::Error => Ok(()),
            TyKind::Fn { pure, .. } => match pure {
                true => Ok(()),
                false => self.not(ty, Why::NotPure),
            },
            TyKind::Union(members) => self.all(members.clone()),
            TyKind::Record { fields, open } => {
                if *open {
                    return self.not(ty, Why::Open);
                }
                self.fields(fields.clone())
            }
            TyKind::Builtin(builtin, args) => match builtin {
                Builtin::List | Builtin::Map | Builtin::Set => self.all(args.clone()),
                Builtin::Lazy => self.not(ty, Why::Lazy),
                Builtin::Ref | Builtin::Ext => self.not(ty, Why::Cell),
                Builtin::RuntimeStream | Builtin::RuntimeHub | Builtin::RuntimeSocket => {
                    self.not(ty, Why::Handle)
                }
                Builtin::CF32 | Builtin::CPtr | Builtin::COut => self.not(ty, Why::C),
                _ => Ok(()),
            },
            TyKind::Param(owner, index, _) => {
                let Some(owner) = *owner else {
                    return self.not(ty, Why::Param);
                };
                let marked = bounds(db, self.program, owner)
                    .markers
                    .contains(&(*index, Marker::Solid));
                if marked {
                    return Ok(());
                }
                match param_bound(db, self.program, owner, *index) {
                    Some(bound) => self.solid(bound),
                    None => self.not(ty, Why::Param),
                }
            }
            TyKind::Named(item, args) => {
                if bans(db, self.program, ty, Marker::Solid.name()) {
                    return self.not(ty, Why::Marked);
                }
                if dispose_handler(db, self.program, ty).is_some() {
                    return self.not(ty, Why::Dispose);
                }
                if body_types(db, self.program, Owner::Item(*item))
                    .effects
                    .has_effects()
                {
                    return self.not(ty, Why::Condition);
                }
                match &type_def(db, self.program, *item).kind {
                    TypeDefKind::Alias(target) | TypeDefKind::Refined(target) => {
                        let target = subst(db, self.program, *target, *item, args);
                        self.solid(target)
                    }
                    TypeDefKind::Record { .. } => {
                        if let Some(fields) = fields_of(db, self.program, ty) {
                            self.fields(fields)?;
                        }
                        // A value of the type may be any of its subtypes.
                        for sub in record_subtypes(db, self.program, ty) {
                            self.path.push(SolidStep::Subtype(sub));
                            let found = self.solid(sub);
                            self.path.pop();
                            found?;
                        }
                        Ok(())
                    }
                    TypeDefKind::Builtin(_) | TypeDefKind::Tag | TypeDefKind::Form => Ok(()),
                }
            }
        }
    }

    fn fields(&mut self, fields: Vec<(Name<'db>, Ty<'db>)>) -> Result<(), NotSolid<'db>> {
        for (name, ty) in fields {
            self.path.push(SolidStep::Field(name));
            let found = self.solid(ty);
            self.path.pop();
            found?;
        }
        Ok(())
    }
}

/// The path to the first `Secret` part of a type, empty when the type is
/// one itself; none when it holds no secret.
#[crag_db::tracked(returns(ref))]
pub fn holds_secret<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Vec<Name<'db>>> {
    secret_path(db, program, ty, &mut Vec::new())
}

fn secret_path<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    seen: &mut Vec<Ty<'db>>,
) -> Option<Vec<Name<'db>>> {
    if seen.contains(&ty) {
        return None;
    }
    seen.push(ty);
    let in_fields = |fields: Vec<(Name<'db>, Ty<'db>)>, seen: &mut Vec<Ty<'db>>| {
        fields.into_iter().find_map(|(name, t)| {
            secret_path(db, program, t, seen).map(|mut path| {
                path.insert(0, name);
                path
            })
        })
    };
    let found = match ty.kind(db) {
        TyKind::Union(members) => members
            .iter()
            .find_map(|&m| secret_path(db, program, m, seen)),
        TyKind::Record { fields, .. } => in_fields(fields.clone(), seen),
        TyKind::Builtin(Builtin::List | Builtin::Map | Builtin::Set, args) => {
            args.iter().find_map(|&a| secret_path(db, program, a, seen))
        }
        TyKind::Named(item, args) => {
            if is_secret(db, program, ty) {
                Some(Vec::new())
            } else {
                match &type_def(db, program, *item).kind {
                    TypeDefKind::Alias(target) | TypeDefKind::Refined(target) => {
                        let target = subst(db, program, *target, *item, args);
                        secret_path(db, program, target, seen)
                    }
                    TypeDefKind::Record { .. } => fields_of(db, program, ty)
                        .and_then(|fields| in_fields(fields, seen))
                        .or_else(|| {
                            record_subtypes(db, program, ty)
                                .into_iter()
                                .find_map(|s| secret_path(db, program, s, seen))
                        }),
                    _ => None,
                }
            }
        }
        _ => None,
    };
    seen.pop();
    found
}

/// Whether a declared type, or a parent it spreads, is `is Secret`.
fn is_secret(db: &dyn Db, program: Program, ty: Ty<'_>) -> bool {
    let mut current = Some(ty);
    while let Some(t) = current {
        if let TyKind::Named(item, _) = t.kind(db) {
            let marked = hir_body(db, program, Owner::Item(*item))
                .type_decl
                .as_ref()
                .is_some_and(|d| {
                    d.markers
                        .iter()
                        .any(|(name, negated)| !negated && name.text(db) == "Secret")
                });
            if marked {
                return true;
            }
        }
        current = crate::relate::parent(db, program, t);
    }
    false
}

/// The types of a module marked `is Solid` that are not (§3.11).
pub(crate) fn marker_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(crag_hir::ItemId<'db>, TypeError<'db>)> {
    let mut errors = Vec::new();
    for item in &item_tree(db, module).items {
        let item = item.id;
        if *item.kind(db) != ItemKind::Type {
            continue;
        }
        let asserted = hir_body(db, program, Owner::Item(item))
            .type_decl
            .as_ref()
            .is_some_and(|d| {
                d.markers
                    .iter()
                    .any(|(name, negated)| !negated && name.text(db) == Marker::Solid.name())
            });
        if !asserted {
            continue;
        }
        let identity = crag_hir::type_identity(db, program, item);
        let names = type_header(db, program, item).params.clone();
        let params = (0..names.len())
            .map(|i| Ty::new(db, TyKind::Param(Some(identity), i as u32, names[i])))
            .collect();
        let ty = Ty::new(db, TyKind::Named(identity, params));
        if let Err(why) = solid(db, program, ty) {
            errors.push((
                item,
                TypeError {
                    site: Site::Name,
                    kind: ErrorKind::NotSolid {
                        ty,
                        why: why.clone(),
                    },
                },
            ));
        }
    }
    errors
}
