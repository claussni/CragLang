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
//!
//! A type parameter carries or lacks a marker as its requirements say,
//! `where T is { Solid, not Secret }` (§4.2); with neither, whether it
//! does is not known.

use crag_db::Db;
use crag_hir::{
    BindingId, BindingKind, Body, Expr, ExprId, ItemId, ItemKind, Marker, ModuleId, Name, Owner,
    Polarity, Program, Stmt, hir_body, item_tree,
};

use crate::body_types;
use crate::def::{TypeDefKind, prelude_item, type_def, type_header};
use crate::derive::bans;
use crate::generic::{MarkerBound, bounds, param_bound};
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
    /// `is not Solid`, or a type parameter required not to be.
    Marked,
    /// An open record, which may hold fields of any type.
    Open,
    /// A type parameter not required to be `Solid`.
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
            Why::Marked => "is marked or required `not Solid`",
            Why::Open => "is an open record, so it may hold any fields",
            Why::Param => "is a type parameter not required to be `Solid`",
        }
    }
}

impl<'db> NotSolid<'db> {
    /// What the part is, and where it is in `ty`: `Holder is not Solid:
    /// its field `s` may hold a Round, whose field `f` holds () -> Int,
    /// which is a function that is not `is Pure``.
    pub fn message(&self, db: &'db dyn Db, ty: Ty<'db>) -> String {
        part_message(db, ty, "Solid", &self.path, self.part, self.why.predicate())
    }
}

/// What a part is, and where it is in `ty`, for the message of a marker
/// the type does not carry.
fn part_message<'db>(
    db: &'db dyn Db,
    ty: Ty<'db>,
    marker: &str,
    path: &[SolidStep<'db>],
    part: Ty<'db>,
    predicate: &str,
) -> String {
    let mut out = format!("{} is not {marker}: ", ty.display(db));
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
    for step in path {
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
        out.push_str(predicate);
    } else {
        out.push_str(&format!("holds {}, which {}", part.display(db), predicate));
    }
    out
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
                Builtin::Ref | Builtin::Ext | Builtin::Dur | Builtin::Slot => {
                    self.not(ty, Why::Cell)
                }
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
                match param_marker(db, self.program, ty, Marker::Solid) {
                    Some(true) => return Ok(()),
                    Some(false) => return self.not(ty, Why::Marked),
                    None => {}
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
        TyKind::Param(..) if param_marker(db, program, ty, Marker::Secret) == Some(true) => {
            Some(Vec::new())
        }
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

/// Why a type is not `Storable` (§21.5): the part that is not, reached
/// through `path`, and the reason.
#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub struct NotStorable<'db> {
    pub path: Vec<SolidStep<'db>>,
    pub part: Ty<'db>,
    pub why: WhyNotStorable<'db>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, crag_db::SalsaValue)]
pub enum WhyNotStorable<'db> {
    /// The part is not `Solid`.
    NotSolid(Why),
    /// The part is or holds a `Secret`.
    Secret,
    /// An opaque type without an `Encode`/`Decode` pair (§18.9); runtime
    /// handles declare none.
    Opaque,
    /// A plain closure is compiled code: of function values, only `Expr`
    /// values are storable (§21.5).
    Function(Ty<'db>),
    /// `is not Storable`, or a type parameter required not to be.
    Marked,
    /// A type parameter not required to be `Storable`.
    Param,
}

impl<'db> WhyNotStorable<'db> {
    fn predicate(&self, db: &'db dyn Db) -> String {
        match self {
            WhyNotStorable::NotSolid(why) => why.predicate().into(),
            WhyNotStorable::Secret => "is marked `Secret`".into(),
            WhyNotStorable::Opaque => "is an opaque type without an `Encode`/`Decode` pair".into(),
            WhyNotStorable::Function(ty) => format!(
                "is a function; of function values, only `Expr[{}]` values are storable",
                ty.display(db)
            ),
            WhyNotStorable::Marked => "is marked or required `not Storable`".into(),
            WhyNotStorable::Param => "is a type parameter not required to be `Storable`".into(),
        }
    }

    /// Whether the reason depends on a type parameter, so the type may
    /// still be `Storable` for some arguments.
    pub fn unknown(&self) -> bool {
        matches!(
            self,
            WhyNotStorable::Param | WhyNotStorable::NotSolid(Why::Param)
        )
    }
}

impl<'db> NotStorable<'db> {
    /// What the part is, and where it is in `ty`, as `NotSolid::message`
    /// spells it.
    pub fn message(&self, db: &'db dyn Db, ty: Ty<'db>) -> String {
        part_message(
            db,
            ty,
            "Storable",
            &self.path,
            self.part,
            &self.why.predicate(db),
        )
    }
}

/// Whether a type is `Storable` (§21.5), or the first part that is not:
/// it is `Solid`, it is not `Secret` and holds none, and every opaque
/// type in it declares an `Encode`/`Decode` pair (§18.9). A plain
/// closure is compiled code and never storable; refs never occur in
/// values (§9.2), so they need no rule of their own.
#[crag_db::tracked(returns(ref))]
pub fn storable<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Result<(), NotStorable<'db>> {
    if let Err(why) = solid(db, program, ty) {
        return Err(NotStorable {
            path: why.path.clone(),
            part: why.part,
            why: WhyNotStorable::NotSolid(why.why),
        });
    }
    if let Some(path) = holds_secret(db, program, ty) {
        return Err(NotStorable {
            path: path.iter().map(|&n| SolidStep::Field(n)).collect(),
            part: ty,
            why: WhyNotStorable::Secret,
        });
    }
    let mut walk = StorableWalk {
        db,
        program,
        seen: Vec::new(),
        path: Vec::new(),
    };
    walk.storable(ty)
}

/// The walk for what solidity does not already decide: opaque types
/// without codecs, function types, bans and parameters.
struct StorableWalk<'db> {
    db: &'db dyn Db,
    program: Program,
    seen: Vec<Ty<'db>>,
    path: Vec<SolidStep<'db>>,
}

impl<'db> StorableWalk<'db> {
    fn not(&self, part: Ty<'db>, why: WhyNotStorable<'db>) -> Result<(), NotStorable<'db>> {
        Err(NotStorable {
            path: self.path.clone(),
            part,
            why,
        })
    }

    fn all(&mut self, parts: impl IntoIterator<Item = Ty<'db>>) -> Result<(), NotStorable<'db>> {
        parts.into_iter().try_for_each(|t| self.storable(t))
    }

    fn storable(&mut self, ty: Ty<'db>) -> Result<(), NotStorable<'db>> {
        if self.seen.contains(&ty) {
            return Ok(());
        }
        self.seen.push(ty);
        let found = self.parts(ty);
        self.seen.pop();
        found
    }

    fn parts(&mut self, ty: Ty<'db>) -> Result<(), NotStorable<'db>> {
        let db = self.db;
        match ty.kind(db) {
            TyKind::Error => Ok(()),
            TyKind::Fn { .. } => self.not(ty, WhyNotStorable::Function(ty)),
            TyKind::Union(members) => self.all(members.clone()),
            TyKind::Record { fields, .. } => self.fields(fields.clone()),
            TyKind::Builtin(builtin, args) => match builtin {
                Builtin::List | Builtin::Map | Builtin::Set => self.all(args.clone()),
                // An `Expr` carries its code as data (§18.6, §21.5).
                _ => Ok(()),
            },
            TyKind::Param(owner, index, _) => {
                match param_marker(db, self.program, ty, Marker::Storable) {
                    Some(true) => return Ok(()),
                    Some(false) => return self.not(ty, WhyNotStorable::Marked),
                    None => {}
                }
                let Some(owner) = *owner else {
                    return self.not(ty, WhyNotStorable::Param);
                };
                match param_bound(db, self.program, owner, *index) {
                    Some(bound) => self.storable(bound),
                    None => self.not(ty, WhyNotStorable::Param),
                }
            }
            TyKind::Named(item, args) => {
                if bans(db, self.program, ty, Marker::Storable.name()) {
                    return self.not(ty, WhyNotStorable::Marked);
                }
                // An opaque type travels through its own codec pair, so
                // its hidden fields are its handlers' business (§18.9).
                if type_def(db, self.program, *item).opaque {
                    let has = |kind| crate::lifecycle_handler(db, self.program, ty, kind).is_some();
                    return match has("Encode") && has("Decode") {
                        true => Ok(()),
                        false => self.not(ty, WhyNotStorable::Opaque),
                    };
                }
                match &type_def(db, self.program, *item).kind {
                    TypeDefKind::Alias(target) | TypeDefKind::Refined(target) => {
                        let target = subst(db, self.program, *target, *item, args);
                        self.storable(target)
                    }
                    TypeDefKind::Record { .. } => {
                        if let Some(fields) = fields_of(db, self.program, ty) {
                            self.fields(fields)?;
                        }
                        for sub in record_subtypes(db, self.program, ty) {
                            self.path.push(SolidStep::Subtype(sub));
                            let found = self.storable(sub);
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

    fn fields(&mut self, fields: Vec<(Name<'db>, Ty<'db>)>) -> Result<(), NotStorable<'db>> {
        for (name, ty) in fields {
            self.path.push(SolidStep::Field(name));
            let found = self.storable(ty);
            self.path.pop();
            found?;
        }
        Ok(())
    }
}

/// Whether a value of a type may hold a function value, in any part or
/// any subtype of one: a type parameter, a cell or a lazy value may.
pub fn holds_function<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    function_in(db, program, ty, &mut Vec::new())
}

fn function_in<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    seen: &mut Vec<Ty<'db>>,
) -> bool {
    if seen.contains(&ty) {
        return false;
    }
    seen.push(ty);
    let any = |parts: Vec<Ty<'db>>, seen: &mut Vec<Ty<'db>>| {
        parts.into_iter().any(|t| function_in(db, program, t, seen))
    };
    let found = match ty.kind(db) {
        TyKind::Error => false,
        TyKind::Fn { .. } | TyKind::Param(..) => true,
        TyKind::Union(members) => any(members.clone(), seen),
        TyKind::Record { fields, .. } => any(fields.iter().map(|(_, t)| *t).collect(), seen),
        TyKind::Builtin(builtin, args) => match builtin {
            Builtin::List | Builtin::Map | Builtin::Set => any(args.clone(), seen),
            Builtin::Lazy | Builtin::Ref | Builtin::Ext | Builtin::Dur | Builtin::Slot => true,
            _ => false,
        },
        TyKind::Named(item, args) => match &type_def(db, program, *item).kind {
            TypeDefKind::Alias(target) | TypeDefKind::Refined(target) => {
                let target = subst(db, program, *target, *item, args);
                any(vec![target], seen)
            }
            TypeDefKind::Record { .. } => {
                let fields = fields_of(db, program, ty)
                    .map(|f| f.into_iter().map(|(_, t)| t).collect())
                    .unwrap_or_default();
                any(fields, seen) || any(record_subtypes(db, program, ty), seen)
            }
            TypeDefKind::Builtin(_) | TypeDefKind::Tag | TypeDefKind::Form => false,
        },
    };
    seen.pop();
    found
}

/// Whether a declared type, or a parent it spreads, is `is Secret`.
fn is_secret(db: &dyn Db, program: Program, ty: Ty<'_>) -> bool {
    declares(db, program, ty, Marker::Secret)
}

/// Whether a declared type, or a parent it spreads, is marked `marker`.
fn declares(db: &dyn Db, program: Program, ty: Ty<'_>, marker: Marker) -> bool {
    let mut current = Some(ty);
    while let Some(t) = current {
        if let TyKind::Named(item, _) = t.kind(db) {
            let marked = hir_body(db, program, Owner::Item(*item))
                .type_decl
                .as_ref()
                .is_some_and(|d| {
                    d.markers
                        .iter()
                        .any(|(name, negated)| !negated && name.text(db) == marker.name())
                });
            if marked {
                return true;
            }
        }
        current = crate::relate::parent(db, program, t);
    }
    false
}

/// Whether a type parameter is required to carry `marker` or to lack it;
/// none when neither, or for another type (§4.2).
fn param_marker(db: &dyn Db, program: Program, ty: Ty<'_>, marker: Marker) -> Option<bool> {
    let TyKind::Param(Some(owner), index, _) = ty.kind(db) else {
        return None;
    };
    let markers = &bounds(db, program, *owner).markers;
    let wants = |polarity| markers.contains(&MarkerBound::new(*index, marker, polarity));
    if wants(Polarity::Carries) {
        Some(true)
    } else if wants(Polarity::Lacks) {
        Some(false)
    } else {
        None
    }
}

/// Whether a type carries a marker that describes types (§3.11, §4.2):
/// none when that is not known, because a type parameter in it is
/// required neither to carry the marker nor to lack it.
pub fn carries<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    marker: Marker,
) -> Option<bool> {
    if let TyKind::Param(..) = ty.kind(db)
        && let Some(known) = param_marker(db, program, ty, marker)
    {
        return Some(known);
    }
    match marker {
        Marker::Solid => match solid(db, program, ty) {
            Ok(()) => Some(true),
            Err(why) if why.why == Why::Param => None,
            Err(_) => Some(false),
        },
        Marker::Secret => {
            if holds_secret(db, program, ty).is_some() {
                Some(true)
            } else if unknown_secret(db, program, ty) {
                None
            } else {
                Some(false)
            }
        }
        Marker::Pure => match ty.kind(db) {
            TyKind::Fn { pure, .. } => Some(*pure),
            TyKind::Param(..) => None,
            _ => Some(false),
        },
        Marker::Immediate => match ty.kind(db) {
            TyKind::Named(..) => Some(declares(db, program, ty, Marker::Immediate)),
            TyKind::Param(..) => None,
            _ => Some(false),
        },
        Marker::Deferred => carries(db, program, ty, Marker::Immediate).map(|i| !i),
        Marker::Storable => match storable(db, program, ty) {
            // A `Secret` part may still hide in a type parameter.
            Ok(()) => match unknown_secret(db, program, ty) {
                true => None,
                false => Some(true),
            },
            Err(why) if why.why.unknown() => None,
            Err(_) => Some(false),
        },
    }
}

/// Whether a type parameter in a type may hold a secret: one required
/// neither to be `Secret` nor not to be.
fn unknown_secret<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    let go = |t: &Ty<'db>| unknown_secret(db, program, *t);
    match ty.kind(db) {
        TyKind::Param(..) => param_marker(db, program, ty, Marker::Secret).is_none(),
        TyKind::Builtin(_, args) | TyKind::Named(_, args) => args.iter().any(go),
        TyKind::Record { fields, .. } => fields.iter().any(|(_, t)| go(t)),
        TyKind::Union(members) => members.iter().any(go),
        TyKind::Error | TyKind::Fn { .. } => false,
    }
}

/// The types of a module marked `is Solid` that are not (§3.11), and its
/// signal types that are not `Solid` or hold a `Secret` (§11.1).
pub(crate) fn marker_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(ItemId<'db>, TypeError<'db>)> {
    let signal =
        prelude_item(db, program, "Signal").map(|s| crag_hir::type_identity(db, program, s));
    let mut errors = Vec::new();
    for item in &item_tree(db, module).items {
        let item = item.id;
        if *item.kind(db) != ItemKind::Type {
            continue;
        }
        let identity = crag_hir::type_identity(db, program, item);
        let names = type_header(db, program, item).params.clone();
        let params = (0..names.len())
            .map(|i| Ty::new(db, TyKind::Param(Some(identity), i as u32, names[i])))
            .collect();
        let ty = Ty::new(db, TyKind::Named(identity, params));
        let error = |kind| {
            (
                item,
                TypeError {
                    site: Site::Name,
                    kind,
                },
            )
        };
        // A signal type's subtypes report their own parts (§11.1).
        if signal.is_some_and(|s| s != identity && spreads(db, program, ty, s)) {
            if let Err(why) = solid(db, program, ty)
                && !why.path.iter().any(|s| matches!(s, SolidStep::Subtype(_)))
            {
                let why = why.clone();
                errors.push(error(ErrorKind::SignalNotSolid { ty, why }));
            }
            if let Some(path) = own_secret(db, program, ty) {
                errors.push(error(ErrorKind::SecretInSignal { ty, path }));
            }
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
        if let Err(why) = solid(db, program, ty) {
            let why = why.clone();
            errors.push(error(ErrorKind::NotSolid { ty, why }));
        }
    }
    errors
}

/// Whether a type spreads `parent`, directly or through its parents.
fn spreads<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>, parent: ItemId<'db>) -> bool {
    let mut current = crate::relate::parent(db, program, ty);
    while let Some(t) = current {
        if matches!(t.kind(db), TyKind::Named(item, _) if *item == parent) {
            return true;
        }
        current = crate::relate::parent(db, program, t);
    }
    false
}

/// The path to a `Secret` part of a type's own fields, leaving out its
/// subtypes, which are checked on their own.
fn own_secret<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Vec<Name<'db>>> {
    if is_secret(db, program, ty) {
        return Some(Vec::new());
    }
    fields_of(db, program, ty)?
        .into_iter()
        .find_map(|(name, t)| {
            holds_secret(db, program, t).clone().map(|mut path| {
                path.insert(0, name);
                path
            })
        })
}

/// The local functions marked `is Pure` that capture what is not
/// `Solid`; a closure's capture is reported where it must be Pure.
pub(crate) fn capture_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &Body<'db>,
    bindings: &[Option<Ty<'db>>],
) -> Vec<TypeError<'db>> {
    let mut errors = Vec::new();
    for expr in &body.exprs {
        let Expr::Block { stmts, .. } = expr else {
            continue;
        };
        for stmt in stmts {
            if let Stmt::Fn { function, .. } = stmt
                && function.pure
                && let Some(root) = function.body
                && let Some((name, ty, why)) = unsolid_capture(db, program, body, bindings, root)
            {
                errors.push(TypeError {
                    site: Site::Expr(root),
                    kind: ErrorKind::PureCapture { name, ty, why },
                });
            }
        }
    }
    errors
}

/// The first capture of a closure or local function that is not
/// `Solid`, which keeps it from being `is Pure`: a local function it calls
/// counts as what that function captures.
pub(crate) fn unsolid_capture<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &Body<'db>,
    bindings: &[Option<Ty<'db>>],
    frame: ExprId,
) -> Option<(Name<'db>, Ty<'db>, NotSolid<'db>)> {
    let local_fn = |binding: BindingId| {
        body.exprs.iter().find_map(|e| match e {
            Expr::Block { stmts, .. } => stmts.iter().find_map(|s| match s {
                Stmt::Fn {
                    binding: b,
                    function,
                } if *b == binding => function.body,
                _ => None,
            }),
            _ => None,
        })
    };
    let mut pending = body.free_bindings(frame);
    pending.reverse();
    let mut seen = Vec::new();
    while let Some(binding) = pending.pop() {
        if seen.contains(&binding) {
            continue;
        }
        seen.push(binding);
        let declared = body.binding(binding);
        match declared.kind {
            BindingKind::Module => {}
            BindingKind::Fn => {
                if let Some(root) = local_fn(binding) {
                    pending.extend(body.free_bindings(root).into_iter().rev());
                }
            }
            _ => {
                let ty = bindings.get(binding.index()).copied().flatten();
                if let (Some(name), Some(ty)) = (declared.name, ty)
                    && let Err(why) = solid(db, program, ty)
                {
                    return Some((name, ty, why.clone()));
                }
            }
        }
    }
    None
}
