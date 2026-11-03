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

//! The type indices a program gives the code it receives (Implementation
//! Plan §11.10.9). Received code runs on the receiver's heap, among its
//! values, so it must number every type as the receiver's own code does:
//! a box's header, a union's tag and a `case` on it all hold indices. The
//! receiver compiles that code from its own sources in a database of its
//! own, whose indices differ, so the program hands over its indices by the
//! canonical hash of each type, and the receiver's compiler takes them
//! (`layout::type_index`).
//!
//! The indices given are those of every type the program's code may name:
//! the types of the locals of its instances and what they are made of,
//! fields, members, elements and arguments, and the record types that may
//! stand for a record among them. A type the receiver meets that the
//! program has no index for is one no code of the program names, such as
//! the environment of a received closure, and gets an index past the
//! program's.

use std::collections::HashSet;

use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{Program, TypeIndices};
use crag_mir::{InstanceKey, Tier, mir};
use crag_types::{Ty, TyKind, fields_of, parent, record_subtypes, type_hash};

/// The program's type indices of the types the code of `instances` may
/// name, by canonical hash, and the first index past them.
pub fn program_indices<'db>(
    db: &'db dyn Db,
    program: Program,
    instances: &[InstanceKey<'db>],
    tier: Tier,
) -> TypeIndices {
    let mut seen = HashSet::new();
    let mut work = Vec::new();
    for &instance in instances {
        if let Some(body) = mir(db, program, instance, tier) {
            work.extend(body.locals.iter().map(|l| l.ty));
            work.push(body.result);
        }
    }
    let mut indices = TypeIndices::default();
    while let Some(ty) = work.pop() {
        if !seen.insert(ty) {
            continue;
        }
        let index = ty.as_id().index();
        indices.base = indices.base.max(index + 1);
        indices
            .by_hash
            .entry(type_hash(db, program, ty).0)
            .or_insert(index);
        work.extend(parts(db, program, ty));
    }
    indices
}

/// The types a value of `ty` may hold or be.
fn parts<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Vec<Ty<'db>> {
    let mut out = Vec::new();
    match ty.kind(db) {
        TyKind::Builtin(_, args) => out.extend(args.iter().copied()),
        TyKind::Named(_, args) => {
            out.extend(args.iter().copied());
            out.extend(parent(db, program, ty));
            out.extend(record_subtypes(db, program, ty));
        }
        TyKind::Record { fields, .. } => out.extend(fields.iter().map(|(_, t)| *t)),
        TyKind::Fn { params, result, .. } => {
            out.extend(params.iter().copied());
            out.push(*result);
        }
        TyKind::Union(members) => out.extend(members.iter().copied()),
        TyKind::Error | TyKind::Param(..) => {}
    }
    if let Some(fields) = fields_of(db, program, ty) {
        out.extend(fields.into_iter().map(|(_, t)| t));
    }
    let refined = crag_types::unrefined(db, program, ty);
    if refined != ty {
        out.push(refined);
    }
    out
}
