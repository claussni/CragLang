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

//! The identity of a type that every program agrees on: a 128-bit hash
//! of its canonical form (Compiler Architecture §A11.2), which the codec
//! and code transport compare where a type index would differ from one
//! program to the next (Implementation Plan §11.10.11).
//!
//! The canonical form is the type as source spells it, a declared type
//! with what it declares: its module and name, its type arguments, whether
//! it is `distinct` or `opaque`, its fields by name with their types or a
//! conditioned alias's target. The declared types within those are named
//! by module, name and arguments alone, so no type is spelled out twice
//! and a recursive type ends; each has a hash of its own where it matters,
//! such as the box of a record in the codec. A union's members are in the
//! order of their hashes, so nothing depends on the order a session met
//! its types in.

use crag_db::Db;
use crag_hir::Program;

use crate::def::{TypeDefKind, type_def};
use crate::relate::{fields_of, parent};
use crate::ty::{Builtin, Ty, TyKind};

/// The hash of a type's canonical form.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord, crag_db::SalsaValue)]
pub struct TypeHash(pub [u8; 16]);

/// The hash of the canonical form of a type.
#[crag_db::tracked(returns(copy))]
pub fn type_hash<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> TypeHash {
    TypeHash(hash(db, program, ty, true))
}

/// The hash of a type, a declared type spelled out only when `whole`.
fn hash<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>, whole: bool) -> [u8; 16] {
    let mut out = Vec::new();
    let text = |out: &mut Vec<u8>, t: &str| {
        out.extend((t.len() as u32).to_le_bytes());
        out.extend(t.as_bytes());
    };
    let part = |out: &mut Vec<u8>, t: Ty<'db>| out.extend(hash(db, program, t, false));
    let list = |out: &mut Vec<u8>, types: &[Ty<'db>]| {
        out.extend((types.len() as u32).to_le_bytes());
        for &t in types {
            part(out, t);
        }
    };
    match ty.kind(db) {
        TyKind::Error => out.push(0),
        TyKind::Builtin(b, args) => {
            out.push(1);
            text(&mut out, b.name());
            if let Builtin::Fixed(scale) = b {
                out.extend(scale.to_le_bytes());
            }
            list(&mut out, args);
        }
        TyKind::Named(item, args) => {
            out.push(2);
            text(&mut out, item.module(db).path(db));
            text(&mut out, item.name(db).text(db));
            list(&mut out, args);
            if whole {
                let def = type_def(db, program, *item);
                out.push(u8::from(def.distinct) | u8::from(def.opaque) << 1);
                match &def.kind {
                    TypeDefKind::Tag => out.push(0),
                    TypeDefKind::Record { .. } => {
                        out.push(1);
                        let mut fields = fields_of(db, program, ty).unwrap_or_default();
                        fields.sort_by(|(a, _), (b, _)| a.text(db).cmp(b.text(db)));
                        out.extend((fields.len() as u32).to_le_bytes());
                        for (name, t) in fields {
                            text(&mut out, name.text(db));
                            part(&mut out, t);
                        }
                    }
                    TypeDefKind::Refined(_) => {
                        out.push(2);
                        let target = parent(db, program, ty).unwrap_or_else(|| Ty::error(db));
                        part(&mut out, target);
                    }
                    TypeDefKind::Builtin(_) | TypeDefKind::Alias(_) | TypeDefKind::Form => {
                        out.push(3)
                    }
                }
            }
        }
        TyKind::Record { fields, open } => {
            out.push(3);
            out.push(u8::from(*open));
            out.extend((fields.len() as u32).to_le_bytes());
            for (name, t) in fields {
                text(&mut out, name.text(db));
                part(&mut out, *t);
            }
        }
        TyKind::Fn {
            params,
            result,
            pure,
        } => {
            out.push(4);
            out.push(u8::from(*pure));
            list(&mut out, params);
            part(&mut out, *result);
        }
        TyKind::Union(members) => {
            out.push(5);
            let mut hashes: Vec<[u8; 16]> = members
                .iter()
                .map(|&m| hash(db, program, m, false))
                .collect();
            hashes.sort();
            out.extend((hashes.len() as u32).to_le_bytes());
            for h in hashes {
                out.extend(h);
            }
        }
        TyKind::Param(_, index, name) => {
            out.push(6);
            out.extend(index.to_le_bytes());
            text(&mut out, name.text(db));
        }
    }
    let mut hash = [0; 16];
    hash.copy_from_slice(&blake3::hash(&out).as_bytes()[..16]);
    hash
}
