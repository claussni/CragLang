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

//! How types relate: subtyping (§3.13.3), unions and their absorption
//! (§3.6.1), the fields of a record type, and substitution of type
//! arguments.

use crag_db::Db;
use crag_hir::{ItemId, Name, Program};

use crate::def::{TypeDefKind, type_def, type_parent};
use crate::generic::param_bound;
use crate::ty::{Builtin, Ty, TyKind};

/// How deep a chain of parents is followed. Longer chains are cycles,
/// which the declarations report.
const MAX_PARENTS: usize = 64;

/// Whether a value of type `s` fits where `t` is expected (§3.13.3).
pub fn is_subtype<'db>(db: &'db dyn Db, program: Program, s: Ty<'db>, t: Ty<'db>) -> bool {
    subtype(db, program, s, t, 0)
}

fn subtype<'db>(db: &'db dyn Db, program: Program, s: Ty<'db>, t: Ty<'db>, depth: usize) -> bool {
    if s == t || s.is_error(db) || t.is_error(db) {
        return true;
    }
    if depth > MAX_PARENTS {
        return false;
    }
    let fits = |a, b| subtype(db, program, a, b, depth);
    match (s.kind(db), t.kind(db)) {
        // Every member of `s` fits `t`; `Never` fits everything.
        (TyKind::Union(members), _) => members.iter().all(|&m| fits(m, t)),
        (_, TyKind::Union(members)) => members.iter().any(|&m| fits(s, m)),
        (TyKind::Named(a, a_args), TyKind::Named(b, b_args)) if a == b => {
            a_args.iter().zip(b_args).all(|(&x, &y)| fits(x, y))
        }
        // A type parameter fits what its named bound fits (§4.2).
        (TyKind::Param(Some(owner), index, _), _) => param_bound(db, program, *owner, *index)
            .is_some_and(|b| subtype(db, program, b, t, depth + 1)),
        (TyKind::Named(..), _) => {
            let by_parent =
                parent(db, program, s).is_some_and(|p| subtype(db, program, p, t, depth + 1));
            by_parent || open_record_fits(db, program, s, t, depth)
        }
        (
            TyKind::Record {
                fields: s_fields,
                open: s_open,
            },
            TyKind::Record {
                fields: t_fields,
                open: t_open,
            },
        ) => {
            if *t_open {
                open_record_fits(db, program, s, t, depth)
            } else {
                !s_open
                    && s_fields.len() == t_fields.len()
                    && s_fields
                        .iter()
                        .zip(t_fields)
                        .all(|((a, x), (b, y))| a == b && fits(*x, *y))
            }
        }
        (TyKind::Builtin(a, a_args), TyKind::Builtin(b, b_args)) if a == b => {
            if *a == Builtin::Ref {
                a_args == b_args
            } else {
                a_args.iter().zip(b_args).all(|(&x, &y)| fits(x, y))
            }
        }
        (
            TyKind::Fn {
                params: s_params,
                result: s_result,
            },
            TyKind::Fn {
                params: t_params,
                result: t_result,
            },
        ) => {
            s_params.len() == t_params.len()
                && t_params.iter().zip(s_params).all(|(&x, &y)| fits(x, y))
                && fits(*s_result, *t_result)
        }
        _ => false,
    }
}

/// A record fits an open record type when it has every field the type
/// names, each fitting (§3.8.1).
fn open_record_fits<'db>(
    db: &'db dyn Db,
    program: Program,
    s: Ty<'db>,
    t: Ty<'db>,
    depth: usize,
) -> bool {
    let TyKind::Record {
        fields: wanted,
        open: true,
    } = t.kind(db)
    else {
        return false;
    };
    let Some(fields) = fields_of(db, program, s) else {
        return false;
    };
    wanted.iter().all(|(name, ty)| {
        fields
            .iter()
            .any(|(n, t)| n == name && subtype(db, program, *t, *ty, depth))
    })
}

/// The union of two types, absorbed (§3.13.2).
pub fn join<'db>(db: &'db dyn Db, program: Program, a: Ty<'db>, b: Ty<'db>) -> Ty<'db> {
    normalize(db, program, vec![a, b]).0
}

/// The union of the members, flattened and absorbed: a member that
/// another member contains is dropped (§3.6.1). Returns the union and the
/// dropped members, each with the member containing it. A union with the
/// error type is the error type.
pub fn normalize<'db>(
    db: &'db dyn Db,
    program: Program,
    members: Vec<Ty<'db>>,
) -> (Ty<'db>, Vec<(Ty<'db>, Ty<'db>)>) {
    let mut flat: Vec<Ty<'db>> = Vec::new();
    for member in members {
        for m in member.members(db) {
            if m.is_error(db) {
                return (m, Vec::new());
            }
            if !flat.contains(&m) {
                flat.push(m);
            }
        }
    }
    let mut kept: Vec<Ty<'db>> = Vec::new();
    let mut absorbed = Vec::new();
    for (i, &m) in flat.iter().enumerate() {
        let container = flat.iter().enumerate().find(|&(j, &other)| {
            j != i
                && is_subtype(db, program, m, other)
                // Of two members that fit each other, the first stays.
                && (j < i || !is_subtype(db, program, other, m))
        });
        match container {
            Some((_, &other)) => absorbed.push((m, other)),
            None => kept.push(m),
        }
    }
    kept.sort_by_key(|t| t.order());
    let ty = match kept.as_slice() {
        [one] => *one,
        _ => Ty::new(db, TyKind::Union(kept)),
    };
    (ty, absorbed)
}

/// The fields of a record type, its parent's first; none for a type
/// without fields of its own kind. A tag has none.
pub fn fields_of<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<Vec<(Name<'db>, Ty<'db>)>> {
    fields(db, program, ty, 0)
}

fn fields<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    depth: usize,
) -> Option<Vec<(Name<'db>, Ty<'db>)>> {
    match ty.kind(db) {
        TyKind::Record { fields, .. } => Some(fields.clone()),
        TyKind::Param(Some(owner), index, _) if depth <= MAX_PARENTS => fields(
            db,
            program,
            param_bound(db, program, *owner, *index)?,
            depth + 1,
        ),
        TyKind::Named(item, args) if depth <= MAX_PARENTS => {
            match &type_def(db, program, *item).kind {
                TypeDefKind::Tag => Some(Vec::new()),
                TypeDefKind::Record {
                    parent,
                    fields: own,
                } => {
                    let mut all = match parent {
                        Some(p) => {
                            fields(db, program, subst(db, program, *p, *item, args), depth + 1)?
                        }
                        None => Vec::new(),
                    };
                    for field in own {
                        let ty = subst(db, program, field.ty, *item, args);
                        match all.iter_mut().find(|(n, _)| *n == field.name) {
                            // A field the type amends replaces its parent's.
                            Some(existing) => existing.1 = ty,
                            None => all.push((field.name, ty)),
                        }
                    }
                    Some(all)
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// The fields a named record type declares itself, with whether each has
/// a default, in declaration order, its parent's first.
pub fn declared_fields<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<Vec<(Name<'db>, Ty<'db>, bool)>> {
    let TyKind::Named(item, args) = ty.kind(db) else {
        return None;
    };
    let TypeDefKind::Record { parent, fields } = &type_def(db, program, *item).kind else {
        return None;
    };
    let mut all: Vec<(Name<'db>, Ty<'db>, bool)> = match parent {
        Some(p) => {
            let p = subst(db, program, *p, *item, args);
            match declared_fields(db, program, p) {
                Some(fields) => fields,
                None => fields_of(db, program, p)?
                    .into_iter()
                    .map(|(n, t)| (n, t, false))
                    .collect(),
            }
        }
        None => Vec::new(),
    };
    for field in fields {
        let ty = subst(db, program, field.ty, *item, args);
        match all.iter_mut().find(|(n, ..)| *n == field.name) {
            Some(existing) => *existing = (field.name, ty, field.default),
            None => all.push((field.name, ty, field.default)),
        }
    }
    Some(all)
}

/// The parent a named type spreads, with its arguments substituted.
pub fn parent<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Ty<'db>> {
    let TyKind::Named(item, args) = ty.kind(db) else {
        return None;
    };
    let parent = type_parent(db, program, *item)?;
    Some(subst(db, program, parent, *item, args))
}

/// `Oks[x]` or `Errs[x]`: the members of `x` that are not errors, or
/// those that are (§8.1). A member that names a type parameter keeps the
/// function applied.
pub fn type_function<'db>(db: &'db dyn Db, program: Program, f: Builtin, x: Ty<'db>) -> Ty<'db> {
    let error = crate::group::error_type(db, program);
    let members = x
        .members(db)
        .into_iter()
        .filter_map(|m| {
            if m.is_error(db) {
                return Some(m);
            }
            if crate::generic::mentions_any(db, m) {
                return Some(Ty::new(db, TyKind::Builtin(f, vec![m])));
            }
            let is_error = error.is_some_and(|e| is_subtype(db, program, m, e));
            (is_error == (f == Builtin::Errs)).then_some(m)
        })
        .collect();
    normalize(db, program, members).0
}

/// `ty` with the type parameters of `owner` replaced by `args`.
pub fn subst<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    owner: ItemId<'db>,
    args: &[Ty<'db>],
) -> Ty<'db> {
    let go = |t: Ty<'db>| subst(db, program, t, owner, args);
    let kind = match ty.kind(db) {
        TyKind::Param(Some(o), index, _) if *o == owner => {
            return args
                .get(*index as usize)
                .copied()
                .unwrap_or_else(|| Ty::error(db));
        }
        TyKind::Error | TyKind::Param(..) => return ty,
        TyKind::Builtin(b, a) if a.is_empty() => return Ty::builtin(db, *b),
        TyKind::Builtin(b @ (Builtin::Oks | Builtin::Errs), a) => {
            return type_function(db, program, *b, go(a[0]));
        }
        TyKind::Builtin(b, a) => TyKind::Builtin(*b, a.iter().map(|&t| go(t)).collect()),
        TyKind::Named(_, a) if a.is_empty() => return ty,
        TyKind::Named(item, a) => TyKind::Named(*item, a.iter().map(|&t| go(t)).collect()),
        TyKind::Record { fields, open } => TyKind::Record {
            fields: fields.iter().map(|&(n, t)| (n, go(t))).collect(),
            open: *open,
        },
        TyKind::Fn { params, result } => TyKind::Fn {
            params: params.iter().map(|&t| go(t)).collect(),
            result: go(*result),
        },
        // A member can become a union, or contain another member.
        TyKind::Union(members) => {
            return normalize(db, program, members.iter().map(|&t| go(t)).collect()).0;
        }
    };
    Ty::new(db, kind)
}
