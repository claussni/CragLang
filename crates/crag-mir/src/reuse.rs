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

//! Reuse after Perceus (Implementation Plan §11.10.1), in the optimizing
//! tier, once the reference counts are placed: the release of a record's
//! last reference becomes a `Reclaim`, which takes a box that no one else
//! holds apart instead of freeing it.
//!
//! The box is kept for a record built later on the straight path
//! from the release, across blocks that only it leads to and calls that
//! no handler of this frame catches, so that the record is built in its
//! memory. Code generation keeps a box only for a record of its size, and
//! a trap between the two frees it, empty.

use std::collections::HashSet;

use crag_db::Db;
use crag_hir::Program;
use crag_types::{Ty, TyKind, TypeDefKind, type_def};

use crate::ir::{BlockId, Local, LocalDecl, MirBody, Rvalue, Statement, Terminator};

/// Turns the releases of records into reclaims, with the records built in
/// their boxes.
pub fn insert_reuse<'db>(db: &'db dyn Db, program: Program, body: &mut MirBody<'db>) {
    let mut incoming = vec![0usize; body.blocks.len()];
    for block in &body.blocks {
        for s in block.terminator.successors() {
            incoming[s.index()] += 1;
        }
    }
    for b in 0..body.blocks.len() {
        let mut i = 0;
        while i < body.blocks[b].statements.len() {
            let Statement::Release(local) = body.blocks[b].statements[i] else {
                i += 1;
                continue;
            };
            let ty = body.locals[local.index()].ty;
            if !record(db, program, ty) {
                i += 1;
                continue;
            }
            if let Some((c, k)) = built_after(db, program, body, &incoming, b, i, ty) {
                let Statement::Assign(_, Rvalue::Record { ty, reuse, .. }) =
                    &mut body.blocks[c].statements[k]
                else {
                    unreachable!("a record is built there");
                };
                let token = Local(body.locals.len() as u32);
                *reuse = Some(token);
                let ty = *ty;
                body.locals.push(LocalDecl {
                    ty,
                    binding: None,
                    counted: true,
                    split: false,
                    borrowed: false,
                });
                body.blocks[b].statements[i] = Statement::Reclaim { local, token };
            }
            i += 1;
        }
    }
}

/// Whether values of the type are records in boxes of their own type.
fn record<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    match ty.kind(db) {
        TyKind::Record { fields, .. } => !fields.is_empty(),
        TyKind::Named(item, _) => matches!(
            type_def(db, program, *item).kind,
            TypeDefKind::Record { .. }
        ),
        _ => false,
    }
}

/// The first record built on the straight path from statement `at` of
/// block `b` that has no box to reuse yet: in the block, then on through
/// jumps and calls without handlers to blocks only they lead to. One of
/// the dying record's type comes first.
fn built_after<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &MirBody<'db>,
    incoming: &[usize],
    b: usize,
    at: usize,
    ty: Ty<'db>,
) -> Option<(usize, usize)> {
    let mut path = Vec::new();
    let mut seen = HashSet::new();
    let (mut block, mut from) = (b, at + 1);
    loop {
        path.push((block, from));
        let next = match &body.blocks[block].terminator {
            Terminator::Jump(next)
            | Terminator::Call {
                target: next,
                unwind: None,
                catch: None,
                ..
            }
            | Terminator::CallValue {
                target: next,
                unwind: None,
                catch: None,
                ..
            } => *next,
            _ => break,
        };
        if next == BlockId(0) || incoming[next.index()] != 1 || !seen.insert(next) {
            break;
        }
        (block, from) = (next.index(), 0);
    }
    let built = |c: usize, k: usize| match &body.blocks[c].statements[k] {
        Statement::Assign(
            _,
            Rvalue::Record {
                ty: built,
                reuse: None,
                ..
            },
        ) if record(db, program, *built) => Some(*built),
        _ => None,
    };
    let records: Vec<(usize, usize, Ty<'db>)> = path
        .iter()
        .flat_map(|&(c, from)| {
            (from..body.blocks[c].statements.len())
                .filter_map(move |k| built(c, k).map(|t| (c, k, t)))
        })
        .collect();
    let same = records.iter().find(|(_, _, t)| *t == ty);
    same.or(records.first()).map(|&(c, k, _)| (c, k))
}
