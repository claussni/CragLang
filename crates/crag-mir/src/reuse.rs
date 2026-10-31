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
//! A field read out of the record before it dies is kept: the reference
//! the box holds passes to the local that read it, which is not retained,
//! so that a value the record held alone stays held alone. The reads of
//! the record and its release move up, past code that uses neither them
//! nor the record and has no effects, to the first read. An update of a
//! part of a record whose old version dies, `Account(..a, items:
//! a.items.append(x))`, therefore finds the part held once, after the
//! record's other fields are read, and the runtime updates it in place
//! (Specification §13.4).
//!
//! The box itself is kept for a record built later on the straight path
//! from the release, across blocks that only it leads to and calls that
//! no handler of this frame catches, so that the record is built in its
//! memory. Code generation keeps a box only for a record of its size, and
//! a trap between the two frees it, empty.

use std::collections::HashSet;

use crag_db::Db;
use crag_hir::{Name, Program};
use crag_types::{Step, Ty, TyKind, TypeDefKind, type_def};

use crate::ir::{
    BlockId, Intrinsic, Local, LocalDecl, MirBody, Place, Rvalue, Statement, Terminator,
};

/// Turns the releases of records into reclaims, with the fields they keep
/// and the records built in their boxes.
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
            hoist(body, b, &mut i, local);
            let kept = keep_fields(body, b, &mut i, local);
            let token = match built_after(db, program, body, &incoming, b, i, ty) {
                Some((c, k)) => {
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
                    Some(token)
                }
                None => None,
            };
            if token.is_some() || !kept.is_empty() {
                body.blocks[b].statements[i] = Statement::Reclaim { local, token, kept };
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

/// Moves the release of `local` at statement `*at` of block `b` up, with
/// the reads of parts of it before, each with the retain that follows it,
/// past statements without effects that use none of them, nor steps that
/// show the record, and has `*at` follow it.
fn hoist(body: &mut MirBody<'_>, b: usize, at: &mut usize, local: Local) {
    let statements = &body.blocks[b].statements;
    let read = |s: &Statement<'_>| match s {
        Statement::Assign(dst, Rvalue::Read(place)) if place.local == local && *dst != local => {
            Some(*dst)
        }
        _ => None,
    };
    // The reads that go up, with their retains, and the statements passed.
    let mut group: Vec<usize> = Vec::new();
    let mut moved: Vec<Local> = Vec::new();
    let mut passed: Vec<usize> = Vec::new();
    let mut j = *at;
    while j > 0 {
        let s = &statements[j - 1];
        // A read and the retain after it, which stay together: before
        // what they pass, or where they are, before the release.
        if let Statement::Retain(k) = s
            && j >= 2
            && read(&statements[j - 2]) == Some(*k)
        {
            if passed.iter().any(|&p| uses(&statements[p], *k)) {
                break;
            }
            group.extend([j - 2, j - 1]);
            moved.push(*k);
            j -= 2;
            continue;
        }
        if let Some(k) = read(s)
            && !passed.iter().any(|&p| uses(&statements[p], k))
        {
            group.push(j - 1);
            moved.push(k);
            j -= 1;
            continue;
        }
        // A step that shows the record still shows it.
        let used = mentions(s, local) || moved.iter().any(|&k| uses(s, k));
        if used || !pure(s) {
            break;
        }
        passed.push(j - 1);
        j -= 1;
    }
    // Only reads that the release follows at once stay put.
    if passed.is_empty() {
        return;
    }
    group.sort_unstable();
    passed.sort_unstable();
    let statements = &mut body.blocks[b].statements;
    let release = statements[*at].clone();
    let mut order: Vec<Statement<'_>> = group.iter().map(|&k| statements[k].clone()).collect();
    order.push(release);
    order.extend(passed.iter().map(|&p| statements[p].clone()));
    let first = j;
    statements.splice(first..=*at, order);
    *at = first + group.len();
}

/// Whether a statement only computes its local's value, with no effect
/// that moving it past a release could show, such as a dispose handler.
fn pure(statement: &Statement<'_>) -> bool {
    match statement {
        Statement::Assign(_, Rvalue::Intrinsic(intrinsic, _)) => matches!(
            intrinsic,
            Intrinsic::ListAppend
                | Intrinsic::ListSet
                | Intrinsic::ListConcat
                | Intrinsic::ListSlice
                | Intrinsic::MapInsert
                | Intrinsic::SetInsert
                | Intrinsic::MapRemove
                | Intrinsic::SetContains
                | Intrinsic::MapKeys
                | Intrinsic::MapValues
                | Intrinsic::CollCount
                | Intrinsic::TextMeasure(_)
                | Intrinsic::TextAt(_)
                | Intrinsic::TextFind(_)
                | Intrinsic::TextMap(_)
                | Intrinsic::TextSlice
                | Intrinsic::CodePointOp(_)
                | Intrinsic::Word
        ),
        Statement::Assign(..) | Statement::Retain(_) | Statement::Step { .. } => true,
        _ => false,
    }
}

/// The fields of the record in `local`, released at statement `*at` of
/// block `b`, that are read out of it into locals before and retained
/// there, with nothing between that uses those locals or changes the
/// record. Their retains are removed, which moves `*at`.
fn keep_fields<'db>(
    body: &mut MirBody<'db>,
    b: usize,
    at: &mut usize,
    local: Local,
) -> Vec<(Name<'db>, Local)> {
    let statements = &body.blocks[b].statements;
    let mut kept: Vec<(Name<'db>, Local)> = Vec::new();
    let mut retains = Vec::new();
    for j in 0..at.saturating_sub(1) {
        let Statement::Assign(read, Rvalue::Read(Place { local: from, path })) = &statements[j]
        else {
            continue;
        };
        let (&[Step::Field(name)], true) = (&path[..], *from == local) else {
            continue;
        };
        if *read == local
            || statements[j + 1] != Statement::Retain(*read)
            || kept.iter().any(|(n, _)| *n == name)
        {
            continue;
        }
        let untouched = statements[j + 2..*at].iter().all(|s| {
            !matches!(s, Statement::Assign(dst, _) if *dst == local)
                && (matches!(s, Statement::Step { .. }) || !mentions(s, *read))
        });
        if untouched {
            kept.push((name, *read));
            retains.push(j + 1);
        }
    }
    for &r in retains.iter().rev() {
        body.blocks[b].statements.remove(r);
    }
    *at -= retains.len();
    kept
}

/// Whether a statement uses the local's value; a step uses none.
fn uses(statement: &Statement<'_>, local: Local) -> bool {
    !matches!(statement, Statement::Step { .. }) && mentions(statement, local)
}

fn mentions(statement: &Statement<'_>, local: Local) -> bool {
    statement
        .clone()
        .locals_mut()
        .into_iter()
        .any(|l| *l == local)
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
