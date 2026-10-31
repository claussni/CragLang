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
//! the record and its release move up to where they keep the most fields:
//! within a block, past code that uses neither them nor the record, and
//! from a block to the block that dominates it, when no code between uses
//! them and the paths from there that leave release the record, which
//! they then need not. An update of a part of a record whose old version
//! dies, `Account(..a, items: a.items.append(x))` or with a call in place
//! of `append`, therefore finds the part held once, after the record's
//! other fields are read, and the runtime updates it in place
//! (Specification §13.4).
//!
//! Moved past code with effects, a release could run a dispose handler
//! earlier than it would have. It moves only past code without effects,
//! then, unless it frees nothing but the box: the record's type has no
//! dispose handler and no subtypes, and every counted field is kept.
//!
//! The box itself is kept for the record built later that every path from
//! the reclaim reaches or leaves the code by, through blocks that only
//! those paths enter, so that the record is built in its memory; the paths
//! that leave free it. Code generation keeps a box only for a record of
//! its size, and a trap between the two frees it, empty.

use std::collections::HashSet;

use crag_db::Db;
use crag_hir::{Name, Program};
use crag_types::{
    Step, Ty, TyKind, TypeDefKind, dispose_handler, fields_of, record_subtypes, type_def,
};

use crate::build::counted;
use crate::ir::{
    BlockId, Intrinsic, Local, LocalDecl, MirBody, Place, Rvalue, Statement, Terminator,
};
use crate::liveness::holds;

/// Turns the releases of records into reclaims, with the fields they keep
/// and the records built in their boxes.
pub fn insert_reuse<'db>(db: &'db dyn Db, program: Program, body: &mut MirBody<'db>) {
    lift_releases(db, program, body);
    let graph = Graph::of(body);
    let held = holds(body);
    let mut tokens = HashSet::new();
    for b in 0..body.blocks.len() {
        let mut i = 0;
        while i < body.blocks[b].statements.len() {
            let Statement::Release(local) = body.blocks[b].statements[i] else {
                i += 1;
                continue;
            };
            let ty = body.locals[local.index()].ty;
            if !record(db, program, ty) || tokens.contains(&local) {
                i += 1;
                continue;
            }
            if !holders(&held, local) {
                let statements = &body.blocks[b].statements;
                if let Some((arranged, at)) = arrange(db, program, statements, i, local, ty) {
                    body.blocks[b].statements = arranged;
                    i = at;
                }
            }
            let kept = keep_fields(body, b, &mut i, local);
            let token = match built_after(db, program, body, &graph, b, i, ty) {
                Some((c, k, exits)) => {
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
                    // The paths that leave without the record free the box.
                    for e in exits {
                        body.blocks[e]
                            .statements
                            .insert(0, Statement::Release(token));
                    }
                    tokens.insert(token);
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

/// Whether a closure on the side stack borrows the local, so that its uses
/// are the local's too: its release then stays where it is.
fn holders(held: &[crate::liveness::LocalSet], local: Local) -> bool {
    held.iter().any(|set| set.contains(&local))
}

/// The predecessors and immediate dominators of a body's blocks.
struct Graph {
    preds: Vec<Vec<usize>>,
    idom: Vec<Option<usize>>,
}

impl Graph {
    /// By the algorithm of Cooper, Harvey and Kennedy, over the blocks the
    /// entry reaches in reverse postorder.
    fn of(body: &MirBody<'_>) -> Graph {
        let n = body.blocks.len();
        let succs: Vec<Vec<usize>> = body
            .blocks
            .iter()
            .map(|b| {
                b.terminator
                    .successors()
                    .iter()
                    .map(|s| s.index())
                    .collect()
            })
            .collect();
        let mut preds = vec![Vec::new(); n];
        for (b, ss) in succs.iter().enumerate() {
            for &s in ss {
                if !preds[s].contains(&b) {
                    preds[s].push(b);
                }
            }
        }
        // Postorder, without recursion.
        let mut order = Vec::new();
        let mut seen = vec![false; n];
        let mut stack = vec![(0usize, 0usize)];
        seen[0] = true;
        while let Some(&mut (b, ref mut next)) = stack.last_mut() {
            if let Some(&s) = succs[b].get(*next) {
                *next += 1;
                if !seen[s] {
                    seen[s] = true;
                    stack.push((s, 0));
                }
                continue;
            }
            order.push(b);
            stack.pop();
        }
        let mut rank = vec![usize::MAX; n];
        for (k, &b) in order.iter().enumerate() {
            rank[b] = k;
        }
        let mut idom: Vec<Option<usize>> = vec![None; n];
        idom[0] = Some(0);
        let intersect = |idom: &[Option<usize>], mut a: usize, mut b: usize| {
            while a != b {
                while rank[a] < rank[b] {
                    a = idom[a].expect("a block with a dominator");
                }
                while rank[b] < rank[a] {
                    b = idom[b].expect("a block with a dominator");
                }
            }
            a
        };
        loop {
            let mut changed = false;
            for &b in order.iter().rev().skip(1) {
                let mut new: Option<usize> = None;
                for &p in &preds[b] {
                    if idom[p].is_none() {
                        continue;
                    }
                    new = Some(match new {
                        None => p,
                        Some(q) => intersect(&idom, p, q),
                    });
                }
                if new.is_some() && idom[b] != new {
                    idom[b] = new;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        idom[0] = None;
        Graph { preds, idom }
    }

    /// The blocks on the paths from `d` before they reach `s`, when only
    /// those paths enter them and `s`, and none goes back to `d`.
    fn region(&self, body: &MirBody<'_>, d: usize, s: usize) -> Option<Vec<usize>> {
        let mut region = Vec::new();
        let mut stack: Vec<usize> = body.blocks[d]
            .terminator
            .successors()
            .iter()
            .map(|b| b.index())
            .collect();
        while let Some(c) = stack.pop() {
            if c == d || region.len() > 256 {
                return None;
            }
            if c == s || region.contains(&c) {
                continue;
            }
            region.push(c);
            stack.extend(
                body.blocks[c]
                    .terminator
                    .successors()
                    .iter()
                    .map(|b| b.index()),
            );
        }
        let entered = region
            .iter()
            .chain([&s])
            .all(|&c| self.preds[c].iter().all(|&p| p == d || region.contains(&p)));
        (entered && !self.preds[s].is_empty()).then_some(region)
    }
}

/// Moves each record's release, with the reads of its fields, from a block
/// to the block that dominates it, where they keep more fields.
fn lift_releases<'db>(db: &'db dyn Db, program: Program, body: &mut MirBody<'db>) {
    for _ in 0..64 {
        let graph = Graph::of(body);
        let held = holds(body);
        let mut lifted = false;
        'blocks: for s in 1..body.blocks.len() {
            for r in 0..body.blocks[s].statements.len() {
                if let Statement::Release(local) = body.blocks[s].statements[r]
                    && record(db, program, body.locals[local.index()].ty)
                    && !holders(&held, local)
                    && lift(db, program, body, &graph, s, r, local)
                {
                    lifted = true;
                    break 'blocks;
                }
            }
        }
        if !lifted {
            return;
        }
    }
}

/// Moves the release of `local` at statement `r` of block `s`, with the
/// reads of its fields before, to the end of the block that dominates
/// `s`, if they keep more fields there, and arranges them there.
fn lift<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &mut MirBody<'db>,
    graph: &Graph,
    s: usize,
    r: usize,
    local: Local,
) -> bool {
    let Some(d) = graph.idom[s] else {
        return false;
    };
    let ty = body.locals[local.index()].ty;
    let statements = &body.blocks[s].statements;
    // What goes up must be all that comes before it in the block.
    let hoist = hoisted(statements, r, local, true);
    if hoist.first != 0 {
        return false;
    }
    let stay = match arrange(db, program, statements, r, local, ty) {
        Some((arranged, at)) => keepable(&arranged, at, local).len(),
        None => keepable(statements, r, local).len(),
    };
    let Some(region) = graph.region(body, d, s) else {
        return false;
    };
    let group = hoist.statements[..hoist.at].to_vec();
    let rest = hoist.statements[hoist.at + 1..].to_vec();
    // Neither the record nor what is read out of it is used between.
    let mut watched = vec![local];
    watched.extend(group.iter().filter_map(|s| match s {
        Statement::Assign(dst, _) => Some(*dst),
        _ => None,
    }));
    let watches = |s: &Statement<'_>| watched.iter().any(|&l| uses(s, l));
    let in_terminator = |t: &Terminator<'_>| {
        let mut t = t.clone();
        t.locals_mut().into_iter().any(|l| watched.contains(l))
    };
    let mut effects = hoist.effects || calls(&body.blocks[d].terminator);
    for &c in &region {
        let block = &body.blocks[c];
        for st in &block.statements {
            match st {
                Statement::Release(l) if *l == local => {}
                _ if watches(st) => return false,
                _ => effects |= !pure(st),
            }
        }
        if in_terminator(&block.terminator) {
            return false;
        }
        effects |= calls(&block.terminator);
    }
    if in_terminator(&body.blocks[d].terminator) {
        return false;
    }
    let mut above = body.blocks[d].statements.clone();
    above.extend(group);
    above.push(Statement::Release(local));
    let at = above.len() - 1;
    let (above, at) = arrange(db, program, &above, at, local, ty).unwrap_or((above, at));
    let kept = keepable(&above, at, local);
    if kept.len() <= stay || (effects && !silent(db, program, ty, &kept)) {
        return false;
    }
    body.blocks[d].statements = above;
    body.blocks[s].statements = rest;
    strip(&mut body.blocks[s].statements, local);
    for &c in &region {
        let statements = &mut body.blocks[c].statements;
        statements.retain(|st| *st != Statement::Release(local));
        strip(statements, local);
    }
    true
}

/// Whether a terminator runs other code.
fn calls(terminator: &Terminator<'_>) -> bool {
    matches!(
        terminator,
        Terminator::Call { .. }
            | Terminator::CallValue { .. }
            | Terminator::TailCall { .. }
            | Terminator::TailCallValue { .. }
    )
}

/// Steps no longer show the local, which is released before them.
fn strip(statements: &mut [Statement<'_>], local: Local) {
    for s in statements {
        if let Statement::Step { locals, .. } = s {
            locals.retain(|&l| l != local);
        }
    }
}

/// Whether releasing the record frees nothing but its box, with the fields
/// kept: its type has no dispose handler and no subtypes, whose boxes it
/// may hold, and every counted field is kept.
fn silent<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    kept: &[(Name<'db>, Local, usize)],
) -> bool {
    let TyKind::Named(_, args) = ty.kind(db) else {
        return false;
    };
    let Some(fields) = fields_of(db, program, ty) else {
        return false;
    };
    args.is_empty()
        && dispose_handler(db, program, ty).is_none()
        && record_subtypes(db, program, ty).is_empty()
        && fields
            .iter()
            .all(|&(name, t)| !counted(db, program, t) || kept.iter().any(|k| k.0 == name))
}

/// The statements of a block with the release of `local` at `at` moved up,
/// with the reads of its fields before, past what uses none of them, the
/// release's new place, where the reads begin, and whether code with
/// effects was passed.
struct Hoisted<'db> {
    statements: Vec<Statement<'db>>,
    at: usize,
    first: usize,
    effects: bool,
}

/// Moves the release of `local` at statement `at` up, with the reads of
/// parts of it before, each with the retain that follows it, past
/// statements that use none of them, and past only those without effects
/// unless `effects`. Steps after the release no longer show the record.
fn hoisted<'db>(
    statements: &[Statement<'db>],
    at: usize,
    local: Local,
    effects: bool,
) -> Hoisted<'db> {
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
    let mut impure = false;
    let mut j = at;
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
        let used = uses(s, local) || moved.iter().any(|&k| uses(s, k));
        if used || !(effects || pure(s)) {
            break;
        }
        impure |= !pure(s);
        passed.push(j - 1);
        j -= 1;
    }
    group.sort_unstable();
    passed.sort_unstable();
    let mut out = statements[..j].to_vec();
    out.extend(group.iter().map(|&k| statements[k].clone()));
    let release = out.len();
    out.push(statements[at].clone());
    let mut after: Vec<Statement<'db>> = passed.iter().map(|&p| statements[p].clone()).collect();
    strip(&mut after, local);
    out.extend(after);
    out.extend(statements[at + 1..].iter().cloned());
    Hoisted {
        statements: out,
        at: release,
        first: j,
        effects: impure,
    }
}

/// The block's statements arranged so that the release of `local` at `at`
/// keeps more fields, and its new place: moved past code with effects when
/// the release is silent then, else past code without.
fn arrange<'db>(
    db: &'db dyn Db,
    program: Program,
    statements: &[Statement<'db>],
    at: usize,
    local: Local,
    ty: Ty<'db>,
) -> Option<(Vec<Statement<'db>>, usize)> {
    let before = keepable(statements, at, local).len();
    for effects in [true, false] {
        let h = hoisted(statements, at, local, effects);
        let kept = keepable(&h.statements, h.at, local);
        if kept.len() > before && (!h.effects || silent(db, program, ty, &kept)) {
            return Some((h.statements, h.at));
        }
    }
    None
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

/// The fields of the record in `local`, released at statement `at`, that
/// are read out of it into locals before and retained there, with nothing
/// between that uses those locals or changes the record: each with its
/// local and its retain.
fn keepable<'db>(
    statements: &[Statement<'db>],
    at: usize,
    local: Local,
) -> Vec<(Name<'db>, Local, usize)> {
    let mut kept: Vec<(Name<'db>, Local, usize)> = Vec::new();
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
            || kept.iter().any(|(n, ..)| *n == name)
        {
            continue;
        }
        let untouched = statements[j + 2..at]
            .iter()
            .all(|s| !matches!(s, Statement::Assign(dst, _) if *dst == local) && !uses(s, *read));
        if untouched {
            kept.push((name, *read, j + 1));
        }
    }
    kept
}

/// The fields `keepable` finds, whose retains go, which moves `*at`.
fn keep_fields<'db>(
    body: &mut MirBody<'db>,
    b: usize,
    at: &mut usize,
    local: Local,
) -> Vec<(Name<'db>, Local)> {
    let kept = keepable(&body.blocks[b].statements, *at, local);
    for &(.., r) in kept.iter().rev() {
        body.blocks[b].statements.remove(r);
    }
    *at -= kept.len();
    kept.into_iter().map(|(name, l, _)| (name, l)).collect()
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

/// The first record built after statement `at` of block `b` that has no
/// box to reuse yet, with the blocks that leave the code on paths that do
/// not reach it. First on the straight path, in the block, then on
/// through jumps and calls without handlers to blocks only they lead to;
/// then in a block that every path from `b` reaches or leaves the code
/// before, through blocks only those paths enter. One of the dying
/// record's type comes first.
fn built_after<'db>(
    db: &'db dyn Db,
    program: Program,
    body: &MirBody<'db>,
    graph: &Graph,
    b: usize,
    at: usize,
    ty: Ty<'db>,
) -> Option<(usize, usize, Vec<usize>)> {
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
    let pick = |records: Vec<(usize, usize, Ty<'db>)>| {
        let same = records.iter().find(|(_, _, t)| *t == ty);
        same.or(records.first()).map(|&(c, k, _)| (c, k))
    };
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
        if next == BlockId(0) || graph.preds[next.index()].len() != 1 || !seen.insert(next) {
            break;
        }
        (block, from) = (next.index(), 0);
    }
    let straight: Vec<(usize, usize, Ty<'db>)> = path
        .iter()
        .flat_map(|&(c, from)| {
            (from..body.blocks[c].statements.len())
                .filter_map(move |k| built(c, k).map(|t| (c, k, t)))
        })
        .collect();
    if let Some((c, k)) = pick(straight) {
        return Some((c, k, Vec::new()));
    }
    // The last block of the straight path, and the blocks that follow it.
    let (last, _) = *path.last().expect("a path");
    let mut candidates = Vec::new();
    let mut seen: HashSet<usize> = HashSet::from([last]);
    let mut queue: Vec<usize> = vec![last];
    while let Some(c) = queue.first().copied() {
        queue.remove(0);
        if seen.len() > 64 {
            break;
        }
        for s in body.blocks[c].terminator.successors() {
            if seen.insert(s.index()) {
                queue.push(s.index());
                let records: Vec<(usize, usize, Ty<'db>)> =
                    (0..body.blocks[s.index()].statements.len())
                        .filter_map(|k| built(s.index(), k).map(|t| (s.index(), k, t)))
                        .collect();
                if !records.is_empty() {
                    candidates.push(records);
                }
            }
        }
    }
    let mut found: Vec<(usize, usize, Vec<usize>, Ty<'db>)> = Vec::new();
    for records in candidates {
        let c = records[0].0;
        let Some(region) = graph.region(body, last, c) else {
            continue;
        };
        let exits = region
            .into_iter()
            .filter(|&e| body.blocks[e].terminator.successors().is_empty())
            .collect::<Vec<_>>();
        let (c, k) = pick(records.clone()).expect("a record");
        let t = records.iter().find(|r| r.1 == k).expect("the record").2;
        found.push((c, k, exits, t));
    }
    let same = found.iter().position(|f| f.3 == ty);
    let chosen = same.or((!found.is_empty()).then_some(0))?;
    let (c, k, exits, _) = found.swap_remove(chosen);
    Some((c, k, exits))
}
