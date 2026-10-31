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

//! Reference counts that cancel (Implementation Plan §11.10.1), once they
//! are placed.
//!
//! A part read out of a value gets a reference of its own when it lives
//! on, which it gives up after its last use. When the part, and the locals
//! it is copied to, are only read, and the value it was read out of keeps
//! its own reference all the while, the two cancel: the part is borrowed
//! from the value, as a borrowed parameter is from the caller, not counted
//! and listed in no stack map. A value of a record type, or a union with a
//! record member, keeps its count, since code generation may read it out
//! of a storage form as a box of its own. A retain directly followed by
//! the release of the same local cancels too.

use std::collections::BTreeSet;

use crag_db::Db;
use crag_hir::Program;

use crate::borrow::borrowable;
use crate::ir::{Local, MirBody, Operand, Place, Rvalue, Statement, Terminator};
use crate::liveness::{
    Lent, Liveness, LocalSet, compute_liveness, statement_uses, terminator_uses,
};

/// A part read out of a value: where it is read, the locals that hold it,
/// the part first and then its copies, and the local it is read out of.
struct Part {
    def: (usize, usize),
    locals: LocalSet,
    source: Local,
}

/// Cancels the retains and releases of the parts read out of values that
/// outlive them, and those of a local that follow each other.
pub fn elide_rc<'db>(db: &'db dyn Db, program: Program, body: &mut MirBody<'db>, lent: &Lent<'db>) {
    cancel_adjacent(body);
    let live = compute_liveness(body, lent.clone());
    // A part borrowed in turn holds no reference to lend.
    let mut borrowed = LocalSet::new();
    let mut sources = LocalSet::new();
    for part in parts(db, program, body) {
        if source_counted(body, part.source)
            && !borrowed.contains(&part.source)
            && part.locals.is_disjoint(&sources)
            && only_read(body, &live, &part)
            && outlived(body, &live, &part)
        {
            borrowed.extend(&part.locals);
            sources.insert(part.source);
        }
    }
    for block in &mut body.blocks {
        block.statements.retain(|st| {
            !matches!(st, Statement::Retain(l) | Statement::Release(l) if borrowed.contains(l))
        });
    }
    for l in borrowed {
        let decl = &mut body.locals[l.index()];
        decl.counted = false;
        decl.borrowed = true;
    }
}

/// Removes each retain that the release of the same local follows.
fn cancel_adjacent(body: &mut MirBody<'_>) {
    for block in &mut body.blocks {
        let mut k = 0;
        while k + 1 < block.statements.len() {
            match (&block.statements[k], &block.statements[k + 1]) {
                (Statement::Retain(a), Statement::Release(b)) if a == b => {
                    block.statements.drain(k..k + 2);
                    k = k.saturating_sub(1);
                }
                _ => k += 1,
            }
        }
    }
}

/// The parts read out of a local and retained right after, with their
/// copies: the counted locals of a type that may be borrowed, each
/// assigned once.
fn parts<'db>(db: &'db dyn Db, program: Program, body: &MirBody<'db>) -> Vec<Part> {
    let mut defs = vec![0usize; body.locals.len()];
    let mut copies: Vec<(Local, Local)> = Vec::new();
    for block in &body.blocks {
        for statement in &block.statements {
            match statement {
                Statement::Assign(dst, rvalue) => {
                    defs[dst.index()] += 1;
                    if let Rvalue::Use(Operand::Local(src)) = rvalue {
                        copies.push((*src, *dst));
                    }
                }
                Statement::Reclaim {
                    token: Some(dst), ..
                } => defs[dst.index()] += 1,
                _ => {}
            }
        }
        if let Terminator::Call { dst, .. } | Terminator::CallValue { dst, .. } = &block.terminator
        {
            defs[dst.index()] += 1;
        }
    }
    let eligible = |l: Local| {
        let decl = &body.locals[l.index()];
        l.index() >= body.params
            && decl.counted
            && defs[l.index()] == 1
            && borrowable(db, program, decl.ty)
    };
    let mut found = Vec::new();
    for (b, block) in body.blocks.iter().enumerate() {
        for (s, statement) in block.statements.iter().enumerate() {
            let Statement::Assign(dst, rvalue) = statement else {
                continue;
            };
            let Some(source) = read_from(rvalue) else {
                continue;
            };
            if source == *dst
                || !eligible(*dst)
                || !matches!(block.statements.get(s + 1), Some(Statement::Retain(l)) if l == dst)
            {
                continue;
            }
            let mut locals = LocalSet::from([*dst]);
            loop {
                let more: Vec<Local> = copies
                    .iter()
                    .filter(|(src, dst)| locals.contains(src) && !locals.contains(dst))
                    .map(|&(_, dst)| dst)
                    .filter(|&dst| eligible(dst))
                    .collect();
                if more.is_empty() {
                    break;
                }
                locals.extend(more);
            }
            if !locals.contains(&source) {
                found.push(Part {
                    def: (b, s),
                    locals,
                    source,
                });
            }
        }
    }
    found
}

/// The local whose value a read borrows its result from, for reads of
/// values that do not change: records, unions, lists and maps, not what
/// a ref, an ext or a lazy value holds.
fn read_from(rvalue: &Rvalue<'_>) -> Option<Local> {
    match rvalue {
        Rvalue::Read(Place { local, .. })
        | Rvalue::Index {
            list: Place { local, .. },
            ..
        }
        | Rvalue::MapGet {
            map: Place { local, .. },
            boxed: false,
            ..
        } => Some(*local),
        _ => None,
    }
}

/// Whether the source holds a reference of its own that only its uses
/// give up: a counted local, or a borrowed parameter, which its caller
/// keeps.
fn source_counted(body: &MirBody<'_>, source: Local) -> bool {
    let decl = &body.locals[source.index()];
    decl.counted || (decl.borrowed && source.index() < body.params)
}

/// Whether the part is only read: besides its one retain, its releases
/// and the copies between its locals, every use of them borrows.
fn only_read<'db>(body: &MirBody<'db>, live: &Liveness<'db>, part: &Part) -> bool {
    let (db, ds) = part.def;
    for (b, block) in body.blocks.iter().enumerate() {
        for (s, statement) in block.statements.iter().enumerate() {
            match statement {
                Statement::Retain(l) if part.locals.contains(l) => {
                    if (b, s) != (db, ds + 1) {
                        return false;
                    }
                    continue;
                }
                Statement::Release(l) if part.locals.contains(l) => continue,
                Statement::Assign(dst, Rvalue::Use(Operand::Local(src)))
                    if part.locals.contains(dst) && part.locals.contains(src) =>
                {
                    continue;
                }
                _ => {}
            }
            let uses = statement_uses(body, &live.holds, statement);
            if uses.consumed.iter().any(|l| part.locals.contains(l)) {
                return false;
            }
        }
        let uses = terminator_uses(body, &live.holds, &live.lent, &block.terminator);
        if uses.consumed.iter().any(|l| part.locals.contains(l)) {
            return false;
        }
    }
    true
}

/// Whether the source keeps its reference wherever one of the part's
/// locals is live: no statement or terminator there gives it up or
/// assigns it.
fn outlived<'db>(body: &MirBody<'db>, live: &Liveness<'db>, part: &Part) -> bool {
    let source = part.source;
    for (b, block) in body.blocks.iter().enumerate() {
        let mut alive: BTreeSet<Local> = live.live_in[b]
            .intersection(&part.locals)
            .copied()
            .collect();
        for (s, statement) in block.statements.iter().enumerate() {
            match statement {
                Statement::Assign(dst, _) if (b, s) == part.def => {
                    alive.insert(*dst);
                    continue;
                }
                // The copied local dies at its copy, which retains nothing.
                Statement::Assign(dst, Rvalue::Use(Operand::Local(src)))
                    if part.locals.contains(dst) && part.locals.contains(src) =>
                {
                    alive.remove(src);
                    alive.insert(*dst);
                    continue;
                }
                Statement::Release(l) if part.locals.contains(l) => {
                    alive.remove(l);
                    continue;
                }
                _ => {}
            }
            if alive.is_empty() {
                continue;
            }
            let uses = statement_uses(body, &live.holds, statement);
            if uses.consumed.contains(&source) || uses.def == Some(source) {
                return false;
            }
        }
        if alive.is_empty() {
            continue;
        }
        let uses = terminator_uses(body, &live.holds, &live.lent, &block.terminator);
        let defines = matches!(
            &block.terminator,
            Terminator::Call { dst, .. } | Terminator::CallValue { dst, .. } if *dst == source
        );
        if uses.consumed.contains(&source) || defines {
            return false;
        }
    }
    true
}
