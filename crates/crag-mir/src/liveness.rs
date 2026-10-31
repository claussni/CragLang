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

//! Reference counts from liveness.
//!
//! A counted local owns one reference while it is live. A use either
//! consumes that reference (an operand: the value moves into a call, a
//! record, another local, the result) or borrows it (a place, a test, an
//! operation on it). So the reference must be duplicated before every
//! consuming use but the last, given up after a last use that only
//! borrows, and given up where the value dies unused: after a definition
//! nothing reads, at the start of a function for an unused parameter, and
//! on the edges into blocks that no longer need it. A part read out of a
//! value is borrowed from it and gets a reference of its own when it lives
//! on. A closure whose environment is on the side stack borrows what it
//! captured, so a use of it, or of a copy of it, uses those locals too.
//! A call borrows the arguments of the parameters its callee borrows
//! (Implementation Plan §11.10.1), and a borrowed parameter is not counted.

use std::collections::{BTreeSet, HashMap};

use crate::InstanceKey;
use crate::ir::{
    BlockId, ClosurePlacement, Intrinsic, Local, MirBody, Operand, Place, Rvalue, Statement,
    Terminator,
};

pub type LocalSet = BTreeSet<Local>;

/// Which parameters of each callee are borrowed, by `crate::borrows`.
pub type Lent<'db> = HashMap<InstanceKey<'db>, Vec<bool>>;

/// The counted locals live at the edges of each block.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Liveness<'db> {
    /// Live on entry.
    pub live_in: Vec<LocalSet>,
    /// Live after the terminator has used its operands: what a successor
    /// needs. A call's result is not among them.
    pub live_out: Vec<LocalSet>,
    /// The locals each local's value borrows: the captures of a closure on
    /// the side stack, for it and its copies.
    pub holds: Vec<LocalSet>,
    /// The parameters the callees borrow.
    pub lent: Lent<'db>,
}

/// The locals each local borrows through the side-stack closures it may
/// hold.
fn holds(body: &MirBody<'_>) -> Vec<LocalSet> {
    let mut holds = vec![LocalSet::new(); body.locals.len()];
    loop {
        let mut changed = false;
        for block in &body.blocks {
            for statement in &block.statements {
                let Statement::Assign(dst, rvalue) = statement else {
                    continue;
                };
                let mut add = LocalSet::new();
                match rvalue {
                    Rvalue::Closure {
                        captures,
                        placement: ClosurePlacement::SideStack,
                        ..
                    } => {
                        for c in captures {
                            if let Operand::Local(l) = c {
                                add.insert(*l);
                                add.extend(holds[l.index()].iter().copied());
                            }
                        }
                    }
                    Rvalue::Use(Operand::Local(src)) | Rvalue::Convert(Operand::Local(src)) => {
                        add.extend(holds[src.index()].iter().copied());
                    }
                    _ => {}
                }
                add.remove(dst);
                let before = holds[dst.index()].len();
                holds[dst.index()].extend(add);
                changed |= holds[dst.index()].len() != before;
            }
        }
        if !changed {
            return holds;
        }
    }
}

/// How a statement or terminator uses locals.
#[derive(Default)]
pub(crate) struct Uses {
    pub(crate) def: Option<Local>,
    /// One entry per consuming use.
    pub(crate) consumed: Vec<Local>,
    pub(crate) borrowed: Vec<Local>,
}

impl Uses {
    fn operand(&mut self, op: &Operand<'_>, consume: bool) {
        if let Operand::Local(l) = op {
            match consume {
                true => self.consumed.push(*l),
                false => self.borrowed.push(*l),
            }
        }
    }

    fn place(&mut self, place: &Place<'_>) {
        self.borrowed.push(place.local);
    }

    /// Only the counted locals, with those the used ones hold borrowed.
    fn counted(mut self, body: &MirBody<'_>, holds: &[LocalSet]) -> Uses {
        let held: Vec<Local> = self
            .all()
            .flat_map(|l| holds[l.index()].iter().copied())
            .collect();
        self.borrowed.extend(held);
        let counted = |l: &Local| body.locals[l.index()].counted;
        self.consumed.retain(counted);
        self.borrowed.retain(counted);
        self.def = self.def.filter(counted);
        self
    }

    fn all(&self) -> impl Iterator<Item = Local> + '_ {
        self.consumed.iter().chain(&self.borrowed).copied()
    }
}

pub(crate) fn statement_uses(
    body: &MirBody<'_>,
    holds: &[LocalSet],
    statement: &Statement<'_>,
) -> Uses {
    let mut uses = Uses::default();
    match statement {
        Statement::Assign(dst, rvalue) => {
            uses.def = Some(*dst);
            match rvalue {
                Rvalue::Use(o) | Rvalue::Convert(o) | Rvalue::FnValue { env: o, .. } => {
                    uses.operand(o, true)
                }
                Rvalue::Read(p) | Rvalue::Len(p) | Rvalue::Slice { list: p, .. } => uses.place(p),
                Rvalue::Index { list: p, index: o } | Rvalue::MapGet { map: p, key: o, .. } => {
                    uses.place(p);
                    uses.operand(o, false);
                }
                Rvalue::Binary { a, b, .. }
                | Rvalue::Overflows { a, b, .. }
                | Rvalue::Compare { a, b, .. } => {
                    uses.operand(a, false);
                    uses.operand(b, false);
                }
                Rvalue::Cast { value, .. } => uses.operand(value, false),
                Rvalue::FloatOverflow(locals) => uses.borrowed.extend(locals),
                Rvalue::Record { fields, reuse, .. } => {
                    for (_, o) in fields {
                        uses.operand(o, true);
                    }
                    uses.consumed.extend(reuse);
                }
                Rvalue::List(items) => {
                    for o in items {
                        uses.operand(o, true);
                    }
                }
                Rvalue::Map(entries) => {
                    for (k, v) in entries {
                        uses.operand(k, true);
                        uses.operand(v, true);
                    }
                }
                Rvalue::Intrinsic(intrinsic, args) => {
                    for (k, o) in args.iter().enumerate() {
                        uses.operand(o, intrinsic.consumes(k));
                    }
                }
                Rvalue::Concat(parts) => {
                    for o in parts {
                        uses.operand(o, false);
                    }
                }
                Rvalue::Closure {
                    captures,
                    placement,
                    ..
                } => {
                    let consume = *placement == ClosurePlacement::Heap;
                    for o in captures {
                        uses.operand(o, consume);
                    }
                }
            }
        }
        Statement::Retain(l) => uses.borrowed.push(*l),
        Statement::Release(l) => uses.consumed.push(*l),
        Statement::Reclaim { local, token } => {
            uses.consumed.push(*local);
            uses.def = Some(*token);
        }
        Statement::Poll | Statement::Step { .. } => {}
    }
    uses.counted(body, holds)
}

fn terminator_uses<'db>(
    body: &MirBody<'db>,
    holds: &[LocalSet],
    lent: &Lent<'db>,
    terminator: &Terminator<'db>,
) -> Uses {
    let mut uses = Uses::default();
    match terminator {
        Terminator::Branch { cond, .. } => uses.operand(cond, false),
        Terminator::Switch { place, .. } => uses.place(place),
        Terminator::Call { func, args, .. } | Terminator::TailCall { func, args, .. } => {
            let borrowed = lent.get(func).map_or(&[][..], Vec::as_slice);
            for (k, o) in args.iter().enumerate() {
                uses.operand(o, !borrowed.get(k).copied().unwrap_or(false));
            }
        }
        Terminator::CallValue { callee, args, .. }
        | Terminator::TailCallValue { callee, args, .. } => {
            uses.operand(callee, true);
            for o in args {
                uses.operand(o, true);
            }
        }
        Terminator::Return(o) => uses.operand(o, true),
        Terminator::Jump(_) | Terminator::Trap { .. } | Terminator::Guard { .. } => {}
    }
    uses.counted(body, holds)
}

/// Whether the rvalue's result is borrowed from what it reads.
fn borrows(rvalue: &Rvalue<'_>) -> bool {
    matches!(
        rvalue,
        Rvalue::Read(_)
            | Rvalue::Index { .. }
            | Rvalue::MapGet { boxed: false, .. }
            | Rvalue::Intrinsic(
                Intrinsic::RefValue | Intrinsic::ExtValue | Intrinsic::LazyCode,
                _
            )
    )
}

/// What a successor needs from a block.
fn needed(live_in: &[LocalSet], terminator: &Terminator<'_>, successor: BlockId) -> LocalSet {
    let mut set = live_in[successor.index()].clone();
    if let Terminator::Call { dst, .. } | Terminator::CallValue { dst, .. } = terminator {
        set.remove(dst);
    }
    set
}

pub fn compute_liveness<'db>(body: &MirBody<'db>, lent: Lent<'db>) -> Liveness<'db> {
    let n = body.blocks.len();
    let mut live = Liveness {
        live_in: vec![LocalSet::new(); n],
        live_out: vec![LocalSet::new(); n],
        holds: holds(body),
        lent,
    };
    let holds = live.holds.clone();
    loop {
        let mut changed = false;
        for b in (0..n).rev() {
            let block = &body.blocks[b];
            let mut out = LocalSet::new();
            for s in block.terminator.successors() {
                out.extend(needed(&live.live_in, &block.terminator, s));
            }
            let mut set = out.clone();
            set.extend(terminator_uses(body, &holds, &live.lent, &block.terminator).all());
            for statement in block.statements.iter().rev() {
                let uses = statement_uses(body, &holds, statement);
                if let Some(def) = uses.def {
                    set.remove(&def);
                }
                set.extend(uses.all());
            }
            if set != live.live_in[b] || out != live.live_out[b] {
                live.live_in[b] = set;
                live.live_out[b] = out;
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// Retains before every consuming use but the last, releases after a last
/// use that borrows, and retains a part read out of a value that lives on.
pub fn insert_rc_ops<'db>(body: &mut MirBody<'db>, live: &Liveness<'db>) {
    for b in 0..body.blocks.len() {
        let block = &body.blocks[b];
        let mut set = live.live_out[b].clone();
        let mut reversed = Vec::new();
        // A terminator consumes or borrows; those it borrows last die on
        // its edges, which `insert_drops` handles.
        let uses = terminator_uses(body, &live.holds, &live.lent, &block.terminator);
        // What a successor needs after a call, the handler's path too.
        let kept = match &block.terminator {
            Terminator::Call { .. } | Terminator::CallValue { .. } => block
                .terminator
                .successors()
                .into_iter()
                .flat_map(|s| needed(&live.live_in, &block.terminator, s))
                .collect(),
            _ => set.clone(),
        };
        // A value the call also borrows lives through it, and dies after.
        for x in distinct(&uses.consumed) {
            let count = uses.consumed.iter().filter(|&&l| l == x).count();
            let retains = match kept.contains(&x) || uses.borrowed.contains(&x) {
                true => count,
                false => count - 1,
            };
            reversed.extend(std::iter::repeat_n(Statement::Retain(x), retains));
        }
        set.extend(uses.all());
        for statement in block.statements.iter().rev() {
            let uses = statement_uses(body, &live.holds, statement);
            let mut after = Vec::new();
            let mut before = Vec::new();
            if let (Statement::Assign(dst, rvalue), Some(def)) = (statement, uses.def)
                && borrows(rvalue)
                && set.contains(dst)
            {
                after.push(Statement::Retain(def));
            }
            for x in distinct(&uses.all().collect::<Vec<_>>()) {
                let count = uses.consumed.iter().filter(|&&l| l == x).count();
                let borrowed = uses.borrowed.contains(&x);
                let (retains, release) = if set.contains(&x) {
                    (count, false)
                } else if count > 0 && !borrowed {
                    (count - 1, false)
                } else {
                    (count, true)
                };
                before.extend(std::iter::repeat_n(Statement::Retain(x), retains));
                if release {
                    after.push(Statement::Release(x));
                }
            }
            reversed.extend(after.into_iter().rev());
            match statement {
                // A step shows what holds a value: a counted local only
                // while it is live, since it may be released before.
                Statement::Step { at, locals } => reversed.push(Statement::Step {
                    at: *at,
                    locals: locals
                        .iter()
                        .copied()
                        .filter(|l| !body.locals[l.index()].counted || set.contains(l))
                        .collect(),
                }),
                _ => reversed.push(statement.clone()),
            }
            reversed.extend(before.into_iter().rev());
            if let Some(def) = uses.def {
                set.remove(&def);
            }
            set.extend(uses.all());
        }
        reversed.reverse();
        body.blocks[b].statements = reversed;
    }
}

/// Releases what dies unused: a definition no one reads, a parameter, and
/// what a block holds that a successor does not need, on that edge.
pub fn insert_drops<'db>(body: &mut MirBody<'db>, live: &Liveness<'db>) {
    let n = body.blocks.len();
    let mut incoming = vec![0usize; n];
    for block in &body.blocks {
        for s in block.terminator.successors() {
            incoming[s.index()] += 1;
        }
    }
    // Releases at the start of blocks, applied after the walk.
    let mut starts: Vec<Vec<Statement<'_>>> = vec![Vec::new(); n];
    for b in 0..n {
        let block = &body.blocks[b];
        let term_uses = terminator_uses(body, &live.holds, &live.lent, &block.terminator);
        let mut set = live.live_out[b].clone();
        let held: LocalSet = set
            .iter()
            .copied()
            .chain(term_uses.borrowed.iter().copied())
            .collect();
        set.extend(term_uses.all());
        let mut statements = Vec::new();
        for statement in block.statements.iter().rev() {
            let uses = statement_uses(body, &live.holds, statement);
            if let (Statement::Assign(_, rvalue), Some(def)) = (statement, uses.def)
                && !borrows(rvalue)
                && !set.contains(&def)
            {
                statements.push(Statement::Release(def));
            }
            statements.push(statement.clone());
            if let Some(def) = uses.def {
                set.remove(&def);
            }
            set.extend(uses.all());
        }
        statements.reverse();
        body.blocks[b].statements = statements;
        // The edges.
        let terminator = body.blocks[b].terminator.clone();
        let mut edges: Vec<(usize, Vec<Local>)> = Vec::new();
        for (k, s) in terminator.successors().into_iter().enumerate() {
            let dying: Vec<Local> = match &terminator {
                // What a call borrows dies after it returns, with a result
                // no one reads.
                // The handler's path, after the first, gets no result.
                Terminator::Call { dst, .. } | Terminator::CallValue { dst, .. } => {
                    let mut dying: Vec<Local> =
                        held.difference(&live.live_in[s.index()]).copied().collect();
                    let counted = body.locals[dst.index()].counted;
                    if counted && !live.live_in[s.index()].contains(dst) && k == 0 {
                        dying.push(*dst);
                    }
                    dying
                }
                _ => held.difference(&live.live_in[s.index()]).copied().collect(),
            };
            if !dying.is_empty() {
                edges.push((k, dying));
            }
        }
        for (k, dying) in edges {
            let releases = dying.into_iter().map(Statement::Release);
            let s = body.blocks[b].terminator.successors()[k];
            if incoming[s.index()] == 1 {
                starts[s.index()].extend(releases);
                continue;
            }
            body.blocks.push(crate::ir::Block {
                statements: releases.collect(),
                terminator: Terminator::Jump(s),
                catch: None,
                inlined: body.blocks[b].inlined,
            });
            let edge = BlockId(body.blocks.len() as u32 - 1);
            *body.blocks[b].terminator.successors_mut()[k] = edge;
        }
    }
    let unused: Vec<Statement<'_>> = (0..body.params)
        .map(|p| Local(p as u32))
        .filter(|p| body.locals[p.index()].counted && !live.live_in[0].contains(p))
        .map(Statement::Release)
        .collect();
    starts[0].splice(0..0, unused);
    for (b, start) in starts.into_iter().enumerate() {
        if !start.is_empty() {
            body.blocks[b].statements.splice(0..0, start);
        }
    }
}

fn distinct(locals: &[Local]) -> Vec<Local> {
    let mut out: Vec<Local> = Vec::new();
    for &l in locals {
        if !out.contains(&l) {
            out.push(l);
        }
    }
    out
}
