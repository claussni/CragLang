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

//! Borrowed parameters (Implementation Plan §11.10.1), after Perceus: a
//! parameter that a function only reads is borrowed, so that neither the
//! caller nor the function counts it. The caller keeps its reference
//! across the call; the function neither releases the value nor lists it
//! in its stack maps.
//!
//! A parameter stays owned when the function gives its value away: into a
//! record, a collection, a heap closure, another local or the result, to
//! a call of a function value, or to a parameter that is owned in turn.
//! Only a function's body borrows: other code is called as a value or by
//! the runtime, which give their arguments away. Records, and unions with
//! a record member, stay owned too, since they may pass by value in their
//! storage form (§11.10.10), whose references the callee takes.
//!
//! A tail call leaves no frame to release what it lends. Within a
//! recursive group, a parameter that a tail call passes an owned value to
//! is owned, so that tail-recursive loops stay loops; a tail call out of
//! its group that would lend an owned value becomes an ordinary call. The
//! members of a group are solved together, all borrowed at first, until
//! no more become owned.

use crag_db::Db;
use crag_hir::{ItemKind, Owner, Program, c_function};
use crag_types::{Ty, TyKind, TypeDefKind, type_def};

use crate::build::counted;
use crate::ir::{Block, BlockId, Local, LocalDecl, MirBody, Operand, Statement, Terminator};
use crate::liveness::{Lent, LocalSet, statement_uses};
use crate::{Entry, InstanceKey, built};

/// Which parameters of an instance are borrowed, in order; empty for code
/// that borrows none.
#[crag_db::tracked(returns(ref))]
pub fn borrows<'db>(db: &'db dyn Db, program: Program, instance: InstanceKey<'db>) -> Vec<bool> {
    if !eligible(db, program, instance) {
        return Vec::new();
    }
    let group = group(db, program, instance);
    let mut solved = solve(db, program, &group);
    let k = group
        .iter()
        .position(|&m| m == instance)
        .expect("an instance is in its group");
    let own = solved.swap_remove(k);
    match own.contains(&true) {
        true => own,
        false => Vec::new(),
    }
}

/// Whether the instance is a function's body with parameters, which only
/// calls in generated code reach.
fn eligible<'db>(db: &'db dyn Db, program: Program, instance: InstanceKey<'db>) -> bool {
    let Owner::Item(item) = *instance.owner(db) else {
        return false;
    };
    *instance.entry(db) == Entry::Body
        && *item.kind(db) == ItemKind::Function
        && c_function(db, item).is_none()
        && built(db, program, instance)
            .as_ref()
            .is_some_and(|b| b.params > 0)
}

/// Whether a parameter of the type may be borrowed: a counted value that
/// never passes by value in a storage form.
fn borrowable<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    fn record<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
        match ty.kind(db) {
            TyKind::Record { .. } => true,
            TyKind::Named(item, _) => match type_def(db, program, *item).kind {
                TypeDefKind::Record { .. } => true,
                TypeDefKind::Alias(t) | TypeDefKind::Refined(t) => record(db, program, t),
                _ => false,
            },
            TyKind::Union(members) => members.iter().any(|&m| record(db, program, m)),
            _ => false,
        }
    }
    counted(db, program, ty) && !record(db, program, ty)
}

/// The callees a body calls directly.
fn calls<'a, 'db>(body: &'a MirBody<'db>) -> impl Iterator<Item = InstanceKey<'db>> + 'a {
    body.blocks.iter().filter_map(|b| match &b.terminator {
        Terminator::Call { func, .. } | Terminator::TailCall { func, .. } => Some(*func),
        _ => None,
    })
}

/// The recursive group of an instance: the strongly connected component
/// of direct calls between eligible instances that it is in, by Tarjan's
/// algorithm over what it reaches.
fn group<'db>(db: &'db dyn Db, program: Program, root: InstanceKey<'db>) -> Vec<InstanceKey<'db>> {
    struct Node<'db> {
        instance: InstanceKey<'db>,
        index: usize,
        low: usize,
        on_stack: bool,
        edges: Vec<InstanceKey<'db>>,
    }
    let node = |instance: InstanceKey<'db>, index: usize| {
        let mut edges: Vec<InstanceKey<'db>> = built(db, program, instance)
            .iter()
            .flat_map(calls)
            .filter(|&c| eligible(db, program, c))
            .collect();
        edges.dedup();
        Node {
            instance,
            index,
            low: index,
            on_stack: true,
            edges,
        }
    };
    let mut nodes = vec![node(root, 0)];
    let mut stack = vec![0];
    // A node and how many of its edges it has followed.
    let mut work: Vec<(usize, usize)> = vec![(0, 0)];
    while let Some(&mut (v, ref mut next)) = work.last_mut() {
        if let Some(&w_instance) = nodes[v].edges.get(*next) {
            *next += 1;
            match nodes.iter().position(|n| n.instance == w_instance) {
                None => {
                    let w = nodes.len();
                    nodes.push(node(w_instance, w));
                    stack.push(w);
                    work.push((w, 0));
                }
                Some(w) if nodes[w].on_stack => nodes[v].low = nodes[v].low.min(nodes[w].index),
                Some(_) => {}
            }
            continue;
        }
        work.pop();
        if let Some(&(u, _)) = work.last() {
            nodes[u].low = nodes[u].low.min(nodes[v].low);
        }
        if nodes[v].low == nodes[v].index {
            let mut members = Vec::new();
            loop {
                let w = stack.pop().expect("the component is on the stack");
                nodes[w].on_stack = false;
                members.push(nodes[w].instance);
                if w == v {
                    break;
                }
            }
            // The root's component is the last to close.
            if v == 0 {
                return members;
            }
        }
    }
    unreachable!("the root closes its component")
}

/// The borrowed parameters of each member of a group.
fn solve<'db>(db: &'db dyn Db, program: Program, group: &[InstanceKey<'db>]) -> Vec<Vec<bool>> {
    let bodies: Vec<&MirBody<'db>> = group
        .iter()
        .map(|&m| built(db, program, m).as_ref().expect("an eligible body"))
        .collect();
    let mut borrowed: Vec<Vec<bool>> = bodies
        .iter()
        .map(|body| {
            (0..body.params)
                .map(|p| {
                    borrowable(db, program, body.locals[p].ty) && !assigned(body, Local(p as u32))
                })
                .collect()
        })
        .collect();
    loop {
        let mut owned: Vec<(usize, usize)> = Vec::new();
        for (k, body) in bodies.iter().enumerate() {
            let param = |l: Local| (l.index() < body.params).then_some((k, l.index()));
            let no_holds = vec![LocalSet::new(); body.locals.len()];
            for block in &body.blocks {
                for statement in &block.statements {
                    let uses = statement_uses(body, &no_holds, statement);
                    owned.extend(uses.consumed.into_iter().filter_map(param));
                }
                match &block.terminator {
                    Terminator::Call { func, args, .. }
                    | Terminator::TailCall { func, args, .. } => {
                        let member = group.iter().position(|m| m == func);
                        let lends = match member {
                            Some(j) => borrowed[j].clone(),
                            None => borrows(db, program, *func).clone(),
                        };
                        let tail = matches!(block.terminator, Terminator::TailCall { .. });
                        for (i, arg) in args.iter().enumerate() {
                            let Operand::Local(l) = arg else { continue };
                            if !lends.get(i).copied().unwrap_or(false) {
                                owned.extend(param(*l));
                                continue;
                            }
                            // A tail call within the group lends only what
                            // its caller borrows.
                            let lent = param(*l).is_some_and(|(_, p)| borrowed[k][p]);
                            if let (true, Some(j)) = (tail, member)
                                && body.locals[l.index()].counted
                                && !lent
                            {
                                owned.push((j, i));
                            }
                        }
                    }
                    Terminator::CallValue { callee, args, .. }
                    | Terminator::TailCallValue { callee, args, .. } => {
                        for o in std::iter::once(callee).chain(args) {
                            if let Operand::Local(l) = o {
                                owned.extend(param(*l));
                            }
                        }
                    }
                    Terminator::Return(Operand::Local(l)) => owned.extend(param(*l)),
                    _ => {}
                }
            }
        }
        let mut changed = false;
        for (k, p) in owned {
            changed |= std::mem::replace(&mut borrowed[k][p], false);
        }
        if !changed {
            return borrowed;
        }
    }
}

/// Whether the body assigns the local anywhere.
pub(crate) fn assigned(body: &MirBody<'_>, local: Local) -> bool {
    body.blocks.iter().any(|block| {
        let assigns = block
            .statements
            .iter()
            .any(|s| matches!(s, Statement::Assign(dst, _) if *dst == local));
        let calls = matches!(
            block.terminator,
            Terminator::Call { dst, .. } | Terminator::CallValue { dst, .. } if dst == local
        );
        assigns || calls
    })
}

/// Marks the borrowed parameters of the body, which are not counted, and
/// gives the parameters each callee borrows. A tail call that would lend
/// an owned value becomes a call whose result is returned, so that the
/// frame lives to release it.
pub(crate) fn lend<'db>(
    db: &'db dyn Db,
    program: Program,
    instance: InstanceKey<'db>,
    body: &mut MirBody<'db>,
) -> Lent<'db> {
    for (p, &b) in borrows(db, program, instance).iter().enumerate() {
        if b {
            body.locals[p].borrowed = true;
            body.locals[p].counted = false;
        }
    }
    let lent: Lent<'db> = calls(body)
        .map(|func| (func, borrows(db, program, func).clone()))
        .collect();
    for b in 0..body.blocks.len() {
        let Terminator::TailCall { func, args, site } = &body.blocks[b].terminator else {
            continue;
        };
        let lends = &lent[func];
        let lends_owned = args.iter().enumerate().any(|(i, arg)| {
            matches!(arg, Operand::Local(l) if body.locals[l.index()].counted)
                && lends.get(i).copied().unwrap_or(false)
        });
        if !lends_owned {
            continue;
        }
        let (func, args, site) = (*func, args.clone(), *site);
        let dst = Local(body.locals.len() as u32);
        body.locals.push(LocalDecl {
            ty: body.result,
            binding: None,
            counted: counted(db, program, body.result),
            split: false,
            borrowed: false,
        });
        let catch = body.blocks[b].catch;
        body.blocks.push(Block {
            statements: Vec::new(),
            terminator: Terminator::Return(Operand::Local(dst)),
            catch,
            inlined: body.blocks[b].inlined,
        });
        let target = BlockId(body.blocks.len() as u32 - 1);
        body.blocks[b].terminator = Terminator::Call {
            func,
            args,
            dst,
            target,
            site,
            unwind: None,
            catch,
        };
    }
    lent
}
