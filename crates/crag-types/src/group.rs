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

//! Error inference over recursive groups (Implementation Plan §11.5.2).
//!
//! A function's errors are the error members of what its body gives, and
//! a call gives the callee's success type and errors. Functions whose
//! inference needs each other form a group: a strongly connected component
//! of the graph of the functions each body names, found by Tarjan's
//! algorithm. A group's errors start empty and grow by what its bodies
//! give, each inferred with the errors found so far, until nothing
//! changes. Unions only grow, and only from the program's types, so this
//! ends.
//!
//! The graph counts every function a body names, every overload of a call
//! included, because inference compares them all (§3.13.1).

use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{Expr, ItemId, ItemKind, Owner, Program, Resolution, hir_body, type_identity};

use crate::def::{prelude_item, signature, success_type};
use crate::infer::infer_in_group;
use crate::relate::{is_subtype, join, normalize};
use crate::ty::{Ty, TyKind};

/// The functions a function's body names: in calls, as values and as the
/// candidates of method calls and fields.
#[crag_db::tracked(returns(ref))]
pub fn callees<'db>(db: &'db dyn Db, program: Program, function: ItemId<'db>) -> Vec<ItemId<'db>> {
    let body = hir_body(db, program, Owner::Item(function));
    let mut callees = Vec::new();
    for expr in &body.exprs {
        let functions = match expr {
            Expr::Name {
                item: Some(Resolution::Value { functions, .. }),
                ..
            }
            | Expr::MethodCall { functions, .. }
            | Expr::TypedCall { functions, .. }
            | Expr::Field { functions, .. } => functions,
            _ => continue,
        };
        for &f in functions {
            if *f.kind(db) == ItemKind::Function && !callees.contains(&f) {
                callees.push(f);
            }
        }
    }
    callees
}

/// The group of a function: the strongly connected component of `callees`
/// it is in, its members in a fixed order.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Group<'db> {
    pub members: Vec<ItemId<'db>>,
    /// Whether the members depend on themselves: more than one, or one
    /// that names itself.
    pub recursive: bool,
}

/// Tarjan's algorithm over the functions reachable from `function`,
/// stopping at its component.
#[crag_db::tracked(returns(ref))]
pub fn group_of<'db>(db: &'db dyn Db, program: Program, function: ItemId<'db>) -> Group<'db> {
    struct Node<'db> {
        item: ItemId<'db>,
        index: usize,
        low: usize,
        on_stack: bool,
    }
    let mut nodes: Vec<Node<'db>> = Vec::new();
    let mut stack: Vec<usize> = Vec::new();
    // The explicit call stack: a node and how many of its callees it has
    // visited.
    let mut work: Vec<(usize, usize)> = Vec::new();
    let find = |nodes: &[Node<'db>], item: ItemId<'db>| nodes.iter().position(|n| n.item == item);
    nodes.push(Node {
        item: function,
        index: 0,
        low: 0,
        on_stack: true,
    });
    stack.push(0);
    work.push((0, 0));
    while let Some(&mut (v, ref mut next)) = work.last_mut() {
        let edges = callees(db, program, nodes[v].item);
        if let Some(&w_item) = edges.get(*next) {
            *next += 1;
            match find(&nodes, w_item) {
                None => {
                    let w = nodes.len();
                    nodes.push(Node {
                        item: w_item,
                        index: w,
                        low: w,
                        on_stack: true,
                    });
                    stack.push(w);
                    work.push((w, 0));
                }
                Some(w) if nodes[w].on_stack => {
                    nodes[v].low = nodes[v].low.min(nodes[w].index);
                }
                Some(_) => {}
            }
            continue;
        }
        work.pop();
        if let Some(&(parent, _)) = work.last() {
            nodes[parent].low = nodes[parent].low.min(nodes[v].low);
        }
        if nodes[v].low == nodes[v].index {
            let mut members = Vec::new();
            loop {
                let w = stack.pop().expect("v is on the stack");
                nodes[w].on_stack = false;
                members.push(nodes[w].item);
                if w == v {
                    break;
                }
            }
            if v == 0 {
                members.sort_by_key(|m| m.as_id());
                let recursive =
                    members.len() > 1 || callees(db, program, function).contains(&function);
                return Group { members, recursive };
            }
        }
    }
    unreachable!("the root closes its component")
}

/// The errors of each member of the group whose first member is `root`,
/// solved together.
#[crag_db::tracked(returns(ref), cycle_result = group_errors_cycle)]
pub fn group_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    root: ItemId<'db>,
) -> Vec<(ItemId<'db>, Ty<'db>)> {
    let group = group_of(db, program, root);
    let never = Ty::never(db);
    let mut errors: Vec<(ItemId<'db>, Ty<'db>)> =
        group.members.iter().map(|&m| (m, never)).collect();
    loop {
        let mut grew = false;
        for i in 0..errors.len() {
            let member = errors[i].0;
            let result = infer_in_group(db, program, Owner::Item(member), &errors).result;
            let found = result.map_or(never, |r| error_members(db, program, r));
            let joined = join(db, program, errors[i].1, found);
            if joined != errors[i].1 {
                errors[i].1 = joined;
                grew = true;
            }
        }
        if !grew || !group.recursive {
            return errors;
        }
    }
}

fn group_errors_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _root: ItemId<'db>,
) -> Vec<(ItemId<'db>, Ty<'db>)> {
    Vec::new()
}

/// What a call of `function` gives: its success type and its errors. None
/// for a function that states no success type and depends on itself, or
/// whose inferred type depends on itself (§3.13.1).
#[crag_db::tracked(returns(copy), cycle_result = result_cycle)]
pub fn result_type<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
) -> Option<Ty<'db>> {
    let group = group_of(db, program, function);
    match signature(db, program, function).result {
        Some(success) => {
            let root = group.members[0];
            let errors = group_errors(db, program, root)
                .iter()
                .find(|(m, _)| *m == function)
                .map_or(Ty::never(db), |(_, e)| *e);
            Some(join(db, program, success, errors))
        }
        None if group.recursive => None,
        None => success_type(db, program, function),
    }
}

fn result_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _function: ItemId<'db>,
) -> Option<Ty<'db>> {
    None
}

/// The prelude's `Error`, the parent of every error type (§8.1).
pub fn error_type<'db>(db: &'db dyn Db, program: Program) -> Option<Ty<'db>> {
    let item = prelude_item(db, program, "Error")?;
    let identity = type_identity(db, program, item);
    Some(Ty::new(db, TyKind::Named(identity, Vec::new())))
}

/// The members of `ty` that are errors.
pub fn error_members<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Ty<'db> {
    let Some(error) = error_type(db, program) else {
        return Ty::never(db);
    };
    let members = ty
        .members(db)
        .into_iter()
        .filter(|&m| !m.is_error(db) && is_subtype(db, program, m, error))
        .collect();
    normalize(db, program, members).0
}

/// The members of `ty` that are not errors.
pub fn success_members<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Ty<'db> {
    let Some(error) = error_type(db, program) else {
        return ty;
    };
    let members = ty
        .members(db)
        .into_iter()
        .filter(|&m| m.is_error(db) || !is_subtype(db, program, m, error))
        .collect();
    normalize(db, program, members).0
}
