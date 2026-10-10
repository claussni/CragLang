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
use crag_hir::{
    Body, Expr, ExprId, ItemId, ItemKind, ModuleId, Owner, Program, Resolution, hir_body,
    item_tree, type_identity,
};

use crate::def::{prelude_item, signature, success_type};
use crate::effect::{EffectSet, intrinsic_effects};
use crate::infer::infer_in_group;
use crate::relate::{is_subtype, join, normalize};
use crate::result::{ErrorKind, Site, TypeError};
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
                local: None,
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

/// The diagnostic of each recursive group whose first member without a
/// written success type is in `module` (§3.13.1). It names the group and
/// every member missing a success type, at a call in that member which
/// links it to the group.
#[crag_db::tracked(returns(ref))]
pub fn recursion_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(ItemId<'db>, TypeError<'db>)> {
    let mut errors = Vec::new();
    for item in &item_tree(db, module).items {
        let function = item.id;
        if *function.kind(db) != ItemKind::Function {
            continue;
        }
        let group = group_of(db, program, function);
        if !group.recursive {
            continue;
        }
        let missing: Vec<ItemId<'db>> = group
            .members
            .iter()
            .copied()
            .filter(|&m| signature(db, program, m).result.is_none())
            .collect();
        if missing.first() != Some(&function) {
            continue;
        }
        let body = hir_body(db, program, Owner::Item(function));
        let Some(call) = linking_call(body, &group.members) else {
            continue;
        };
        let kind = ErrorKind::RecursiveGroup {
            members: group.members.clone(),
            missing,
        };
        errors.push((
            function,
            TypeError {
                site: Site::Expr(call),
                kind,
            },
        ));
    }
    errors
}

/// The first call in a body of one of `members`, or the first use of one
/// as a value.
fn linking_call<'db>(body: &Body<'db>, members: &[ItemId<'db>]) -> Option<ExprId> {
    let names = |expr: &Expr<'db>| match expr {
        Expr::Name {
            local: None,
            item: Some(Resolution::Value { functions, .. }),
            ..
        }
        | Expr::MethodCall { functions, .. }
        | Expr::TypedCall { functions, .. }
        | Expr::Field { functions, .. } => functions.iter().any(|f| members.contains(f)),
        _ => false,
    };
    let callees: Vec<ExprId> = body
        .exprs
        .iter()
        .filter_map(|e| match e {
            Expr::Call { callee, .. } => Some(*callee),
            _ => None,
        })
        .collect();
    body.exprs.iter().enumerate().find_map(|(i, expr)| {
        let id = ExprId(i as u32);
        let linked = match expr {
            Expr::Call { callee, .. } => names(body.expr(*callee)),
            Expr::Name { .. } => names(expr) && !callees.contains(&id),
            _ => names(expr),
        };
        linked.then_some(id)
    })
}

/// What the solution of a group says of one member so far.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct GroupMember<'db> {
    pub function: ItemId<'db>,
    pub errors: Ty<'db>,
    pub effects: EffectSet,
}

/// The errors and effects of each member of the group whose first member
/// is `root`, solved together: both start empty and grow until nothing
/// changes (§11.5.2, §11.5.7).
#[crag_db::tracked(returns(ref), cycle_result = group_errors_cycle)]
pub fn group_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    root: ItemId<'db>,
) -> Vec<GroupMember<'db>> {
    let group = group_of(db, program, root);
    let never = Ty::never(db);
    let mut members: Vec<GroupMember<'db>> = group
        .members
        .iter()
        .map(|&function| GroupMember {
            function,
            errors: never,
            effects: EffectSet::NONE,
        })
        .collect();
    loop {
        let mut grew = false;
        for i in 0..members.len() {
            let function = members[i].function;
            let inferred = infer_in_group(db, program, Owner::Item(function), &members);
            let found = inferred
                .result
                .map_or(never, |r| error_members(db, program, r));
            let errors = join(db, program, members[i].errors, found);
            let effects = members[i].effects.union(inferred.effects);
            if errors != members[i].errors || effects != members[i].effects {
                members[i].errors = errors;
                members[i].effects = effects;
                grew = true;
            }
        }
        if !grew || !group.recursive {
            return members;
        }
    }
}

fn group_errors_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _root: ItemId<'db>,
) -> Vec<GroupMember<'db>> {
    Vec::new()
}

/// The effects of a function: of its body and what it calls, with an
/// entry for each closure parameter it calls and each slot (§3.14).
#[crag_db::tracked(returns(copy), cycle_result = function_effects_cycle)]
pub fn function_effects<'db>(
    db: &'db dyn Db,
    program: Program,
    function: ItemId<'db>,
) -> EffectSet {
    if let Some(effects) = intrinsic_effects(db, program, function) {
        return effects;
    }
    let root = group_of(db, program, function).members[0];
    group_errors(db, program, root)
        .iter()
        .find(|m| m.function == function)
        .map_or(EffectSet::NONE, |m| m.effects)
}

/// A function whose effects depend on themselves outside a group, through
/// a module-level value, admits any.
fn function_effects_cycle<'db>(
    _db: &'db dyn Db,
    _id: crag_db::Id,
    _program: Program,
    _function: ItemId<'db>,
) -> EffectSet {
    EffectSet::all()
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
                .find(|m| m.function == function)
                .map_or(Ty::never(db), |m| m.errors);
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
