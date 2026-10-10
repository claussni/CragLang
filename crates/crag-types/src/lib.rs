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

//! Crag's types and type inference (Implementation Plan §11.4.7).
//!
//! Written types are lowered to interned `Ty` terms: `type_def` and
//! `signature` lower declarations, `result_type` and `value_type` give
//! the types other bodies use: a call gives the callee's success type and
//! the errors inferred for its recursive group (§11.5.2). `bounds`,
//! `form_def` and `slots` lower what generic functions require, and
//! `instantiate` fits type arguments to them (§11.5.3). `body_types`
//! infers one body: a type for every expression, pattern and binding, the
//! target of every call, and the type errors.

extern crate crag_db as salsa;

mod case;
mod decision;
mod def;
mod effect;
mod generic;
mod group;
mod infer;
mod overload;
mod relate;
mod result;
mod ty;

use crag_db::Db;
use crag_hir::{ItemKind, ModuleId, Owner, Program, owners};

pub use case::{ListLen, Value};
pub use decision::{Bindings, DecisionTree, Position, Step, decision_tree};
pub use def::{
    FieldDef, HeaderKind, SigParam, Signature, TypeDef, TypeDefKind, TypeHeader, alias_target,
    prelude_item, signature, success_type, type_def, type_header, type_parent, value_type,
};
pub use effect::{EffectSet, Restriction};
pub use generic::{
    Bounds, CallSite, Filling, FitError, FormBound, FormDef, Instance, Slot, bounds, form_def,
    instantiate, param_bound, slots, type_param_names,
};
pub use group::{
    Group, GroupMember, callees, error_members, error_type, function_effects, group_errors,
    group_of, recursion_errors, result_type, success_members,
};
pub use infer::constant as literal_value;
pub use overload::{Ranked, Specificity, compare_param, most_specific, overload_errors};
pub use relate::{declared_fields, fields_of, is_subtype, join, normalize, parent, subst};
pub use result::{Callee, Dispatch, DispatchArm, ErrorKind, InferenceResult, Site, TypeError};
pub use ty::{Builtin, Ty, TyKind};

/// The types of a body: a function, a module-level `let`, a test, or the
/// field defaults of a type declaration.
#[crag_db::tracked(returns(ref))]
pub fn body_types<'db>(
    db: &'db dyn Db,
    program: Program,
    owner: Owner<'db>,
) -> InferenceResult<'db> {
    infer::infer(db, program, owner)
}

/// Every type error of a module, with the owner of the body it is in,
/// whose source map gives its range.
pub fn module_type_errors<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<(Owner<'db>, TypeError<'db>)> {
    let mut errors: Vec<(Owner<'db>, TypeError<'db>)> = overload_errors(db, program, module)
        .iter()
        .chain(recursion_errors(db, program, module))
        .map(|(item, e)| (Owner::Item(*item), e.clone()))
        .collect();
    for owner in owners(db, module) {
        if let Owner::Item(item) = owner
            && *item.kind(db) == ItemKind::Type
        {
            let def = type_def(db, program, item);
            errors.extend(def.errors.iter().map(|e| (owner, e.clone())));
        }
        if let Owner::Item(item) = owner {
            let found = match *item.kind(db) {
                ItemKind::Function | ItemKind::Type => &bounds(db, program, item).errors,
                ItemKind::Form => &form_def(db, program, item).errors,
                _ => &Vec::new(),
            };
            errors.extend(found.iter().map(|e| (owner, e.clone())));
        }
        let result = body_types(db, program, owner);
        errors.extend(result.errors.iter().map(|e| (owner, e.clone())));
    }
    errors
}
