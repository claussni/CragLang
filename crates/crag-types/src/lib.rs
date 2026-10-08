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
//! `signature` lower declarations, `success_type` and `value_type` give
//! the types other bodies use. `body_types` infers one body: a type for
//! every expression, pattern and binding, the target of every call, and
//! the type errors.

extern crate crag_db as salsa;

mod case;
mod def;
mod infer;
mod relate;
mod result;
mod ty;

use crag_db::Db;
use crag_hir::{ItemKind, ModuleId, Owner, Program, owners};

pub use def::{
    FieldDef, HeaderKind, SigParam, Signature, TypeDef, TypeDefKind, TypeHeader, alias_target,
    signature, success_type, type_def, type_header, type_parent, value_type,
};
pub use relate::{declared_fields, fields_of, is_subtype, join, normalize, parent, subst};
pub use result::{Callee, ErrorKind, InferenceResult, Site, TypeError};
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
    let mut errors = Vec::new();
    for owner in owners(db, module) {
        if let Owner::Item(item) = owner
            && *item.kind(db) == ItemKind::Type
        {
            let def = type_def(db, program, item);
            errors.extend(def.errors.iter().map(|e| (owner, e.clone())));
        }
        let result = body_types(db, program, owner);
        errors.extend(result.errors.iter().map(|e| (owner, e.clone())));
    }
    errors
}
