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

//! The no-shadowing rule (§5.4): a binding may not take a name already in
//! scope, whether a binding of an enclosing scope, a module-level value, or
//! a visible type or form. Functions are not bindings, so a binding may
//! share a name with them. Lowering checks the rule while it resolves
//! names; this collects what it found in a module's bodies.

use std::ops::Range;

use crag_db::Db;

use crate::body::{lower_body, owners};
use crate::input::{ModuleId, Program};
use crate::items::ItemId;
use crate::lower::LowerError;

/// A binding that takes a name already in scope.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Redeclaration<'db> {
    pub name: String,
    pub range: Range<u32>,
    pub previous: Previous<'db>,
}

/// What first had the name.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Previous<'db> {
    /// A binding of the same body, at this range of the file.
    Local(Range<u32>),
    /// A module-level value, a type or a form.
    Item(ItemId<'db>),
}

#[crag_db::tracked(returns(ref))]
pub fn check_shadowing<'db>(
    db: &'db dyn Db,
    program: Program,
    module: ModuleId,
) -> Vec<Redeclaration<'db>> {
    owners(db, module)
        .into_iter()
        .flat_map(|owner| &lower_body(db, program, owner).errors)
        .filter_map(|error| match error {
            LowerError::Redeclared(redeclaration) => Some(redeclaration.clone()),
            _ => None,
        })
        .collect()
}
