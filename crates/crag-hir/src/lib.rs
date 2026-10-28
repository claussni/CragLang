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

//! Crag's semantic front end (Implementation Plan §11.4.4–§11.4.6): what a
//! module declares, what its names refer to, and its bodies as resolved,
//! desugared trees.
//!
//! Everything here is a query over the database of `crag-db`. The inputs
//! are source files, the modules they make and the program of all modules.
//! `parse` turns a file into a syntax tree, `item_tree` reads a module's
//! declarations from it, `module_scope` adds what the module imports, and
//! `import_graph` checks the rules on imports. `hir_body` lowers a body to
//! the HIR, resolving its names, and `check_shadowing` collects the names
//! its bodies declare twice.

extern crate crag_db as salsa;

mod body;
mod embed;
mod hir;
mod input;
mod items;
pub mod literal;
mod lower;
mod package;
mod patterns;
mod pretty;
mod scope;
mod shadow;

pub use body::{LoweredBody, Owner, hir_body, lower_body, owners, prefixes};
pub use embed::{embed_content, embed_source, embed_sources};
pub use hir::*;
pub use input::{ModuleId, Parse, Program, Resource, SourceFile, parse};
pub use items::{
    CFunction, Import, ImportItem, Item, ItemId, ItemKind, ItemTree, Name, SlotItem, Test, TestId,
    Threading, c_function, c_function_info, form_slots, item_tree, slot_item, type_param_count,
};
pub use literal::Literal;
pub use lower::{BodySourceMap, LowerError};
pub use package::{PackageScope, Packages};
pub use pretty::pretty;
pub use scope::{
    Entries, Entry, ImportCycle, ImportGraph, ImportTarget, Imports, ModuleIndex, ModuleScope,
    NameError, Origin, PRELUDE, PathError, PathTarget, Resolution, Selection, import_graph,
    imports, module_index, module_scope, resolve_path, same_signature, scope_entries,
    type_identity, type_names,
};
pub use shadow::{Previous, Redeclaration, check_shadowing};
