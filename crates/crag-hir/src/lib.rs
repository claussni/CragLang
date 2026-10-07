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
//! module declares, and later what its names refer to and what its bodies
//! mean.
//!
//! Everything here is a query over the database of `crag-db`. The inputs
//! are source files and the modules they make; `parse` turns a file into a
//! syntax tree, and `item_tree` reads a module's declarations from it.

extern crate crag_db as salsa;

mod input;
mod items;

pub use input::{ModuleId, Parse, SourceFile, parse};
pub use items::{Import, ImportItem, Item, ItemId, ItemKind, ItemTree, Name, Test, item_tree};
