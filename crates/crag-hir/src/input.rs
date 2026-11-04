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

//! The inputs: source files, the modules they make and the program the
//! modules belong to, and the parse of a file.

use std::collections::BTreeMap;
use std::sync::Arc;

use crag_syntax::{GreenNode, ParseError, lex};

use crate::package::Packages;

/// The text of one source file, as a buffer or a file on disk shows it.
#[crag_db::input(debug)]
pub struct SourceFile {
    #[returns(ref)]
    pub text: String,
}

/// A module: one file under its dotted path (§14.1).
#[crag_db::input(debug)]
pub struct ModuleId {
    #[returns(ref)]
    pub path: String,
    pub file: SourceFile,
}

impl ModuleId {
    /// A module at `path` with `text` as its source.
    pub fn of(db: &dyn crag_db::Db, path: &str, text: &str) -> ModuleId {
        ModuleId::new(db, path.to_string(), SourceFile::new(db, text.to_string()))
    }
}

/// The modules of a program: an application with its dependencies, or a
/// REPL session. Paths are unique; of two modules with one path, the first
/// counts.
#[crag_db::input(debug)]
pub struct Program {
    #[returns(ref)]
    pub modules: Vec<ModuleId>,
    /// The resources the modules' `embed` declarations name: the module,
    /// the source as written, and what the driver read (§18.4.1).
    #[returns(ref)]
    pub resources: Vec<(ModuleId, String, Resource)>,
    /// The packages the modules belong to, which limit what each module
    /// may import (§14.5); none for a program of loose modules.
    #[default]
    #[returns(ref)]
    pub packages: Packages,
    /// The type indices of the program this one's code is compiled for,
    /// in place of its own: received code runs on the receiver's heap
    /// (Implementation Plan §11.10.9). Empty for a program of its own.
    #[default]
    #[returns(ref)]
    pub type_indices: TypeIndices,
}

/// The type indices of another program by the canonical hash of each type
/// (Compiler Architecture §A11.2), and the first index past them, from
/// which a type that program does not have takes one of its own.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct TypeIndices {
    pub by_hash: BTreeMap<[u8; 16], u32>,
    pub base: u32,
}

impl TypeIndices {
    pub fn is_empty(&self) -> bool {
        self.by_hash.is_empty() && self.base == 0
    }
}

/// The content of a resource an `embed` names, as the driver read it, or
/// why it could not: a file of the package, read when the program was
/// loaded and again when it changes.
#[crag_db::input(debug)]
pub struct Resource {
    #[returns(ref)]
    pub content: Result<Arc<[u8]>, String>,
}

/// A file's syntax tree and syntax errors.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parse {
    pub green: GreenNode,
    pub errors: Vec<ParseError>,
}

/// Parses a file. Every edit reruns it, and the queries that read the tree
/// are rerun only when what they take from it changed.
#[crag_db::tracked(returns(ref))]
pub fn parse(db: &dyn crag_db::Db, file: SourceFile) -> Parse {
    let text = file.text(db);
    let (green, errors) = crag_syntax::parse(text, &lex(text));
    Parse { green, errors }
}
