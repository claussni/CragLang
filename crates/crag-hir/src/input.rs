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

use crag_syntax::{GreenNode, ParseError, lex};

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

/// The modules of a program: an application with its dependencies, or a
/// REPL session. Paths are unique; of two modules with one path, the first
/// counts.
#[crag_db::input(debug)]
pub struct Program {
    #[returns(ref)]
    pub modules: Vec<ModuleId>,
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
