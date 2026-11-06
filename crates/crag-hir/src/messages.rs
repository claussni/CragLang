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

//! The messages of name and lowering errors, as the driver reports them
//! and a receiver of code gives them back (Implementation Plan §11.10.8).

use std::ops::Range;

use crag_db::Db;
use crag_diag::DiagCode;

use crate::{LowerError, NameError, Origin, PathError, Previous, Redeclaration};

/// The message of a name error.
pub fn name_message(db: &dyn Db, error: &NameError) -> String {
    match error {
        NameError::Path {
            error: PathError::Unknown(path),
            ..
        } => format!("no module or directory has the path `{path}`"),
        NameError::Path {
            error: PathError::PastElement(path),
            ..
        } => format!("`{path}` goes on past an element of a module"),
        NameError::Path {
            error: PathError::Hidden { reason, .. },
            ..
        } => reason.clone(),
        NameError::ModuleRenamed { path, .. } => {
            format!("`as` renames elements only, not the module or directory `{path}`")
        }
        NameError::UnknownElement { module, name, .. } => format!(
            "module `{}` has no element `{}`",
            module.path(db),
            name.text(db)
        ),
        NameError::PrivateElement { module, name, .. } => format!(
            "`{}` of module `{}` is not `pub`",
            name.text(db),
            module.path(db)
        ),
        NameError::ModuleBesideDirectory { path } => {
            format!("module `{path}` lies beside a directory of the same name")
        }
        NameError::Collision { name, items } => {
            let from: Vec<String> = items
                .iter()
                .map(|(item, _)| format!("`{}`", item.module(db).path(db)))
                .collect();
            let mut message = format!(
                "`{}` comes from more than one place: {}",
                name.text(db),
                from.join(", ")
            );
            // The prelude's names are reserved, but a file may rename one
            // (Specification §19.3).
            if items.iter().any(|(_, origin)| *origin == Origin::Prelude) {
                message += &format!(
                    "; use another name, or rename the prelude's with \
                     `import std.core.{} as <name>`",
                    name.text(db)
                );
            }
            message
        }
    }
}

/// The message of a declaration that takes a name again.
pub fn redeclared(db: &dyn Db, r: &Redeclaration) -> String {
    let first = match &r.previous {
        Previous::Local(_) => "a binding of the same body".to_string(),
        Previous::Item(item) => format!("the declaration in `{}`", item.module(db).path(db)),
    };
    format!(
        "`{}` is declared again, but {first} has the name already; Crag has no shadowing",
        r.name
    )
}

/// The range and message of a lowering error.
pub fn lower_message(db: &dyn Db, error: &LowerError) -> (Range<u32>, String) {
    match error {
        LowerError::Unresolved { name, range } => {
            (range.clone(), format!("`{name}` is not defined"))
        }
        LowerError::UnknownType { name, range } => {
            (range.clone(), format!("`{name}` is not a type"))
        }
        LowerError::Redeclared(r) => (r.range.clone(), redeclared(db, r)),
        LowerError::NotInEveryAlternative { name, range } => (
            range.clone(),
            format!("`{name}` is not bound by every alternative"),
        ),
        LowerError::UnnamedField { range } => (range.clone(), "a record field needs a name".into()),
        LowerError::Literal { message, range } => (range.clone(), message.clone()),
        LowerError::Embed { message, range } => (range.clone(), message.clone()),
        LowerError::UnknownPrefix { text, range } => (
            range.clone(),
            format!("no declared prefixes make up `{text}`"),
        ),
        LowerError::NoOperator { function, range } => (
            range.clone(),
            format!("no `{function}` is in scope for this operator"),
        ),
        LowerError::NotAVar { name, range } => (
            range.clone(),
            format!("`{name}` is not a `var`, so it cannot be assigned"),
        ),
        LowerError::VarWrittenInClosure { name, range } => (
            range.clone(),
            format!("the `var` `{name}` cannot be assigned inside a closure that captures it"),
        ),
        LowerError::MisplacedSpread { range } => (
            range.clone(),
            "a spread must be the first entry of a field list, and the only one".into(),
        ),
        LowerError::ExpectedType { range } => (range.clone(), "a type is expected here".into()),
        LowerError::ExpectedValue { range } => {
            (range.clone(), "a value is expected here, not a type".into())
        }
        LowerError::Marker { range } => (
            range.clone(),
            "only `Pure` marks a function or a function type".into(),
        ),
        LowerError::BindElse { ext, range } => (
            range.clone(),
            match ext {
                true => "the `else` part of an `ext` binding is not supported yet".into(),
                false => "only a `dur` binding takes an `else` part here".into(),
            },
        ),
    }
}

/// The code of a name error.
pub fn name_code(error: &NameError) -> DiagCode {
    match error {
        NameError::Path {
            error: PathError::Unknown(_),
            ..
        } => crag_diag::UNKNOWN_PATH,
        NameError::Path {
            error: PathError::PastElement(_),
            ..
        } => crag_diag::PATH_PAST_ELEMENT,
        NameError::Path {
            error: PathError::Hidden { .. },
            ..
        } => crag_diag::HIDDEN_PATH,
        NameError::ModuleRenamed { .. } => crag_diag::MODULE_RENAMED,
        NameError::UnknownElement { .. } => crag_diag::UNKNOWN_ELEMENT,
        NameError::PrivateElement { .. } => crag_diag::PRIVATE_ELEMENT,
        NameError::ModuleBesideDirectory { .. } => crag_diag::MODULE_BESIDE_DIRECTORY,
        NameError::Collision { .. } => crag_diag::NAME_COLLISION,
    }
}

/// The code of a lowering error.
pub fn lower_code(error: &LowerError) -> DiagCode {
    match error {
        LowerError::Unresolved { .. } => crag_diag::UNDEFINED,
        LowerError::UnknownType { .. } => crag_diag::NOT_A_TYPE,
        LowerError::Redeclared(_) => crag_diag::REDECLARED,
        LowerError::NotInEveryAlternative { .. } => crag_diag::NOT_IN_EVERY_ALTERNATIVE,
        LowerError::UnnamedField { .. } => crag_diag::UNNAMED_FIELD,
        LowerError::Literal { .. } => crag_diag::BAD_LITERAL,
        LowerError::Embed { .. } => crag_diag::EMBED_UNREADABLE,
        LowerError::UnknownPrefix { .. } => crag_diag::UNKNOWN_PREFIX,
        LowerError::NoOperator { .. } => crag_diag::NO_OPERATOR,
        LowerError::NotAVar { .. } => crag_diag::NOT_A_VAR,
        LowerError::VarWrittenInClosure { .. } => crag_diag::VAR_WRITTEN_IN_CLOSURE,
        LowerError::MisplacedSpread { .. } => crag_diag::MISPLACED_SPREAD,
        LowerError::ExpectedType { .. } => crag_diag::EXPECTED_TYPE,
        LowerError::ExpectedValue { .. } => crag_diag::EXPECTED_VALUE,
        LowerError::Marker { .. } => crag_diag::MISPLACED_MARKER,
        LowerError::BindElse { .. } => crag_diag::BIND_ELSE,
    }
}
