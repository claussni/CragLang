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

//! Diagnostics: every error the front end reports, as a message at a range
//! of a module's source, printed with the offending text underlined.

use std::ops::Range;

use crag_db::Db;
use crag_eval::EvalError;
use crag_hir::{
    ImportCycle, LowerError, ModuleId, NameError, Origin, PathError, Previous, Redeclaration,
    check_shadowing, import_graph, lower_body, module_scope, owners, parse,
};
use crag_syntax::SyntaxNode;

use crate::project::Project;

/// An error at a range of a module's source.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub module: ModuleId,
    pub range: Range<u32>,
    pub message: String,
}

/// Every error of the project's modules, the prelude's included, in the
/// order of the modules and then of their positions.
pub fn check(project: &Project) -> Vec<Diagnostic> {
    let (db, program) = (&project.db as &dyn Db, project.program);
    let mut out = Vec::new();
    for file in &project.files {
        let module = file.module;
        let at = |range: Range<u32>, message: String| Diagnostic {
            module,
            range,
            message,
        };
        for error in &parse(db, *module.file(db)).errors {
            out.push(at(error.range.clone(), error.message.clone()));
        }
        for error in &module_scope(db, program, module).errors {
            out.push(at(
                name_error_range(db, module, error),
                name_error(db, error),
            ));
        }
        for redeclaration in check_shadowing(db, program, module) {
            out.push(at(
                redeclaration.range.clone(),
                redeclared(db, redeclaration),
            ));
        }
        for owner in owners(db, module) {
            let lowered = lower_body(db, program, owner);
            for error in &lowered.errors {
                let (range, message) = lower_error(db, error);
                out.push(at(range, message));
            }
        }
        for (owner, error) in crag_types::module_type_errors(db, program, module) {
            let map = &lower_body(db, program, owner).source_map;
            let range = error.site.range(map).unwrap_or(0..0);
            out.push(at(range, error.kind.message(db)));
        }
        // Constants are evaluated at compile time (Specification §18.4),
        // and an evaluation that fails is an error at the value.
        for (item, error) in crag_eval::eval_errors(db, program, module) {
            let EvalError::Trap { kind, stack, .. } = error else {
                continue;
            };
            let name = item.name(db).text(db);
            let mut message = format!(
                "`{name}` cannot be computed at compile time: it {}",
                trap_verb(kind)
            );
            if let Some(inner) = stack.first().filter(|f| *f != name) {
                message += &format!(" in {inner}");
            }
            out.push(at(decl_range(db, module, item_decl(db, item)), message));
        }
    }
    for cycle in &import_graph(db, program).cycles {
        out.push(import_cycle(db, cycle));
    }
    let mut seen = Vec::new();
    out.retain(|d| {
        let new = !seen.contains(d);
        if new {
            seen.push(d.clone());
        }
        new
    });
    let order = |m: ModuleId| project.files.iter().position(|f| f.module == m);
    out.sort_by_key(|d| (order(d.module), d.range.start));
    out
}

/// What a trap in a compile-time evaluation did, after "it".
fn trap_verb(kind: crag_abi::TrapKind) -> String {
    use crag_abi::TrapKind::*;
    match kind {
        OutOfSteps | OutOfMemory => crate::exec::trap_message(kind).to_string(),
        kind => format!("traps with {}", crate::exec::trap_message(kind)),
    }
}

/// The range of a module's declaration by its index.
fn decl_range(db: &dyn Db, module: ModuleId, decl: u32) -> Range<u32> {
    let root = SyntaxNode::new_root(parse(db, *module.file(db)).green.clone());
    root.children()
        .nth(decl as usize)
        .map_or(0..0, |node| node.range())
}

fn name_error_range(db: &dyn Db, module: ModuleId, error: &NameError) -> Range<u32> {
    match error {
        NameError::Path { decl, .. }
        | NameError::ModuleRenamed { decl, .. }
        | NameError::UnknownElement { decl, .. }
        | NameError::PrivateElement { decl, .. } => decl_range(db, module, *decl),
        NameError::ModuleBesideDirectory { .. } => 0..0,
        NameError::Collision { items, .. } => {
            let decl = items.iter().find_map(|(item, origin)| match origin {
                Origin::Imported(decl) => Some(*decl),
                Origin::Declared if *item.module(db) == module => Some(item_decl(db, *item)),
                _ => None,
            });
            decl.map_or(0..0, |d| decl_range(db, module, d))
        }
    }
}

fn item_decl(db: &dyn Db, item: crag_hir::ItemId) -> u32 {
    crag_hir::item_tree(db, *item.module(db))
        .items
        .iter()
        .find(|i| i.id == item)
        .map_or(0, |i| i.decl)
}

fn name_error(db: &dyn Db, error: &NameError) -> String {
    match error {
        NameError::Path {
            error: PathError::Unknown(path),
            ..
        } => format!("no module or directory has the path `{path}`"),
        NameError::Path {
            error: PathError::PastElement(path),
            ..
        } => format!("`{path}` goes on past an element of a module"),
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
            format!(
                "`{}` comes from more than one place: {}",
                name.text(db),
                from.join(", ")
            )
        }
    }
}

fn redeclared(db: &dyn Db, r: &Redeclaration) -> String {
    let first = match &r.previous {
        Previous::Local(_) => "a binding of the same body".to_string(),
        Previous::Item(item) => format!("the declaration in `{}`", item.module(db).path(db)),
    };
    format!(
        "`{}` is declared again, but {first} has the name already; Crag has no shadowing",
        r.name
    )
}

fn lower_error(db: &dyn Db, error: &LowerError) -> (Range<u32>, String) {
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
    }
}

fn import_cycle(db: &dyn Db, cycle: &ImportCycle) -> Diagnostic {
    let (first, decl) = cycle.steps[0];
    let mut names: Vec<String> = cycle
        .steps
        .iter()
        .map(|(m, _)| format!("`{}`", m.path(db)))
        .collect();
    names.push(names[0].clone());
    Diagnostic {
        module: first,
        range: decl.map_or(0..0, |d| decl_range(db, first, d)),
        message: format!("modules import each other: {}", names.join(" imports ")),
    }
}

/// The line and column, from one, of a byte offset, counting characters.
pub fn line_col(source: &str, offset: u32) -> (usize, usize) {
    let offset = (offset as usize).min(source.len());
    let before = &source[..offset];
    let line = before.matches('\n').count() + 1;
    let start = before.rfind('\n').map_or(0, |i| i + 1);
    (line, before[start..].chars().count() + 1)
}

/// A message at a range of a file's source: its location, the first line
/// of the range, and the range's text on it underlined.
pub fn render_at(kind: &str, message: &str, file: &str, source: &str, range: Range<u32>) -> String {
    let start = (range.start as usize).min(source.len());
    let end = (range.end as usize).clamp(start, source.len());
    let (line, col) = line_col(source, start as u32);
    let line_start = source[..start].rfind('\n').map_or(0, |i| i + 1);
    let line_end = source[start..]
        .find('\n')
        .map_or(source.len(), |i| start + i);
    let text = &source[line_start..line_end];
    let width = source[start..end.min(line_end)].chars().count().max(1);
    let number = line.to_string();
    let pad = " ".repeat(number.len());
    let indent: String = source[line_start..start]
        .chars()
        .map(|c| if c == '\t' { '\t' } else { ' ' })
        .collect();
    format!(
        "{kind}: {message}\n{pad}--> {file}:{line}:{col}\n{pad} |\n{number} | {text}\n{pad} | {indent}{}\n",
        "^".repeat(width)
    )
}

/// A diagnostic printed against the source of its module.
pub fn render_diagnostic(d: &Diagnostic, file: &str, source: &str) -> String {
    render_at("error", &d.message, file, source, d.range.clone())
}
