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

//! The public API of the project's package (Implementation Plan §11.9.2):
//! every `pub` declaration of the modules it exports, with what the
//! compiler inferred about it, from the same queries the compiler uses.

use crag_hir::{ItemKind, item_tree};
use crag_package::api::{ApiEntry, ApiFile};
use crag_types::{
    EscapeLevel, error_members, function_effects, param_escapes, result_type, signature,
    success_members, value_type,
};

use crate::lsp::analysis::signature_text;
use crate::project::Project;

/// Whether the manifest exports the module: by name, or a directory it
/// lies directly in.
pub fn exported(exports: &[String], module: &str) -> bool {
    exports.iter().any(|e| {
        e == module
            || module
                .strip_prefix(e.as_str())
                .and_then(|rest| rest.strip_prefix('.'))
                .is_some_and(|rest| !rest.contains('.'))
    })
}

pub fn public_api(project: &Project) -> ApiFile {
    let (db, program) = (&project.db, project.program);
    let manifest = project.manifest.clone().unwrap_or_default();
    let mut entries = Vec::new();
    for file in project.own() {
        let module = file.module.path(db);
        if !exported(&manifest.exports, module) {
            continue;
        }
        for item in item_tree(db, file.module).items.iter().filter(|i| i.public) {
            let id = item.id;
            let kind = *id.kind(db);
            if kind == ItemKind::Slot {
                continue;
            }
            let Some(decl) = signature_text(db, id) else {
                continue;
            };
            let mut entry = ApiEntry {
                module: module.clone(),
                decl,
                ..ApiEntry::default()
            };
            match kind {
                ItemKind::Function => {
                    let sig = signature(db, program, id);
                    if let Some(result) = result_type(db, program, id) {
                        if sig.result.is_none() {
                            entry.returns = Some(success_members(db, program, result).display(db));
                        }
                        entry.errors = error_members(db, program, result)
                            .members(db)
                            .into_iter()
                            .map(|m| m.display(db))
                            .collect();
                    }
                    let param_name = |i: usize| {
                        sig.params
                            .get(i)
                            .and_then(|p| p.name)
                            .map_or_else(|| format!("#{i}"), |n| n.text(db).clone())
                    };
                    let effects = function_effects(db, program, id);
                    entry.effects = effects.names().into_iter().map(String::from).collect();
                    entry.effects.extend(
                        effects
                            .called_params()
                            .into_iter()
                            .map(|i| format!("calls {}", param_name(i))),
                    );
                    entry.escaping = param_escapes(db, program, id)
                        .iter()
                        .enumerate()
                        .filter(|(_, l)| **l == EscapeLevel::Escaping)
                        .map(|(i, _)| param_name(i))
                        .collect();
                }
                ItemKind::Value | ItemKind::Embed => {
                    entry.returns = value_type(db, program, id).map(|t| t.display(db));
                }
                _ => {}
            }
            entries.push(entry);
        }
    }
    ApiFile::new(&manifest.package, manifest.version, entries)
}
