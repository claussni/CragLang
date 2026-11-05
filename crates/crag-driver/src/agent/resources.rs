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

//! The resources of the agent server (Implementation Plan §11.12.4):
//! read-only documents at `crag://` URIs. The primer, the principles, the
//! spec sections and the diagnostic entries come from the bundle and the
//! registry; `crag://std/<module>` and the `crag://project/...` resources
//! are rendered from the compiler's own queries, so they follow edits.

use crag_diag::DiagCode;
use crag_hir::{ItemKind, item_tree};
use crag_mcp::{ResourceSpec, TemplateSpec};

use super::AgentServer;
use crate::lsp::analysis::{documentation, signature_text};
use crate::project::std_modules;

const MARKDOWN: &str = "text/markdown";

/// Every resource the server lists. Spec sections are listed by chapter
/// and appendix only, to keep the listing short; `crag://spec/9.3` still
/// reads one section.
pub(super) fn list() -> (Vec<ResourceSpec>, Vec<TemplateSpec>) {
    let fixed = [
        (
            "crag://primer",
            "primer",
            "Crag primer",
            "Where Crag differs from the languages agents are trained on; read it first",
        ),
        (
            "crag://principles",
            "principles",
            "Design principles",
            "The design principles of the language, with their rationale",
        ),
        (
            "crag://project/api",
            "project/api",
            "Project API",
            "The public declarations of the project and its dependencies, with their \
             inferred errors, effects and escaping parameters",
        ),
        (
            "crag://project/manifest",
            "project/manifest",
            "Project manifest",
            "The project's package.crag and sbom.crag",
        ),
    ];
    let mut resources: Vec<ResourceSpec> = fixed
        .into_iter()
        .map(|(uri, name, title, description)| ResourceSpec {
            uri: uri.into(),
            name: name.into(),
            title: title.into(),
            description: description.into(),
            mime_type: MARKDOWN,
        })
        .collect();
    resources.extend(crag_knowledge::chapters().map(|chapter| ResourceSpec {
        uri: format!("crag://spec/{}", chapter.key),
        name: format!("spec/{}", chapter.key),
        title: format!("§{} {}", chapter.key, chapter.title),
        description: format!(
            "The specification's chapter {}, {}",
            chapter.key, chapter.title
        ),
        mime_type: MARKDOWN,
    }));
    resources.extend(std_modules().map(|module| ResourceSpec {
        uri: format!("crag://std/{module}"),
        name: format!("std/{module}"),
        title: module.to_string(),
        description: format!("The public declarations of `{module}` with their documentation"),
        mime_type: MARKDOWN,
    }));
    resources.extend(crag_diag::ENTRIES.iter().map(|e| ResourceSpec {
        uri: format!("crag://diagnostic/{}", e.code),
        name: e.code.to_string(),
        title: format!("{}: {}", e.code, e.title),
        description: format!("The diagnostic {}: {}", e.code, e.title),
        mime_type: MARKDOWN,
    }));
    let templates = vec![
        TemplateSpec {
            uri_template: "crag://spec/{section}",
            name: "spec",
            title: "A specification section",
            description: "One section of the specification by its number, subsections \
                          included, as diagnostics and the primer cite them: crag://spec/9.3, \
                          or an appendix such as crag://spec/D",
            mime_type: MARKDOWN,
        },
        TemplateSpec {
            uri_template: "crag://std/{module}",
            name: "std",
            title: "A module's declarations",
            description: "The public declarations of a std, dependency or project module \
                          with their documentation, by its path: crag://std/std.io",
            mime_type: MARKDOWN,
        },
        TemplateSpec {
            uri_template: "crag://diagnostic/{code}",
            name: "diagnostic",
            title: "A diagnostic code",
            description: "What a diagnostic code means, with a refused program, its fix and \
                          the section of the specification",
            mime_type: MARKDOWN,
        },
    ];
    (resources, templates)
}

/// The resource at `uri`: `Ok(None)` when there is none.
pub(super) fn read(server: &mut AgentServer, uri: &str) -> Result<Option<String>, String> {
    let Some(rest) = uri.strip_prefix("crag://") else {
        return Ok(None);
    };
    match rest {
        "primer" => Ok(Some(crag_knowledge::primer().to_string())),
        "principles" => Ok(Some(crag_knowledge::principles().to_string())),
        "project/api" => api(server).map(Some),
        "project/manifest" => manifest(server).map(Some),
        _ => {
            if let Some(key) = rest.strip_prefix("spec/") {
                return Ok(crag_knowledge::section(key).map(|s| s.text.to_string()));
            }
            if let Some(code) = rest.strip_prefix("diagnostic/") {
                return Ok(DiagCode::parse(code).map(|c| c.entry().markdown()));
            }
            if let Some(module) = rest.strip_prefix("std/") {
                return module_docs(server, module);
            }
            Ok(None)
        }
    }
}

/// `crag://std/<module>`: the module's public declarations, each its
/// signature and the comment above it, as the LSP's hover shows them.
fn module_docs(server: &mut AgentServer, module: &str) -> Result<Option<String>, String> {
    let project = server.context(None)?.repl.project();
    let db = &project.db;
    let Some(file) = project.files.iter().find(|f| f.module.path(db) == module) else {
        return Ok(None);
    };
    let mut out = format!("# {module}\n");
    for item in item_tree(db, file.module)
        .items
        .iter()
        .filter(|i| i.public && *i.id.kind(db) != ItemKind::Slot)
    {
        let Some(signature) = signature_text(db, item.id) else {
            continue;
        };
        out += &format!("\n```crag\n{signature}\n```\n");
        if let Some(doc) = documentation(db, item.id) {
            out += &format!("\n{doc}\n");
        }
    }
    Ok(Some(out))
}

/// `crag://project/api`: the API of the project, computed, and of each
/// dependency, from its generated api.crag (§20.5).
fn api(server: &mut AgentServer) -> Result<String, String> {
    let project = server.context(None)?.repl.project();
    if project.root.is_none() {
        return Err("the server runs with std alone; name or enter a project".into());
    }
    // An app exports nothing; its API is every module's public surface.
    let exports = match project.manifest.as_ref().map(|m| m.exports.clone()) {
        Some(exports) if !exports.is_empty() => exports,
        _ => {
            let db = &project.db;
            project
                .own()
                .iter()
                .map(|f| f.module.path(db).clone())
                .collect()
        }
    };
    let mut out = format!(
        "# Project API\n\n```crag\n{}```\n",
        crate::api::api_of(project, &exports).write()
    );
    let mut seen = Vec::new();
    for file in &project.files {
        let Some(dependency) = &file.dependency else {
            continue;
        };
        if seen.contains(&&dependency.package_dir) {
            continue;
        }
        seen.push(&dependency.package_dir);
        if let Ok(text) = std::fs::read_to_string(dependency.package_dir.join("api.crag")) {
            out += &format!("\n```crag\n{text}```\n");
        }
    }
    Ok(out)
}

/// `crag://project/manifest`: package.crag and sbom.crag as committed.
fn manifest(server: &mut AgentServer) -> Result<String, String> {
    let context = server.context(None)?;
    let Some(root) = &context.root else {
        return Err("the server runs with std alone; name or enter a project".into());
    };
    let manifest = std::fs::read_to_string(root.join("package.crag"))
        .map_err(|e| format!("cannot read package.crag: {e}"))?;
    let mut out = format!("# package.crag\n\n```crag\n{manifest}```\n");
    if let Ok(sbom) = std::fs::read_to_string(root.join("sbom.crag")) {
        out += &format!("\n# sbom.crag\n\n```crag\n{sbom}```\n");
    }
    Ok(out)
}
