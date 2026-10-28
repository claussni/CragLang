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

//! The commands that manage a project's packages (Specification §20.6),
//! `crag package new`, `add`, `remove`, `upgrade`, `outdated`, `deps`,
//! `sbom`, `pack` and `publish`, and `crag registry`, which edits the
//! user's list of registries. Each
//! returns its exit status, 0 for success, 1 for a failure and 2 for a
//! usage error, and a command that would change something prints its
//! usage when run bare. Those that edit the manifest change only the
//! lines they touch, then resolve again and write the SBOM, which they
//! show the change of; when the new manifest does not resolve, nothing is
//! written.

use std::fs;
use std::io::Write;
use std::path::Path;

use crag_hir::imports;
use crag_package::manifest::{add_import, remove_import, reserved, set_version, valid_name};
use crag_package::{Manifest, Registry, Resolution, Sbom, Version};

pub use crate::commands::{Args, Spec};
use crate::project::{Check, Project, read_manifest, resolve};

/// A command of this module: the project's directory, or for `new` the
/// directory to create it in, and the arguments; the exit status.
pub type PackageCommand = fn(&Path, &Args, &mut dyn Write) -> u8;

pub const NEW: Spec = Spec {
    switches: &["lib"],
    values: &[],
};
pub const ADD: Spec = Spec::NONE;
pub const REMOVE: Spec = Spec::NONE;
pub const UPGRADE: Spec = Spec {
    switches: &[],
    values: &["version"],
};
pub const LIST: Spec = Spec {
    switches: &["json"],
    values: &[],
};

impl Spec {
    pub const NONE: Spec = Spec {
        switches: &[],
        values: &[],
    };
}

/// Prints a usage line and gives the usage error's status.
fn usage(out: &mut dyn Write, text: &str) -> u8 {
    let _ = writeln!(out, "usage: {text}");
    2
}

fn fail(out: &mut dyn Write, message: impl std::fmt::Display) -> u8 {
    let _ = writeln!(out, "error: {message}");
    1
}

/// The registries of the user's settings.
fn registries() -> Result<Vec<Registry>, String> {
    match crag_package::home::crag_home() {
        Some(home) => crag_package::home::registries(&home),
        None => Ok(Vec::new()),
    }
}

/// The one registry that has a package.
fn registry_of<'a>(name: &str, registries: &'a [Registry]) -> Result<&'a Registry, String> {
    let having: Vec<&Registry> = registries.iter().filter(|r| r.has(name)).collect();
    match having[..] {
        [one] => Ok(one),
        [] if registries.is_empty() => Err(format!(
            "no registry is set up; `crag registry new` makes one, `crag registry add` names one \
             that exists, in registries.crag in the settings directory ({})",
            crag_package::home::crag_home()
                .map(|h| h.display().to_string())
                .unwrap_or_else(|| "CRAG_HOME".into())
        )),
        [] => Err(format!("package {name} is in no registry")),
        _ => Err(format!(
            "package {name} is in several registries; name the source with `from` in the manifest"
        )),
    }
}

/// The newest version that is not yanked, among those `keep` accepts.
fn newest(registry: &Registry, name: &str, keep: impl Fn(&Version) -> bool) -> Option<Version> {
    registry
        .versions(name)
        .into_iter()
        .rev()
        .map(|(v, _)| v)
        .find(|v| keep(v) && registry.yanked(name, v).is_none())
}

/// `new <name> [--lib]`: a project in a new directory `name` below `dir`.
pub fn crag_new(dir: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let [name] = &args.positional[..] else {
        return usage(out, "crag package new <name> [--lib]");
    };
    if !valid_name(name) || name.contains('.') || reserved(name) {
        return fail(out, format!("`{name}` is not a name for a new package"));
    }
    let root = dir.join(name);
    if root.exists() {
        return fail(out, format!("{} exists already", root.display()));
    }
    let lib = args.switch("lib");
    let (manifest, files) = if lib {
        (
            format!(
                "package {name} 0.1\nruntime {}\n\nexport {name}.greeting\n",
                crag_package::RUNTIME
            ),
            vec![
                (
                    "greeting.crag",
                    "// What the package offers.\npub fn greeting() -> Str { \"Hello\" }\n"
                        .to_string(),
                ),
                (
                    "test/greeting_test.crag",
                    format!("import {name}.greeting\n\ntest \"greets\" {{\n  greeting()\n}}\n"),
                ),
            ],
        )
    } else {
        (
            format!(
                "package {name} 0.1\nruntime {}\n\nmain {name}.main\n",
                crag_package::RUNTIME
            ),
            vec![
                (
                    "main.crag",
                    "// The application's entry point.\nfn main() {\n}\n".to_string(),
                ),
                (
                    "test/main_test.crag",
                    "test \"the project builds\" {\n}\n".to_string(),
                ),
            ],
        )
    };
    let written = (|| -> std::io::Result<()> {
        fs::create_dir_all(root.join("test"))?;
        fs::write(root.join("package.crag"), manifest)?;
        for (file, text) in files {
            fs::write(root.join(file), text)?;
        }
        Ok(())
    })();
    match written {
        Ok(()) => {
            let what = if lib { "library" } else { "application" };
            let _ = writeln!(out, "created the {what} {name} in {}", root.display());
            0
        }
        Err(e) => fail(out, format!("cannot create {}: {e}", root.display())),
    }
}

/// Writes a changed manifest and the SBOM it resolves to, or nothing when
/// it does not resolve or would bring in a yanked version anew.
fn change_manifest(root: &Path, text: &str, out: &mut dyn Write) -> u8 {
    let manifest = match Manifest::parse(text) {
        Ok(m) => m,
        Err(errors) => {
            for e in errors {
                let _ = writeln!(out, "error: package.crag:{}: {}", e.line, e.message);
            }
            return 1;
        }
    };
    let resolution = match resolve(root, &manifest) {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    let old = read_sbom(root).unwrap_or_default();
    for p in &resolution.packages {
        if let Some(reason) = &p.yanked {
            let kept = old
                .entries
                .iter()
                .any(|e| e.name == p.name && e.version == p.version);
            if !kept {
                return fail(
                    out,
                    format!(
                        "{} {} was yanked ({reason}); choose another version",
                        p.name, p.version
                    ),
                );
            }
        }
    }
    if let Err(e) = fs::write(root.join("package.crag"), text) {
        return fail(out, format!("cannot write package.crag: {e}"));
    }
    write_sbom(root, &old, &resolution, out)
}

fn read_sbom(root: &Path) -> Option<Sbom> {
    Sbom::parse(&fs::read_to_string(root.join("sbom.crag")).ok()?).ok()
}

/// Writes the SBOM of a resolution and prints how it changed.
fn write_sbom(root: &Path, old: &Sbom, resolution: &Resolution, out: &mut dyn Write) -> u8 {
    let new = Sbom::of(resolution);
    let file = root.join("sbom.crag");
    let result = if new.entries.is_empty() && !file.exists() {
        Ok(())
    } else {
        fs::write(&file, new.write())
    };
    if let Err(e) = result {
        return fail(out, format!("cannot write sbom.crag: {e}"));
    }
    for line in old.diff(&new) {
        let _ = writeln!(out, "sbom.crag: {line}");
    }
    0
}

/// The manifest's text and contents, or the status of the failure.
fn manifest(root: &Path, out: &mut dyn Write) -> Result<(String, Manifest), u8> {
    let text = fs::read_to_string(root.join("package.crag"))
        .map_err(|e| fail(out, format!("cannot read package.crag: {e}")))?;
    let manifest = read_manifest(root).map_err(|e| fail(out, e))?;
    Ok((text, manifest))
}

/// `add <package> [version]`.
pub fn crag_add(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let (name, version) = match &args.positional[..] {
        [name] => (name, None),
        [name, version] => (name, Some(version)),
        _ => return usage(out, "crag package add <package> [version]"),
    };
    let (text, manifest) = match manifest(root, out) {
        Ok(m) => m,
        Err(status) => return status,
    };
    if manifest.import(name).is_some() {
        return fail(
            out,
            format!("the manifest imports {name} already; `upgrade` changes its version"),
        );
    }
    let version = match version {
        Some(v) => match Version::parse(v) {
            Ok(v) => v,
            Err(e) => return fail(out, e),
        },
        None => {
            let registries = match registries() {
                Ok(r) => r,
                Err(e) => return fail(out, e),
            };
            let registry = match registry_of(name, &registries) {
                Ok(r) => r,
                Err(e) => return fail(out, e),
            };
            match newest(registry, name, |_| true) {
                Some(v) => v,
                None => return fail(out, format!("every version of {name} was yanked")),
            }
        }
    };
    let status = change_manifest(root, &add_import(&text, &manifest, name, &version), out);
    if status == 0 {
        let _ = writeln!(out, "added {name} {version}");
    }
    status
}

/// `remove <package>`: refused while code still imports from it.
pub fn crag_remove(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let [name] = &args.positional[..] else {
        return usage(out, "crag package remove <package>");
    };
    let (text, manifest) = match manifest(root, out) {
        Ok(m) => m,
        Err(status) => return status,
    };
    let Some(dep) = manifest.import(name) else {
        return fail(out, format!("the manifest does not import {name}"));
    };
    let project = match Project::load_with(root, Check::Resolve) {
        Ok(p) => p,
        Err(e) => return fail(out, e),
    };
    let users = users_of(&project, name);
    if !users.is_empty() {
        return fail(
            out,
            format!("{name} is still imported by {}", users.join(", ")),
        );
    }
    let status = change_manifest(root, &remove_import(&text, dep), out);
    if status == 0 {
        let _ = writeln!(out, "removed {name}");
    }
    status
}

/// The project's files that import modules of the package `name`.
fn users_of(project: &Project, name: &str) -> Vec<String> {
    let db = &project.db;
    let prefix = format!("{name}.");
    project
        .own()
        .iter()
        .filter(|f| {
            imports(db, project.program, f.module)
                .targets
                .iter()
                .any(|t| t.module.path(db).starts_with(&prefix))
        })
        .map(|f| f.shown.clone())
        .collect()
}

/// `upgrade <package> [--version=V]` or `upgrade all`: to the newest
/// version of the same major, or to the version given.
pub fn crag_upgrade(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let [target] = &args.positional[..] else {
        return usage(
            out,
            "crag package upgrade <package> [--version=V] | crag package upgrade all",
        );
    };
    let (mut text, manifest) = match manifest(root, out) {
        Ok(m) => m,
        Err(status) => return status,
    };
    let registries = match registries() {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    let names: Vec<String> = if target == "all" {
        if args.value("version").is_some() {
            return fail(out, "`upgrade all` takes no version");
        }
        manifest
            .imports
            .iter()
            .filter(|d| d.source.is_none())
            .map(|d| d.name.clone())
            .collect()
    } else {
        vec![target.clone()]
    };
    let mut changes = Vec::new();
    // From the last import up, so earlier spans stay where they are.
    let mut deps = Vec::new();
    for name in &names {
        match manifest.import(name) {
            Some(dep) => deps.push(dep),
            None => return fail(out, format!("the manifest does not import {name}")),
        }
    }
    deps.sort_by_key(|d| std::cmp::Reverse(d.span.start));
    for dep in deps {
        let to = match args.value("version") {
            Some(v) => match Version::parse(v) {
                Ok(v) => v,
                Err(e) => return fail(out, e),
            },
            None => {
                let registry = match registry_of(&dep.name, &registries) {
                    Ok(r) => r,
                    Err(e) => return fail(out, e),
                };
                match newest(registry, &dep.name, |v| v.major == dep.version.major) {
                    Some(v) => v,
                    None => continue,
                }
            }
        };
        if to.to_string() != dep.version.to_string() {
            text = set_version(&text, dep, &to);
            changes.push(format!("{} {} -> {to}", dep.name, dep.version));
        }
    }
    if changes.is_empty() {
        let _ = writeln!(out, "nothing to upgrade");
        return 0;
    }
    let status = change_manifest(root, &text, out);
    if status == 0 {
        changes.reverse();
        for c in changes {
            let _ = writeln!(out, "upgraded {c}");
        }
    }
    status
}

/// `outdated`: newer versions of what the manifest imports, those of a
/// newer major apart.
pub fn crag_outdated(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let (_, manifest) = match manifest(root, out) {
        Ok(m) => m,
        Err(status) => return status,
    };
    let registries = match registries() {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    let mut rows = Vec::new();
    for dep in manifest.imports.iter().filter(|d| d.source.is_none()) {
        let Ok(registry) = registry_of(&dep.name, &registries) else {
            continue;
        };
        let same = newest(registry, &dep.name, |v| {
            v.major == dep.version.major && *v > dep.version
        });
        let major = newest(registry, &dep.name, |v| v.major > dep.version.major);
        if same.is_some() || major.is_some() {
            rows.push((dep.name.clone(), dep.version, same, major));
        }
    }
    let show = |v: &Option<Version>| v.map(|v| v.to_string());
    if args.switch("json") {
        let rows: Vec<serde_json::Value> = rows
            .iter()
            .map(|(name, v, same, major)| {
                serde_json::json!({"package": name, "version": v.to_string(), "newer": show(same), "newerMajor": show(major)})
            })
            .collect();
        let _ = writeln!(out, "{}", serde_json::Value::Array(rows));
        return 0;
    }
    if rows.is_empty() {
        let _ = writeln!(out, "everything is up to date");
    }
    for (name, v, same, major) in rows {
        let mut news = Vec::new();
        if let Some(same) = same {
            news.push(format!("{same} available"));
        }
        if let Some(major) = major {
            news.push(format!("new major {major}"));
        }
        let _ = writeln!(out, "{name} {v}: {}", news.join(", "));
    }
    0
}

/// `deps`: the resolved packages as a tree from the project's imports.
pub fn crag_deps(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let (_, manifest) = match manifest(root, out) {
        Ok(m) => m,
        Err(status) => return status,
    };
    let resolution = match resolve(root, &manifest) {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    if args.switch("json") {
        let packages: Vec<serde_json::Value> = resolution
            .packages
            .iter()
            .map(|p| {
                let imports: Vec<&str> = p.manifest.imports.iter().filter(|d| !d.dev).map(|d| d.name.as_str()).collect();
                serde_json::json!({"package": p.name, "version": p.version.to_string(), "imports": imports})
            })
            .collect();
        let imports: Vec<&str> = manifest.imports.iter().map(|d| d.name.as_str()).collect();
        let _ = writeln!(
            out,
            "{}",
            serde_json::json!({"package": manifest.package, "imports": imports, "packages": packages})
        );
        return 0;
    }
    let _ = writeln!(out, "{}", manifest.package);
    let mut path = Vec::new();
    for dep in &manifest.imports {
        tree(
            &resolution,
            &dep.name,
            dep.dev,
            &dep.version,
            1,
            &mut path,
            out,
        );
    }
    0
}

fn tree(
    resolution: &Resolution,
    name: &str,
    dev: bool,
    asked: &Version,
    depth: usize,
    path: &mut Vec<String>,
    out: &mut dyn Write,
) {
    let indent = "  ".repeat(depth);
    let Some(p) = resolution.get(name) else {
        return;
    };
    let mut line = format!("{indent}{name} {}", p.version);
    if p.version.to_string() != asked.to_string() {
        line.push_str(&format!(" (asks for {asked})"));
    }
    if dev {
        line.push_str(" (dev)");
    }
    if path.iter().any(|n| n == name) {
        let _ = writeln!(out, "{line} …");
        return;
    }
    let _ = writeln!(out, "{line}");
    path.push(name.to_string());
    for dep in p.manifest.imports.iter().filter(|d| !d.dev) {
        tree(
            resolution,
            &dep.name,
            false,
            &dep.version,
            depth + 1,
            path,
            out,
        );
    }
    path.pop();
}

/// `sbom diff` and `sbom regenerate`.
pub fn crag_sbom(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let regenerate = match &args.positional[..] {
        [w] if w == "diff" => false,
        [w] if w == "regenerate" => true,
        _ => return usage(out, "crag package sbom diff | crag package sbom regenerate"),
    };
    let (_, manifest) = match manifest(root, out) {
        Ok(m) => m,
        Err(status) => return status,
    };
    let resolution = match resolve(root, &manifest) {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    let old = read_sbom(root).unwrap_or_default();
    if regenerate {
        return write_sbom(root, &old, &resolution, out);
    }
    let diff = old.diff(&Sbom::of(&resolution));
    if args.switch("json") {
        let _ = writeln!(out, "{}", serde_json::json!(diff));
    } else if diff.is_empty() {
        let _ = writeln!(out, "sbom.crag is up to date");
    }
    for line in diff.iter().filter(|_| !args.switch("json")) {
        let _ = writeln!(out, "{line}");
    }
    0
}

pub const PUBLISH: Spec = Spec::NONE;

/// Whether `crag package <name>` is a command: one of [`command`] but
/// `registry`, which is an area of its own.
pub fn is_package_command(name: &str) -> bool {
    name != "registry" && command(name).is_some()
}

/// The commands of this module by name, with what they accept, for both
/// surfaces; `package new` is the shell's alone, since it makes another
/// project.
pub fn command(name: &str) -> Option<(Spec, PackageCommand)> {
    Some(match name {
        "new" => (NEW, crag_new),
        "add" => (ADD, crag_add),
        "remove" => (REMOVE, crag_remove),
        "upgrade" => (UPGRADE, crag_upgrade),
        "outdated" => (LIST, crag_outdated),
        "deps" => (LIST, crag_deps),
        "sbom" => (LIST, crag_sbom),
        "publish" => (PUBLISH, crag_publish),
        "pack" => (PUBLISH, crag_pack),
        "registry" => (REGISTRY, crag_registry),
        _ => return None,
    })
}

pub const REGISTRY: Spec = Spec::NONE;

/// `registry new <name> <folder>` makes a new, empty registry and adds it
/// to the settings; `registry add <name> <folder>` adds one that exists,
/// as a team shares it; `registry list` lists them and `registry remove
/// <name>` takes one out of the settings, leaving its folder. A relative
/// folder is relative to `dir`, the current directory.
pub fn crag_registry(dir: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    const USAGE: &str = "crag registry new <name> <folder> | crag registry add <name> <folder> \
                         | crag registry list | crag registry remove <name>";
    let Some(home) = crag_package::home::crag_home() else {
        return fail(out, "there is no settings directory; set CRAG_HOME");
    };
    let words: Vec<&str> = args.positional.iter().map(String::as_str).collect();
    match words[..] {
        ["list"] => {
            let entries = match crag_package::home::registry_entries(&home) {
                Ok(e) => e,
                Err(e) => return fail(out, e),
            };
            if entries.is_empty() {
                let _ = writeln!(out, "no registries; `crag registry new` makes one");
            }
            for e in entries {
                let state = match Registry::open(&e.name, &e.dir) {
                    Ok(_) => String::new(),
                    Err(problem) => format!("  ({problem})"),
                };
                let _ = writeln!(out, "{} {}{state}", e.name, e.dir.display());
            }
            0
        }
        ["remove", name] => match crag_package::home::remove_registry(&home, name) {
            Ok(true) => {
                let _ = writeln!(out, "removed registry {name} from the settings");
                0
            }
            Ok(false) => fail(out, format!("the settings name no registry `{name}`")),
            Err(e) => fail(out, e),
        },
        [verb @ ("new" | "add"), name, folder] => {
            if !valid_name(name) || name.contains('.') {
                return fail(out, format!("`{name}` is not a name for a registry"));
            }
            match crag_package::home::registry_entries(&home) {
                Ok(entries) if entries.iter().any(|e| e.name == name) => {
                    return fail(
                        out,
                        format!("the settings name a registry `{name}` already"),
                    );
                }
                Ok(_) => {}
                Err(e) => return fail(out, e),
            }
            let folder = dir.join(folder);
            if verb == "new" {
                let empty = fs::read_dir(&folder).map_or(true, |mut d| d.next().is_none());
                if folder.exists() && !(folder.is_dir() && empty) {
                    return fail(out, format!("{} exists and is not empty", folder.display()));
                }
                if let Err(e) = Registry::create(name, &folder) {
                    return fail(out, format!("cannot create {}: {e}", folder.display()));
                }
            }
            let folder = match folder.canonicalize() {
                Ok(f) => f,
                Err(e) => return fail(out, format!("{}: {e}", folder.display())),
            };
            if let Err(e) = Registry::open(name, &folder) {
                return fail(out, e);
            }
            if let Err(e) = crag_package::home::add_registry(&home, name, &folder) {
                return fail(out, e);
            }
            let made = if verb == "new" { "made" } else { "added" };
            let _ = writeln!(out, "{made} registry {name} at {}", folder.display());
            0
        }
        _ => usage(out, USAGE),
    }
}

/// Whether a command that succeeded changed the project's packages.
pub fn changes_packages(name: &str, args: &Args) -> bool {
    matches!(name, "add" | "remove" | "upgrade")
        || (name == "sbom" && args.positional.first().is_some_and(|w| w == "regenerate"))
}

/// `publish <registry>`: runs the publishing checks (§20.5), builds the
/// package folder and places it into the registry.
pub fn crag_publish(root: &Path, args: &Args, out: &mut dyn Write) -> u8 {
    let [name] = &args.positional[..] else {
        return usage(out, "crag package publish <registry>");
    };
    let registries = match registries() {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    let Some(registry) = registries.iter().find(|r| &r.name == name) else {
        let names: Vec<&str> = registries.iter().map(|r| r.name.as_str()).collect();
        return fail(
            out,
            format!(
                "no registry is named `{name}`; the settings name {}",
                match names.is_empty() {
                    true => "none".to_string(),
                    false => names.join(", "),
                }
            ),
        );
    };
    let (dir, manifest) = match prepare(root, Some(registry), out) {
        Ok(prepared) => prepared,
        Err(status) => return status,
    };
    let version = manifest.version.expect("checked");
    let result = registry.publish(&manifest.package, &version, &dir);
    let _ = fs::remove_dir_all(&dir);
    match result {
        Ok(_) => {
            let _ = writeln!(
                out,
                "published {} {version} to {}",
                manifest.package, registry.name
            );
            0
        }
        Err(e) => fail(out, e),
    }
}

/// `package pack` for a library: the folder `publish` would place, in
/// `target/package/`, after every publishing check; compared with the
/// default registry's previous version when there is one.
pub fn crag_pack(root: &Path, _args: &Args, out: &mut dyn Write) -> u8 {
    let registries = match registries() {
        Ok(r) => r,
        Err(e) => return fail(out, e),
    };
    match prepare(root, registries.first(), out) {
        Ok((dir, manifest)) => {
            let _ = writeln!(
                out,
                "packaged {} {} in {}",
                manifest.package,
                manifest.version.expect("checked"),
                dir.display()
            );
            0
        }
        Err(status) => status,
    }
}

/// Checks the project for publishing and builds its package folder: the
/// folder and the manifest, or the status of the failure, whose reasons
/// were printed.
fn prepare(
    root: &Path,
    registry: Option<&Registry>,
    out: &mut dyn Write,
) -> Result<(std::path::PathBuf, Manifest), u8> {
    let (text, manifest) = manifest(root, out)?;
    let mut problems = Vec::new();
    if manifest.runtime.is_none() {
        problems.push("the manifest states no `runtime` version".to_string());
    }
    if manifest.main.is_some() {
        problems.push("an application is not published; a library has no `main`".to_string());
    }
    let Some(version) = manifest.version else {
        return Err(fail(out, "the manifest states no version"));
    };
    if !problems.is_empty() {
        for p in problems {
            let _ = writeln!(out, "error: {p}");
        }
        return Err(1);
    }
    // Every import resolves and the code compiles.
    let Some(project) = crate::checked(root, out) else {
        return Err(1);
    };
    let db = &project.db;
    let shipped: Vec<_> = project
        .own()
        .iter()
        .filter(|f| !crag_package::content::is_dev_module(&manifest.package, f.module.path(db)))
        .collect();
    let mut problems = Vec::new();
    // No type holes (§6.11).
    for f in &shipped {
        let source = project.source(f.module);
        for token in crag_syntax::lex(source)
            .iter()
            .filter(|t| t.kind == crag_syntax::TokenKind::Hole)
        {
            let (line, _) = crate::diagnostics::line_col(source, token.start);
            problems.push(format!(
                "{}:{line}: a type hole `???` is not published",
                f.shown
            ));
        }
    }
    // Exports name the package's own modules, none of them a test's or a
    // tool's, so no development import reaches the public API.
    for export in &manifest.exports {
        let owned: Vec<_> = shipped
            .iter()
            .filter(|f| crate::api::exported(std::slice::from_ref(export), f.module.path(db)))
            .collect();
        if owned.is_empty() {
            problems.push(format!(
                "`export {export}` names no module of the package outside test and tools"
            ));
        }
    }
    if !problems.is_empty() {
        for p in problems {
            let _ = writeln!(out, "error: {p}");
        }
        return Err(1);
    }
    // Every test passes.
    let report = crate::crag_test(root, None, out);
    if !report.success() {
        return Err(fail(out, "the tests do not pass, so nothing is published"));
    }
    let api = crate::api::public_api(&project);
    if let Some(registry) = registry {
        if registry.version_dir(&manifest.package, &version).is_some() {
            return Err(fail(
                out,
                format!(
                    "{} {version} is already in registry `{}`",
                    manifest.package, registry.name
                ),
            ));
        }
        // The previous version of the same major line, if any.
        let previous = registry
            .versions(&manifest.package)
            .into_iter()
            .rfind(|(v, _)| v.major == version.major && *v < version);
        if let Some((previous, dir)) = previous {
            let old = fs::read_to_string(dir.join("api.crag"))
                .map_err(|e| e.to_string())
                .and_then(|t| crag_package::api::ApiFile::parse(&t));
            let old = match old {
                Ok(old) => old,
                Err(e) => {
                    return Err(fail(
                        out,
                        format!("cannot read the api.crag of {previous}: {e}"),
                    ));
                }
            };
            let changes = crag_package::api::diff_api(&old, &api);
            let bump = crag_package::api::required_bump(&changes);
            if !crag_package::api::allows(&previous, &version, bump) {
                let step = match bump {
                    crag_package::api::Bump::Major => "a new major version",
                    crag_package::api::Bump::Minor => "at least a new minor version",
                    crag_package::api::Bump::Patch => "a newer version",
                };
                let _ = writeln!(
                    out,
                    "error: from {previous}, the API changed so that it needs {step}:"
                );
                for c in changes {
                    let _ = writeln!(out, "  {c}");
                }
                return Err(1);
            }
        }
    }
    // The contents are built twice and must come out the same.
    let base = root.join("target").join("package");
    let dir = base.join(format!("{}-{version}", manifest.package));
    let again = base.join(format!("{}-{version}.check", manifest.package));
    let built = build_folder(&project, &shipped, &text, &api, &dir)
        .and_then(|()| build_folder(&project, &shipped, &text, &api, &again));
    if let Err(e) = built {
        return Err(fail(out, format!("cannot build the package folder: {e}")));
    }
    let same = crag_package::content::content_hash(&dir).ok()
        == crag_package::content::content_hash(&again).ok();
    let _ = fs::remove_dir_all(&again);
    if !same {
        return Err(fail(
            out,
            "the package contents are not reproducible from the sources",
        ));
    }
    Ok((dir, manifest))
}

/// Writes the package folder of §20.4: the manifest, the shipped modules in
/// `src/`, their `embed` sources in `res/`, `api.crag` and `sbom.crag`.
fn build_folder(
    project: &Project,
    shipped: &[&crate::project::ModuleFile],
    manifest: &str,
    api: &crag_package::api::ApiFile,
    dir: &Path,
) -> Result<(), String> {
    let root = project.root.clone().unwrap_or_default();
    let _ = fs::remove_dir_all(dir);
    let io = |e: std::io::Error| e.to_string();
    fs::create_dir_all(dir.join("src")).map_err(io)?;
    fs::write(dir.join("package.crag"), manifest).map_err(io)?;
    fs::write(dir.join("api.crag"), api.write()).map_err(io)?;
    if let Ok(sbom) = fs::read_to_string(root.join("sbom.crag")) {
        fs::write(dir.join("sbom.crag"), sbom).map_err(io)?;
    }
    let db = &project.db;
    for f in shipped {
        let target = dir.join("src").join(&f.shown);
        fs::create_dir_all(target.parent().expect("a file has a parent")).map_err(io)?;
        fs::write(&target, project.source(f.module)).map_err(io)?;
        for source in crag_hir::embed_sources(db, f.module) {
            let path = crate::project::resource_path(&f.dir, &source)?;
            let target = dir.join("res").join(&path);
            fs::create_dir_all(target.parent().expect("a file has a parent")).map_err(io)?;
            fs::copy(root.join(&path), &target).map_err(io)?;
        }
    }
    Ok(())
}
