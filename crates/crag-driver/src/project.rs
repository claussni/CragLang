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

//! A project on disk: its manifest, its module files and the packages it
//! depends on.
//!
//! Every `.crag` file below the root other than the manifest and the
//! generated `sbom.crag` and `api.crag` is a module, named by the package
//! and its path: `geo/shape.crag` in package `demo` is `demo.geo.shape`.
//! The manifest's imports are resolved against the registries of the
//! user's settings (Specification §14.5.1), checked against the committed
//! SBOM, and the modules of every resolved package join the program, which
//! then knows the packages' boundaries (§14.5).
//!
//! The resources the modules' `embed` declarations name are files of the
//! package too, resolved against the module's file (Specification
//! §18.4.1). The project reads them when it is loaded and again on
//! `read_resources`, and gives the database what it read; a resource that
//! did not change keeps its input, so nothing that reads it is redone.

use std::fs;
use std::path::{Component, Path, PathBuf};
use std::sync::Arc;

use crag_db::{RootDatabase, Setter};
use crag_hir::{
    ModuleId, PRELUDE, PackageScope, Packages, Program, Resource, SourceFile, embed_sources,
};
use crag_package::content::{Layout, is_dev_module, module_files, module_path};
use crag_package::{Manifest, Resolution, Sbom};

/// The modules of `std` bundled with the tool, the prelude first
/// (Specification §19.4).
const STD: &[(&str, &str)] = &[
    (PRELUDE, include_str!("../../../std/core.crag")),
    ("std.time", include_str!("../../../std/time.crag")),
    ("std.task", include_str!("../../../std/task.crag")),
    ("std.stream", include_str!("../../../std/stream.crag")),
    ("std.io", include_str!("../../../std/io.crag")),
];

/// A module's file, where diagnostics name it.
#[derive(Clone, Debug)]
pub struct ModuleFile {
    pub module: ModuleId,
    /// The path shown to the user, relative to the project's root, or the
    /// prelude's module path.
    pub shown: String,
    /// The directory of the file, relative to its package's root, against
    /// which its `embed` sources resolve.
    pub dir: PathBuf,
    /// For a module of a dependency, where it is.
    pub dependency: Option<DependencyFile>,
}

/// Where a dependency's module is: its package's folder and layout, and
/// its file, which is not to be edited.
#[derive(Clone, Debug)]
pub struct DependencyFile {
    pub package_dir: PathBuf,
    pub layout: Layout,
    pub file: PathBuf,
}

/// The project's modules in a database.
pub struct Project {
    pub db: RootDatabase,
    pub program: Program,
    pub package: String,
    /// The entry module the manifest names.
    pub main: Option<String>,
    /// The modules of `std`, the prelude first, then the project's modules
    /// by path.
    pub files: Vec<ModuleFile>,
    /// The project's root; none outside a project, where `embed` sources
    /// resolve against the working directory.
    pub root: Option<PathBuf>,
    /// The manifest; none outside a project.
    pub manifest: Option<Manifest>,
    /// The packages the project uses, as resolved.
    pub resolution: Resolution,
    /// What loading found worth saying that does not stop it, such as a
    /// yanked version in use.
    pub warnings: Vec<String>,
    /// How many of `files` after `std` are the dependencies' modules.
    dependencies: usize,
}

/// How a project's dependencies are checked when it is loaded.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Check {
    /// Against the committed `sbom.crag`, refusing on a mismatch.
    Sbom,
    /// Not against the SBOM: for the commands that write it.
    Resolve,
}

impl Project {
    /// Reads the project at `root`, with its dependencies checked against
    /// the SBOM.
    pub fn load(root: &Path) -> Result<Project, String> {
        Project::load_with(root, Check::Sbom)
    }

    /// Reads the project at `root`.
    pub fn load_with(root: &Path, check: Check) -> Result<Project, String> {
        let manifest = read_manifest(root)?;
        let resolution = resolve(root, &manifest)?;
        let mut warnings = Vec::new();
        if check == Check::Sbom {
            verify_sbom(root, &resolution)?;
        }
        for p in &resolution.packages {
            if let Some(reason) = &p.yanked {
                warnings.push(format!(
                    "{} {} was yanked ({reason}); the SBOM keeps it, but upgrade soon",
                    p.name, p.version
                ));
            }
        }
        let mut project = Project::bare();
        let read = |path: &Path| {
            fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display()))
        };
        // The dependencies' modules, then the project's own.
        let dependencies = dependency_files(&mut project.db, &resolution, &[])?;
        project.dependencies = dependencies.len();
        project.files.extend(dependencies);
        let paths =
            module_files(root).map_err(|e| format!("cannot read {}: {e}", root.display()))?;
        for relative in paths {
            let text = read(&root.join(&relative))?;
            let path = module_path(&manifest.package, &relative);
            let module = ModuleId::new(&project.db, path, SourceFile::new(&project.db, text));
            project.files.push(ModuleFile {
                module,
                shown: relative.display().to_string(),
                dir: relative.parent().map(Path::to_path_buf).unwrap_or_default(),
                dependency: None,
            });
        }
        let modules = project.files.iter().map(|f| f.module).collect();
        project.program.set_modules(&mut project.db).to(modules);
        if !resolution.packages.is_empty() {
            project
                .program
                .set_packages(&mut project.db)
                .to(packages(&manifest, &resolution));
        }
        project.package = manifest.package.clone();
        project.main = manifest.main.clone();
        project.root = Some(root.to_path_buf());
        project.manifest = Some(manifest);
        project.resolution = resolution;
        project.warnings = warnings;
        project.read_resources();
        Ok(project)
    }

    /// Reads the manifest again and puts the modules of the packages it now
    /// resolves to in place of the old ones, keeping those of packages
    /// that did not change, as after `add`, `remove` or `upgrade`. The
    /// database stays, so code already compiled from it keeps its ids.
    pub fn reload_dependencies(&mut self) -> Result<(), String> {
        let root = self.root.clone().ok_or("no project is loaded")?;
        let manifest = read_manifest(&root)?;
        let resolution = resolve(&root, &manifest)?;
        verify_sbom(&root, &resolution)?;
        let range = STD.len()..STD.len() + self.dependencies;
        let old: Vec<ModuleFile> = self.files[range.clone()].to_vec();
        let new = dependency_files(&mut self.db, &resolution, &old)?;
        self.dependencies = new.len();
        self.files.splice(range, new);
        let modules = self.files.iter().map(|f| f.module).collect();
        self.program.set_modules(&mut self.db).to(modules);
        let packages = match resolution.packages.is_empty() {
            true => Packages::default(),
            false => packages(&manifest, &resolution),
        };
        if *self.program.packages(&self.db) != packages {
            self.program.set_packages(&mut self.db).to(packages);
        }
        self.warnings = resolution
            .packages
            .iter()
            .filter_map(|p| {
                let reason = p.yanked.as_ref()?;
                Some(format!(
                    "{} {} was yanked ({reason}); the SBOM keeps it, but upgrade soon",
                    p.name, p.version
                ))
            })
            .collect();
        self.manifest = Some(manifest);
        self.resolution = resolution;
        self.read_resources();
        Ok(())
    }

    /// A program of `std` alone, as the REPL has outside a project.
    pub fn bare() -> Project {
        let db = RootDatabase::new();
        let files: Vec<ModuleFile> = STD
            .iter()
            .map(|(name, text)| ModuleFile {
                module: ModuleId::new(
                    &db,
                    name.to_string(),
                    SourceFile::new(&db, text.to_string()),
                ),
                shown: format!("{name} (bundled)"),
                dir: PathBuf::new(),
                dependency: None,
            })
            .collect();
        let program = Program::new(&db, files.iter().map(|f| f.module).collect(), Vec::new());
        Project {
            db,
            program,
            package: String::new(),
            main: None,
            files,
            root: None,
            manifest: None,
            resolution: Resolution::default(),
            warnings: Vec::new(),
            dependencies: 0,
        }
    }

    /// Adds a module that no file holds, such as the REPL's session, shown
    /// as `shown`.
    pub fn add_module(&mut self, path: &str, shown: &str, text: String) -> ModuleId {
        let module = ModuleId::new(&self.db, path.to_string(), SourceFile::new(&self.db, text));
        self.files.push(ModuleFile {
            module,
            shown: shown.to_string(),
            dir: PathBuf::new(),
            dependency: None,
        });
        let modules = self.files.iter().map(|f| f.module).collect();
        self.program.set_modules(&mut self.db).to(modules);
        module
    }

    /// Reads the project's files again, as a reload does, and gives the
    /// database those that changed on disk: the files that did.
    pub fn refresh(&mut self) -> Vec<String> {
        let Some(root) = self.root.clone() else {
            return Vec::new();
        };
        let mut changed = Vec::new();
        for i in STD.len() + self.dependencies..self.files.len() {
            let file = &self.files[i];
            let Ok(text) = fs::read_to_string(root.join(&file.shown)) else {
                continue;
            };
            if text != *self.source(file.module) {
                let (module, shown) = (file.module, file.shown.clone());
                self.set_source(module, text);
                changed.push(shown);
            }
        }
        changed
    }

    /// The text of each of the project's files as the database holds it;
    /// modules no file holds, such as the REPL's, are left out.
    pub fn texts(&self) -> Vec<(String, String)> {
        let Some(root) = &self.root else {
            return Vec::new();
        };
        self.own()
            .iter()
            .filter(|f| root.join(&f.shown).is_file())
            .map(|f| (f.shown.clone(), self.source(f.module).to_string()))
            .collect()
    }

    /// The modules of the project itself, without `std` and the
    /// dependencies.
    pub fn own(&self) -> &[ModuleFile] {
        &self.files[STD.len() + self.dependencies..]
    }

    pub fn file(&self, module: ModuleId) -> &ModuleFile {
        self.files
            .iter()
            .find(|f| f.module == module)
            .expect("a module of the project")
    }

    pub fn module(&self, path: &str) -> Option<ModuleId> {
        let db = &self.db;
        self.files
            .iter()
            .map(|f| f.module)
            .find(|m| m.path(db) == path)
    }

    pub fn source(&self, module: ModuleId) -> &str {
        module.file(&self.db).text(&self.db)
    }

    /// Replaces the text of a module, as an edit of its file does.
    pub fn set_source(&mut self, module: ModuleId, text: String) {
        let file = module.file(&self.db);
        file.set_text(&mut self.db).to(text);
        self.read_resources();
    }

    /// Reads the resources the modules' `embed` declarations name and
    /// gives the database those that changed: new sources, other content,
    /// or a read that now fails or succeeds.
    pub fn read_resources(&mut self) {
        let root = self.root.clone().unwrap_or_else(|| PathBuf::from("."));
        let old = self.program.resources(&self.db).clone();
        let mut resources = Vec::new();
        for file in &self.files {
            for source in embed_sources(&self.db, file.module) {
                if resources
                    .iter()
                    .any(|(m, s, _): &(ModuleId, String, Resource)| {
                        *m == file.module && *s == source
                    })
                {
                    continue;
                }
                let content = match &file.dependency {
                    Some(d) => read_resource(&d.package_dir, d.layout, &file.dir, &source),
                    None => read_resource(&root, Layout::Project, &file.dir, &source),
                };
                let known = old
                    .iter()
                    .find(|(m, s, _)| *m == file.module && *s == source);
                let resource = match known {
                    Some(&(_, _, resource)) => {
                        if *resource.content(&self.db) != content {
                            let _old = resource.set_content(&mut self.db).to(content);
                        }
                        resource
                    }
                    None => Resource::new(&self.db, content),
                };
                resources.push((file.module, source, resource));
            }
        }
        if resources != old {
            self.program.set_resources(&mut self.db).to(resources);
        }
    }
}

/// The content of the file an `embed` source names: a path relative to the
/// directory `dir` of the module's file, within the package at `root`,
/// whose layout says where its resources are.
fn read_resource(
    root: &Path,
    layout: Layout,
    dir: &Path,
    source: &str,
) -> Result<Arc<[u8]>, String> {
    let outside = || format!("`{source}` is outside the package");
    let path = resource_path(dir, source)?;
    let full = layout.resource(root, &path);
    // A link may lead out of the package.
    let real = full.canonicalize();
    let base = root.canonicalize();
    if let (Ok(real), Ok(base)) = (&real, &base)
        && !real.starts_with(base)
    {
        return Err(outside());
    }
    match fs::read(&full) {
        Ok(bytes) => Ok(Arc::from(bytes)),
        Err(e) => Err(format!("cannot read `{source}`: {e}")),
    }
}

/// Where an `embed` source of a module in the directory `dir` lies,
/// relative to its package's root; an error when that is outside it.
pub fn resource_path(dir: &Path, source: &str) -> Result<PathBuf, String> {
    let mut path = PathBuf::new();
    for part in dir.join(source).components() {
        match part {
            Component::CurDir => {}
            Component::ParentDir => {
                if !path.pop() {
                    return Err(format!("`{source}` is outside the package"));
                }
            }
            Component::Normal(name) => path.push(name),
            Component::RootDir | Component::Prefix(_) => {
                return Err(format!(
                    "`{source}` is absolute; an `embed` names a file relative to its module"
                ));
            }
        }
    }
    Ok(path)
}

/// The modules of the resolved packages, leaving out their test and tool
/// modules; a module of `old` that is the same file of the same package
/// folder is kept, with its text brought up to date.
fn dependency_files(
    db: &mut RootDatabase,
    resolution: &Resolution,
    old: &[ModuleFile],
) -> Result<Vec<ModuleFile>, String> {
    let mut files = Vec::new();
    for p in &resolution.packages {
        let dir = p.layout.modules_dir(&p.dir);
        let paths =
            module_files(&dir).map_err(|e| format!("cannot read {}: {e}", dir.display()))?;
        for relative in paths {
            let path = module_path(&p.name, &relative);
            // A dependency's tests and tools are its own business.
            if is_dev_module(&p.name, &path) {
                continue;
            }
            let location = dir.join(&relative);
            let text = fs::read_to_string(&location)
                .map_err(|e| format!("cannot read {}: {e}", location.display()))?;
            let kept = old.iter().find(|f| {
                f.dependency.as_ref().is_some_and(|d| d.file == location)
                    && f.module.path(db) == &path
            });
            let module = match kept {
                Some(f) => {
                    let file = f.module.file(db);
                    if *file.text(db) != text {
                        file.set_text(db).to(text);
                    }
                    f.module
                }
                None => ModuleId::new(db, path, SourceFile::new(db, text)),
            };
            files.push(ModuleFile {
                module,
                shown: format!("{} {}/{}", p.name, p.version, relative.display()),
                dir: relative.parent().map(Path::to_path_buf).unwrap_or_default(),
                dependency: Some(DependencyFile {
                    package_dir: p.dir.clone(),
                    layout: p.layout,
                    file: location,
                }),
            });
        }
    }
    Ok(files)
}

/// The manifest of the project at `root`.
pub fn read_manifest(root: &Path) -> Result<Manifest, String> {
    let file = root.join("package.crag");
    let text =
        fs::read_to_string(&file).map_err(|e| format!("cannot read {}: {e}", file.display()))?;
    Manifest::parse(&text).map_err(|errors| {
        let lines: Vec<String> = errors
            .iter()
            .map(|e| format!("package.crag:{}: {}", e.line, e.message))
            .collect();
        lines.join("\n")
    })
}

/// The packages the manifest's imports resolve to, against the registries
/// of the user's settings.
pub fn resolve(root: &Path, manifest: &Manifest) -> Result<Resolution, String> {
    if manifest.imports.is_empty() {
        return Ok(Resolution::default());
    }
    let registries = match crag_package::home::crag_home() {
        Some(home) => crag_package::home::registries(&home)?,
        None => Vec::new(),
    };
    crag_package::resolve(manifest, root, &registries).map_err(|errors| errors.join("\n"))
}

/// Checks the resolved packages against the committed `sbom.crag`.
fn verify_sbom(root: &Path, resolution: &Resolution) -> Result<(), String> {
    let new = Sbom::of(resolution);
    let file = root.join("sbom.crag");
    let old = match fs::read_to_string(&file) {
        Ok(text) => Sbom::parse(&text)?,
        Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
            if new.entries.is_empty() {
                return Ok(());
            }
            return Err(
                "the project has dependencies but no sbom.crag; `crag sbom regenerate` writes it"
                    .into(),
            );
        }
        Err(e) => return Err(format!("cannot read {}: {e}", file.display())),
    };
    let diff = old.diff(&new);
    if diff.is_empty() {
        return Ok(());
    }
    Err(format!(
        "sbom.crag does not match the packages the manifests resolve to:\n  {}\n`crag sbom diff` shows it again; `crag sbom regenerate` accepts it",
        diff.join("\n  ")
    ))
}

/// The packages of the program, the project's first, for their
/// boundaries.
fn packages(manifest: &Manifest, resolution: &Resolution) -> Packages {
    let scope = |m: &Manifest| PackageScope {
        name: m.package.clone(),
        exports: m.exports.clone(),
        imports: m
            .imports
            .iter()
            .filter(|d| !d.dev)
            .map(|d| d.name.clone())
            .collect(),
        dev_imports: m
            .imports
            .iter()
            .filter(|d| d.dev)
            .map(|d| d.name.clone())
            .collect(),
    };
    let mut packages = vec![scope(manifest)];
    packages.extend(resolution.packages.iter().map(|p| PackageScope {
        dev_imports: Vec::new(),
        ..scope(&p.manifest)
    }));
    Packages { packages }
}
