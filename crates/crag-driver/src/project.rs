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

//! A project on disk: its manifest and its module files.
//!
//! M1 reads only the `package` and `main` lines of `package.crag`; the full
//! manifest comes with the resolver (Implementation Plan §11.9.1). Every
//! other `.crag` file below the root is a module, named by the package and
//! its path: `geo/shape.crag` in package `demo` is `demo.geo.shape`.

use std::fs;
use std::path::{Path, PathBuf};

use crag_db::{RootDatabase, Setter};
use crag_hir::{ModuleId, PRELUDE, Program, SourceFile};

/// The prelude, bundled with the tool (Specification §19.4).
const CORE: &str = include_str!("../../../std/core.crag");

/// A module's file, where diagnostics name it.
#[derive(Clone, Debug)]
pub struct ModuleFile {
    pub module: ModuleId,
    /// The path shown to the user, relative to the project's root, or the
    /// prelude's module path.
    pub shown: String,
}

/// The project's modules in a database.
pub struct Project {
    pub db: RootDatabase,
    pub program: Program,
    pub package: String,
    /// The entry module the manifest names.
    pub main: Option<String>,
    /// The prelude first, then the project's modules by path.
    pub files: Vec<ModuleFile>,
}

impl Project {
    /// Reads the project at `root`.
    pub fn load(root: &Path) -> Result<Project, String> {
        let manifest = root.join("package.crag");
        let text = fs::read_to_string(&manifest)
            .map_err(|e| format!("cannot read {}: {e}", manifest.display()))?;
        let (mut package, mut main) = (None, None);
        for line in text.lines() {
            let mut words = line.split_whitespace();
            match (words.next(), words.next()) {
                (Some("package"), Some(name)) => package = Some(name.to_string()),
                (Some("main"), Some(module)) => main = Some(module.to_string()),
                _ => {}
            }
        }
        let package = package.ok_or("package.crag has no `package` line")?;
        let mut paths = Vec::new();
        collect(root, &mut paths).map_err(|e| format!("cannot read {}: {e}", root.display()))?;
        paths.sort();
        let mut project = Project::bare();
        let (db, files) = (&project.db, &mut project.files);
        for path in paths {
            let relative = path.strip_prefix(root).unwrap_or(&path);
            if relative == Path::new("package.crag") {
                continue;
            }
            let text = fs::read_to_string(&path)
                .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
            let segments: Vec<String> = relative
                .with_extension("")
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            let name = format!("{package}.{}", segments.join("."));
            let module = ModuleId::new(db, name, SourceFile::new(db, text));
            files.push(ModuleFile {
                module,
                shown: relative.display().to_string(),
            });
        }
        let modules = project.files.iter().map(|f| f.module).collect();
        project.program.set_modules(&mut project.db).to(modules);
        project.package = package;
        project.main = main;
        Ok(project)
    }

    /// A program of the prelude alone, as the REPL has outside a project.
    pub fn bare() -> Project {
        let db = RootDatabase::new();
        let core = ModuleId::new(
            &db,
            PRELUDE.to_string(),
            SourceFile::new(&db, CORE.to_string()),
        );
        let files = vec![ModuleFile {
            module: core,
            shown: format!("{PRELUDE} (bundled)"),
        }];
        let program = Program::new(&db, vec![core]);
        Project {
            db,
            program,
            package: String::new(),
            main: None,
            files,
        }
    }

    /// Adds a module that no file holds, such as the REPL's session, shown
    /// as `shown`.
    pub fn add_module(&mut self, path: &str, shown: &str, text: String) -> ModuleId {
        let module = ModuleId::new(&self.db, path.to_string(), SourceFile::new(&self.db, text));
        self.files.push(ModuleFile {
            module,
            shown: shown.to_string(),
        });
        let modules = self.files.iter().map(|f| f.module).collect();
        self.program.set_modules(&mut self.db).to(modules);
        module
    }

    /// The modules of the project itself, without the prelude.
    pub fn own(&self) -> &[ModuleFile] {
        &self.files[1..]
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
    }
}

/// The `.crag` files below `dir`, leaving out hidden directories and the
/// build output.
fn collect(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        let name = path.file_name().map(|n| n.to_string_lossy().into_owned());
        let name = name.unwrap_or_default();
        if path.is_dir() {
            if !name.starts_with('.') && name != "target" {
                collect(&path, out)?;
            }
        } else if path.extension().is_some_and(|e| e == "crag") {
            out.push(path);
        }
    }
    Ok(())
}
