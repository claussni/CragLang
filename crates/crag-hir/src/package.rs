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

//! Packages as visibility boundaries (Specification §14.5): a module sees
//! the modules of its own package, `std`, and the modules that the
//! packages its manifest imports export. Development imports are seen by
//! test and tool modules only: those below the package's top-level `test`
//! and `tools` directories.
//!
//! A program without packages, such as one a test builds, has no
//! boundaries. A module of no package, such as the REPL's session, sees
//! what the first package, the application, sees.

/// One package of a program.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct PackageScope {
    pub name: String,
    /// The paths its manifest exports: modules, or directories whose
    /// modules directly in them are exported.
    pub exports: Vec<String>,
    /// The packages its manifest imports, and those it imports for
    /// development.
    pub imports: Vec<String>,
    pub dev_imports: Vec<String>,
    /// The native libraries its manifest declares: the name `cLib` uses,
    /// and the files to try, in order (§14.5.1).
    pub natives: Vec<(String, Vec<String>)>,
}

/// The packages of a program, the application first.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Packages {
    pub packages: Vec<PackageScope>,
}

impl Packages {
    /// The package a module belongs to: the longest package name that is
    /// a prefix of its path. `std` belongs to none.
    pub fn of(&self, module: &str) -> Option<&PackageScope> {
        self.packages
            .iter()
            .filter(|p| {
                module
                    .strip_prefix(p.name.as_str())
                    .is_some_and(|rest| rest.starts_with('.'))
            })
            .max_by_key(|p| p.name.len())
    }

    /// The files a module's `cLib(library)` stands for: those its
    /// package's manifest declares, or the name itself outside any
    /// package; none when the package declares no such library.
    pub fn native_files(&self, module: &str, library: &str) -> Option<Vec<String>> {
        match self.of(module).or(self.packages.first()) {
            Some(package) => package
                .natives
                .iter()
                .find(|(name, _)| name == library)
                .map(|(_, files)| files.clone()),
            None => Some(vec![library.to_string()]),
        }
    }

    /// Why `importer` may not import the module `target`, if it may not.
    pub fn hidden(&self, importer: &str, target: &str) -> Option<String> {
        let to = self.of(target)?;
        let from = self.of(importer).or(self.packages.first())?;
        if from.name == to.name {
            return None;
        }
        let exported = to.exports.iter().any(|e| {
            e == target
                || target
                    .strip_prefix(e.as_str())
                    .and_then(|rest| rest.strip_prefix('.'))
                    .is_some_and(|rest| !rest.contains('.'))
        });
        let dev_module = importer
            .strip_prefix(from.name.as_str())
            .and_then(|rest| rest.strip_prefix('.'))
            .is_some_and(|rest| rest.starts_with("test.") || rest.starts_with("tools."));
        if from.imports.contains(&to.name) || (dev_module && from.dev_imports.contains(&to.name)) {
            return (!exported).then(|| format!("package {} does not export `{target}`", to.name));
        }
        Some(if from.dev_imports.contains(&to.name) {
            format!(
                "{} is a development import of {}; only test and tool modules (below `test` and `tools`) import it",
                to.name, from.name
            )
        } else {
            format!(
                "package {} does not import {}; add `import {} <version>` to its manifest",
                from.name, to.name, to.name
            )
        })
    }
}
