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

//! Folder registries (Specification §20.4): a package version is a folder
//! `<registry>/<name as directories>/<version>/` that is never changed once
//! it is published. Publishing fills a folder in `.staging/` and renames it
//! into place, so a reader sees a whole package or none.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use crate::content::{CONTENT_HASH, content_hash};
use crate::version::Version;

/// The format of registry folders this tool reads and writes.
pub const FORMAT: u32 = 1;

/// A registry, under the name the user's settings give it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Registry {
    pub name: String,
    pub dir: PathBuf,
}

impl Registry {
    /// Opens the registry folder `dir`, checking its `registry.crag`.
    pub fn open(name: &str, dir: &Path) -> Result<Registry, String> {
        let file = dir.join("registry.crag");
        let text = fs::read_to_string(&file)
            .map_err(|e| format!("registry `{name}`: cannot read {}: {e}", file.display()))?;
        let format = text
            .lines()
            .find_map(|l| l.trim().strip_prefix("format "))
            .and_then(|f| f.trim().parse::<u32>().ok());
        match format {
            Some(FORMAT) => Ok(Registry {
                name: name.to_string(),
                dir: dir.to_path_buf(),
            }),
            Some(other) => Err(format!(
                "registry `{name}` has format {other}; this tool reads format {FORMAT}"
            )),
            None => Err(format!(
                "registry `{name}`: {} states no format",
                file.display()
            )),
        }
    }

    /// Makes `dir` an empty registry named `name`.
    pub fn create(name: &str, dir: &Path) -> io::Result<Registry> {
        fs::create_dir_all(dir.join(".staging"))?;
        fs::write(
            dir.join("registry.crag"),
            format!("registry {name}\nformat {FORMAT}\n"),
        )?;
        Ok(Registry {
            name: name.to_string(),
            dir: dir.to_path_buf(),
        })
    }

    /// The folder of a package: a directory level for each dot.
    pub fn package_dir(&self, package: &str) -> PathBuf {
        package.split('.').fold(self.dir.clone(), |d, s| d.join(s))
    }

    /// The published versions of a package, oldest first, each with its
    /// folder. Version folders start with a digit, so a sub-package's
    /// folder is never one.
    pub fn versions(&self, package: &str) -> Vec<(Version, PathBuf)> {
        let Ok(entries) = fs::read_dir(self.package_dir(package)) else {
            return Vec::new();
        };
        let mut versions: Vec<(Version, PathBuf)> = entries
            .flatten()
            .filter(|e| e.path().join("package.crag").is_file())
            .filter_map(|e| {
                let name = e.file_name().to_string_lossy().into_owned();
                Version::parse(&name).ok().map(|v| (v, e.path()))
            })
            .collect();
        versions.sort_by_key(|a| a.0);
        versions
    }

    pub fn has(&self, package: &str) -> bool {
        !self.versions(package).is_empty()
    }

    /// The folder of a published version.
    pub fn version_dir(&self, package: &str, version: &Version) -> Option<PathBuf> {
        self.versions(package)
            .into_iter()
            .find(|(v, _)| v == version)
            .map(|(_, dir)| dir)
    }

    /// Why a version was yanked, if it was.
    pub fn yanked(&self, package: &str, version: &Version) -> Option<String> {
        let dir = self.version_dir(package, version)?;
        let reason = fs::read_to_string(dir.join("yanked")).ok()?;
        let reason = reason.trim();
        Some(match reason.is_empty() {
            true => "no reason given".to_string(),
            false => reason.to_string(),
        })
    }

    /// Publishes the package folder `from` as `package` `version`: copies
    /// it into `.staging/`, writes its content hash and renames it into
    /// place. A version that exists is never replaced.
    pub fn publish(
        &self,
        package: &str,
        version: &Version,
        from: &Path,
    ) -> Result<PathBuf, String> {
        if self.version_dir(package, version).is_some() {
            return Err(format!(
                "{package} {version} is already in registry `{}`; a published version never changes",
                self.name
            ));
        }
        let fail = |e: io::Error| format!("cannot publish into registry `{}`: {e}", self.name);
        let staging = self
            .dir
            .join(".staging")
            .join(format!("{package}-{version}-{}", std::process::id()));
        let _ = fs::remove_dir_all(&staging);
        copy_dir(from, &staging).map_err(fail)?;
        let hash = content_hash(&staging).map_err(fail)?;
        fs::write(staging.join(CONTENT_HASH), format!("{hash}\n")).map_err(fail)?;
        let target = self.package_dir(package).join(version.to_string());
        fs::create_dir_all(self.package_dir(package)).map_err(fail)?;
        // Renaming onto an existing folder fails, so of two publishes of
        // one version only the first lands.
        if let Err(e) = fs::rename(&staging, &target) {
            let _ = fs::remove_dir_all(&staging);
            return Err(fail(e));
        }
        Ok(target)
    }
}

fn copy_dir(from: &Path, to: &Path) -> io::Result<()> {
    fs::create_dir_all(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let target = to.join(entry.file_name());
        if entry.file_type()?.is_dir() {
            copy_dir(&entry.path(), &target)?;
        } else {
            fs::copy(entry.path(), target)?;
        }
    }
    Ok(())
}
