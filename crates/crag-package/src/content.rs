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

//! The content of a package folder and its hash (Specification §20.4): the
//! manifest, the modules in `src/`, the `embed` sources in `res/`, and the
//! generated `api.crag` and `sbom.crag`. `content.hash` holds the hash
//! over all of them, and `yanked` is not part of it.

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

/// The file holding a published version's content hash.
pub const CONTENT_HASH: &str = "content.hash";

const CONTENT: [&str; 5] = ["package.crag", "src", "res", "api.crag", "sbom.crag"];

/// The files of a package folder that its hash covers, by path relative
/// to the folder with `/` between segments, sorted.
pub fn content_files(dir: &Path) -> io::Result<Vec<(String, PathBuf)>> {
    let mut files = Vec::new();
    for top in CONTENT {
        walk(dir, Path::new(top), &mut files)?;
    }
    files.sort();
    Ok(files)
}

fn walk(base: &Path, relative: &Path, out: &mut Vec<(String, PathBuf)>) -> io::Result<()> {
    let path = base.join(relative);
    if path.is_dir() {
        for entry in fs::read_dir(&path)? {
            walk(base, &relative.join(entry?.file_name()), out)?;
        }
    } else if path.is_file() {
        let shown: Vec<String> = relative
            .components()
            .map(|c| c.as_os_str().to_string_lossy().into_owned())
            .collect();
        out.push((shown.join("/"), path));
    }
    Ok(())
}

/// The BLAKE3 hash over the content's paths and bytes, in hex.
pub fn content_hash(dir: &Path) -> io::Result<String> {
    let mut hasher = blake3::Hasher::new();
    for (shown, path) in content_files(dir)? {
        let bytes = fs::read(path)?;
        hasher.update(&(shown.len() as u64).to_le_bytes());
        hasher.update(shown.as_bytes());
        hasher.update(&(bytes.len() as u64).to_le_bytes());
        hasher.update(&bytes);
    }
    Ok(hasher.finalize().to_hex().to_string())
}

/// How a package folder holds its modules: a published version keeps
/// them in `src/` and its `embed` sources in `res/`; a project, which a
/// `path:` source may name, keeps both below its root.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    Published,
    Project,
}

impl Layout {
    pub fn of(dir: &Path) -> Layout {
        match dir.join("src").is_dir() && dir.join(CONTENT_HASH).is_file() {
            true => Layout::Published,
            false => Layout::Project,
        }
    }

    /// Where the modules' files are.
    pub fn modules_dir(self, dir: &Path) -> PathBuf {
        match self {
            Layout::Published => dir.join("src"),
            Layout::Project => dir.to_path_buf(),
        }
    }

    /// Where an `embed` source at `path`, relative to the package's root,
    /// is.
    pub fn resource(self, dir: &Path, path: &Path) -> PathBuf {
        match self {
            Layout::Published => dir.join("res").join(path),
            Layout::Project => dir.join(path),
        }
    }
}

/// The module files below `dir`, sorted, as paths relative to it: every
/// `.crag` file except the manifest, leaving out hidden directories and
/// the build output.
pub fn module_files(dir: &Path) -> io::Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    collect(dir, dir, &mut out)?;
    out.sort();
    Ok(out)
}

fn collect(base: &Path, dir: &Path, out: &mut Vec<PathBuf>) -> io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let path = entry?.path();
        let name = path.file_name().map(|n| n.to_string_lossy().into_owned());
        let name = name.unwrap_or_default();
        if path.is_dir() {
            if !name.starts_with('.') && name != "target" {
                collect(base, &path, out)?;
            }
        } else if path.extension().is_some_and(|e| e == "crag") {
            let relative = path.strip_prefix(base).unwrap_or(&path).to_path_buf();
            let generated = ["package.crag", "api.crag", "sbom.crag"];
            if !generated.iter().any(|g| relative == Path::new(g)) {
                out.push(relative);
            }
        }
    }
    Ok(())
}

/// The module a file at `relative` holds in package `package`:
/// `geo/shape.crag` in `demo` is `demo.geo.shape`.
pub fn module_path(package: &str, relative: &Path) -> String {
    let segments: Vec<String> = relative
        .with_extension("")
        .components()
        .map(|c| c.as_os_str().to_string_lossy().into_owned())
        .collect();
    format!("{package}.{}", segments.join("."))
}

/// Whether a module is a test or tool module, which alone may import
/// development dependencies: one below the package's top-level `test` or
/// `tools` directory.
pub fn is_dev_module(package: &str, module: &str) -> bool {
    module
        .strip_prefix(package)
        .and_then(|rest| rest.strip_prefix('.'))
        .is_some_and(|rest| rest.starts_with("test.") || rest.starts_with("tools."))
}
