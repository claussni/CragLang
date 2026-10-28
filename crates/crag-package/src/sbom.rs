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

//! The SBOM `sbom.crag` (Specification §14.5.1, §16.7): every package the
//! build uses, with its version and content hash. It is committed with the
//! project; the build verifies the resolved packages against it and
//! refuses on a mismatch until it is regenerated on purpose.
//!
//! ```text
//! // The packages this build uses. `crag package sbom regenerate` writes it.
//! package geo 1.2 hash "9f3c…"
//! package billing 1.2 path "../billing"
//! ```
//!
//! A package from a `path:` source is a folder under development, so it is
//! recorded without a hash and not verified. The native libraries the
//! application and its packages declare follow, each with its package:
//!
//! ```text
//! native shop sqlite "libsqlite3.so.0", "libsqlite3.so"
//! ```

use crate::manifest::Manifest;
use crate::resolve::{Origin, Resolution};
use crate::version::Version;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub name: String,
    pub version: Version,
    pub hash: Option<String>,
    pub path: Option<String>,
}

/// A `native` declaration of a manifest (§16.7).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeEntry {
    pub package: String,
    pub name: String,
    pub files: Vec<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Sbom {
    /// By name.
    pub entries: Vec<Entry>,
    /// By package, then name.
    pub natives: Vec<NativeEntry>,
}

const HEADER: &str = "// The packages this build uses. `crag package sbom regenerate` writes it.\n";

impl Sbom {
    /// The SBOM of an application's manifest and what it resolves to.
    pub fn of(app: &Manifest, resolution: &Resolution) -> Sbom {
        let mut entries: Vec<Entry> = resolution
            .packages
            .iter()
            .map(|p| Entry {
                name: p.name.clone(),
                version: p.version,
                hash: match p.origin {
                    Origin::Registry(_) => Some(p.hash.clone()),
                    Origin::Path(_) => None,
                },
                path: match &p.origin {
                    Origin::Path(shown) => Some(shown.trim_start_matches("path:").to_string()),
                    Origin::Registry(_) => None,
                },
            })
            .collect();
        entries.sort_by(|a, b| a.name.cmp(&b.name));
        let manifests = std::iter::once(app).chain(resolution.packages.iter().map(|p| &p.manifest));
        let mut natives: Vec<NativeEntry> = manifests
            .flat_map(|m| {
                m.natives.iter().map(|(name, files)| NativeEntry {
                    package: m.package.clone(),
                    name: name.clone(),
                    files: files.clone(),
                })
            })
            .collect();
        natives.sort_by(|a, b| (&a.package, &a.name).cmp(&(&b.package, &b.name)));
        Sbom { entries, natives }
    }

    /// Whether it records nothing.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty() && self.natives.is_empty()
    }

    pub fn write(&self) -> String {
        let mut out = HEADER.to_string();
        for e in &self.entries {
            out.push_str(&format!("package {} {}", e.name, e.version));
            if let Some(hash) = &e.hash {
                out.push_str(&format!(" hash \"{hash}\""));
            }
            if let Some(path) = &e.path {
                out.push_str(&format!(" path \"{path}\""));
            }
            out.push('\n');
        }
        for n in &self.natives {
            let files: Vec<String> = n.files.iter().map(|f| format!("{f:?}")).collect();
            out.push_str(&format!(
                "native {} {} {}\n",
                n.package,
                n.name,
                files.join(", ")
            ));
        }
        out
    }

    pub fn parse(text: &str) -> Result<Sbom, String> {
        let mut entries = Vec::new();
        let mut natives = Vec::new();
        for (i, line) in text.lines().enumerate() {
            let line = line.trim();
            if line.is_empty() || line.starts_with("//") {
                continue;
            }
            let bad = || format!("sbom.crag:{}: cannot read `{line}`", i + 1);
            if let Some(rest) = line.strip_prefix("native ") {
                natives.push(native_entry(rest).ok_or_else(bad)?);
                continue;
            }
            let words: Vec<&str> = line.split_whitespace().collect();
            let ["package", name, version, rest @ ..] = &words[..] else {
                return Err(bad());
            };
            let mut entry = Entry {
                name: name.to_string(),
                version: Version::parse(version).map_err(|_| bad())?,
                hash: None,
                path: None,
            };
            let quoted = |w: &str| {
                w.strip_prefix('"')
                    .and_then(|w| w.strip_suffix('"'))
                    .map(str::to_string)
            };
            match rest {
                ["hash", h] => entry.hash = Some(quoted(h).ok_or_else(bad)?),
                ["path", p] => entry.path = Some(quoted(p).ok_or_else(bad)?),
                _ => return Err(bad()),
            }
            entries.push(entry);
        }
        Ok(Sbom { entries, natives })
    }

    /// What changes from `self` to `new`, one line each: `+` for a package
    /// added, `-` for one removed, `~` for another version or content.
    pub fn diff(&self, new: &Sbom) -> Vec<String> {
        let mut lines = Vec::new();
        for old in &self.entries {
            match new.entries.iter().find(|e| e.name == old.name) {
                None => lines.push(format!("- {} {}", old.name, old.version)),
                Some(e) if e.version.to_string() != old.version.to_string() => {
                    lines.push(format!("~ {} {} -> {}", old.name, old.version, e.version))
                }
                Some(e) if e.hash != old.hash || e.path != old.path => {
                    lines.push(format!("~ {} {}: other content", old.name, old.version))
                }
                Some(_) => {}
            }
        }
        for e in &new.entries {
            if !self.entries.iter().any(|o| o.name == e.name) {
                lines.push(format!("+ {} {}", e.name, e.version));
            }
        }
        let same = |a: &NativeEntry, b: &NativeEntry| a.package == b.package && a.name == b.name;
        for old in &self.natives {
            match new.natives.iter().find(|n| same(n, old)) {
                None => lines.push(format!("- native {} {}", old.package, old.name)),
                Some(n) if n.files != old.files => lines.push(format!(
                    "~ native {} {}: other files",
                    old.package, old.name
                )),
                Some(_) => {}
            }
        }
        for n in &new.natives {
            if !self.natives.iter().any(|o| same(o, n)) {
                lines.push(format!("+ native {} {}", n.package, n.name));
            }
        }
        lines
    }
}

/// `<package> <name> "file", …`, after `native`.
fn native_entry(rest: &str) -> Option<NativeEntry> {
    let (package, rest) = rest.trim().split_once(' ')?;
    let (name, files) = rest.trim().split_once(' ')?;
    let files = files
        .split(',')
        .map(|f| {
            f.trim()
                .strip_prefix('"')
                .and_then(|f| f.strip_suffix('"'))
                .map(str::to_string)
        })
        .collect::<Option<Vec<_>>>()?;
    Some(NativeEntry {
        package: package.to_string(),
        name: name.to_string(),
        files,
    })
}
