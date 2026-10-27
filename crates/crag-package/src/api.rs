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

//! `api.crag`, a package's public surface (Specification §20.5), and the
//! comparison of two of them that decides the version a publish needs.
//!
//! Every `pub` declaration of every module is one entry: its declaration
//! as written, without body, and what the compiler inferred about it,
//! each on an indented line of its own: the success type it does not
//! state (`returns`), the errors it may give, its effects, and the
//! parameters it may store or return (`escaping`). Entries are sorted, so
//! two files diff line by line.
//!
//! ```text
//! package geo 1.1
//!
//! module geo.shape
//! pub fn area(w: Int, h: Int) -> Int
//! pub fn load(path: Str)
//!   returns Str
//!   errors IoError
//!   effects io
//!   escaping path
//! pub type Point(x: Int, y: Int)
//! ```

use crate::version::Version;

#[derive(Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ApiEntry {
    pub module: String,
    /// The declaration as written, without its body, on one line.
    pub decl: String,
    pub returns: Option<String>,
    pub errors: Vec<String>,
    pub effects: Vec<String>,
    pub escaping: Vec<String>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ApiFile {
    pub package: String,
    pub version: Option<Version>,
    pub entries: Vec<ApiEntry>,
}

const HEADER: &str = "// The public API of the package, written on publishing. A publish\n// compares it with the previous version of the same major.\n";

impl ApiFile {
    pub fn new(package: &str, version: Option<Version>, mut entries: Vec<ApiEntry>) -> ApiFile {
        for e in &mut entries {
            e.errors.sort();
            e.errors.dedup();
            e.effects.sort();
            e.escaping.sort();
        }
        entries.sort();
        entries.dedup();
        ApiFile {
            package: package.to_string(),
            version,
            entries,
        }
    }

    pub fn write(&self) -> String {
        let mut out = HEADER.to_string();
        out.push_str(&format!("package {}", self.package));
        if let Some(v) = self.version {
            out.push_str(&format!(" {v}"));
        }
        out.push('\n');
        let mut module = None;
        for e in &self.entries {
            if module != Some(&e.module) {
                out.push_str(&format!("\nmodule {}\n", e.module));
                module = Some(&e.module);
            }
            out.push_str(&e.decl);
            out.push('\n');
            if let Some(r) = &e.returns {
                out.push_str(&format!("  returns {r}\n"));
            }
            for (word, list) in [
                ("errors", &e.errors),
                ("effects", &e.effects),
                ("escaping", &e.escaping),
            ] {
                if !list.is_empty() {
                    out.push_str(&format!("  {word} {}\n", list.join(" | ")));
                }
            }
        }
        out
    }

    pub fn parse(text: &str) -> Result<ApiFile, String> {
        let mut file = ApiFile::default();
        let mut module = String::new();
        for (i, line) in text.lines().enumerate() {
            let bad = || format!("api.crag:{}: cannot read `{line}`", i + 1);
            if line.trim().is_empty() || line.starts_with("//") {
                continue;
            }
            if let Some(rest) = line.strip_prefix("package ") {
                let mut words = rest.split_whitespace();
                file.package = words.next().ok_or_else(bad)?.to_string();
                file.version = words.next().map(Version::parse).transpose()?;
            } else if let Some(rest) = line.strip_prefix("module ") {
                module = rest.trim().to_string();
            } else if let Some(rest) = line.strip_prefix("  ") {
                let entry = file.entries.last_mut().ok_or_else(bad)?;
                let (word, value) = rest.split_once(' ').ok_or_else(bad)?;
                let list = || value.split(" | ").map(str::to_string).collect::<Vec<_>>();
                match word {
                    "returns" => entry.returns = Some(value.to_string()),
                    "errors" => entry.errors = list(),
                    "effects" => entry.effects = list(),
                    "escaping" => entry.escaping = list(),
                    _ => return Err(bad()),
                }
            } else {
                file.entries.push(ApiEntry {
                    module: module.clone(),
                    decl: line.to_string(),
                    ..ApiEntry::default()
                });
            }
        }
        Ok(file)
    }
}

/// How one entry changed from one version to the next.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ApiChange {
    Added(ApiEntry),
    /// Gone, or declared differently, which is the same to a caller.
    Removed(ApiEntry),
    /// What it infers changed: `what` is `returns`, `errors`, `effects` or
    /// `escaping`; `gained` and `lost` list the parts.
    Inferred {
        entry: ApiEntry,
        what: &'static str,
        gained: Vec<String>,
        lost: Vec<String>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Compatibility {
    Compatible,
    Breaking,
}

/// The least version step a set of changes requires.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Bump {
    Patch,
    Minor,
    Major,
}

pub fn diff_api(old: &ApiFile, new: &ApiFile) -> Vec<ApiChange> {
    let key = |e: &ApiEntry| (e.module.clone(), e.decl.clone());
    let mut changes = Vec::new();
    for o in &old.entries {
        match new.entries.iter().find(|n| key(n) == key(o)) {
            None => changes.push(ApiChange::Removed(o.clone())),
            Some(n) => {
                let lists: [(&'static str, Vec<String>, Vec<String>); 4] = [
                    (
                        "returns",
                        o.returns.iter().cloned().collect(),
                        n.returns.iter().cloned().collect(),
                    ),
                    ("errors", o.errors.clone(), n.errors.clone()),
                    ("effects", o.effects.clone(), n.effects.clone()),
                    ("escaping", o.escaping.clone(), n.escaping.clone()),
                ];
                for (what, before, after) in lists {
                    let gained: Vec<String> = after
                        .iter()
                        .filter(|x| !before.contains(x))
                        .cloned()
                        .collect();
                    let lost: Vec<String> = before
                        .iter()
                        .filter(|x| !after.contains(x))
                        .cloned()
                        .collect();
                    if !gained.is_empty() || !lost.is_empty() {
                        changes.push(ApiChange::Inferred {
                            entry: n.clone(),
                            what,
                            gained,
                            lost,
                        });
                    }
                }
            }
        }
    }
    for n in &new.entries {
        if !old.entries.iter().any(|o| key(o) == key(n)) {
            changes.push(ApiChange::Added(n.clone()));
        }
    }
    changes
}

/// A removal or another declaration breaks callers; so does gaining an
/// error, an effect or an escaping parameter, or another inferred success
/// type. Losing them, or an addition, does not.
pub fn classify(change: &ApiChange) -> Compatibility {
    match change {
        ApiChange::Added(_) => Compatibility::Compatible,
        ApiChange::Removed(_) => Compatibility::Breaking,
        ApiChange::Inferred {
            what: "returns", ..
        } => Compatibility::Breaking,
        ApiChange::Inferred { gained, .. } if !gained.is_empty() => Compatibility::Breaking,
        ApiChange::Inferred { .. } => Compatibility::Compatible,
    }
}

/// A breaking change needs a new major; any other change a new minor at
/// least, since a new public name can collide in importers (§14.3); an
/// unchanged API allows a patch.
pub fn required_bump(changes: &[ApiChange]) -> Bump {
    if changes
        .iter()
        .any(|c| classify(c) == Compatibility::Breaking)
    {
        Bump::Major
    } else if changes.is_empty() {
        Bump::Patch
    } else {
        Bump::Minor
    }
}

/// Whether going from `previous` to `next` makes the step `bump` needs.
pub fn allows(previous: &Version, next: &Version, bump: Bump) -> bool {
    let step = if next.major > previous.major {
        Bump::Major
    } else if next.major == previous.major && next.minor > previous.minor {
        Bump::Minor
    } else if next > previous {
        Bump::Patch
    } else {
        return false;
    };
    step >= bump
}

impl std::fmt::Display for ApiChange {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ApiChange::Added(e) => write!(f, "added in {}: {}", e.module, e.decl),
            ApiChange::Removed(e) => write!(f, "removed or changed in {}: {}", e.module, e.decl),
            ApiChange::Inferred {
                entry,
                what,
                gained,
                lost,
            } => {
                write!(f, "{} in {}: {what}", entry.decl, entry.module)?;
                if !gained.is_empty() {
                    write!(f, " gained {}", gained.join(" | "))?;
                }
                if !lost.is_empty() {
                    write!(f, " lost {}", lost.join(" | "))?;
                }
                Ok(())
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn entry(decl: &str) -> ApiEntry {
        ApiEntry {
            module: "geo.shape".into(),
            decl: decl.into(),
            ..ApiEntry::default()
        }
    }

    fn file(entries: Vec<ApiEntry>) -> ApiFile {
        ApiFile::new("geo", Version::parse("1.1").ok(), entries)
    }

    #[test]
    fn the_file_reads_back_as_written() {
        let mut load = entry("pub fn load(path: Str)");
        load.returns = Some("Str".into());
        load.errors = vec!["IoError".into()];
        load.effects = vec!["io".into()];
        load.escaping = vec!["path".into()];
        let api = file(vec![load, entry("pub fn area(w: Int, h: Int) -> Int")]);
        let text = api.write();
        assert!(text.contains("\nmodule geo.shape\npub fn area(w: Int, h: Int) -> Int\npub fn load(path: Str)\n  returns Str\n  errors IoError\n  effects io\n  escaping path\n"), "{text}");
        assert_eq!(ApiFile::parse(&text).unwrap(), api);
    }

    #[test]
    fn changes_decide_the_version_step() {
        let area = entry("pub fn area(w: Int, h: Int) -> Int");
        let old = file(vec![area.clone()]);
        assert_eq!(required_bump(&diff_api(&old, &old)), Bump::Patch);
        let added = file(vec![
            area.clone(),
            entry("pub fn perimeter(w: Int, h: Int) -> Int"),
        ]);
        assert_eq!(required_bump(&diff_api(&old, &added)), Bump::Minor);
        assert_eq!(required_bump(&diff_api(&added, &old)), Bump::Major);
        let mut effectful = area.clone();
        effectful.effects = vec!["io".into()];
        let changes = diff_api(&old, &file(vec![effectful]));
        assert_eq!(required_bump(&changes), Bump::Major);
        assert_eq!(
            changes[0].to_string(),
            "pub fn area(w: Int, h: Int) -> Int in geo.shape: effects gained io"
        );
        let mut escaping = area.clone();
        escaping.escaping = vec!["w".into()];
        assert_eq!(
            required_bump(&diff_api(&old, &file(vec![escaping.clone()]))),
            Bump::Major
        );
        assert_eq!(
            required_bump(&diff_api(&file(vec![escaping]), &old)),
            Bump::Minor
        );
        let v = |t| Version::parse(t).unwrap();
        assert!(allows(&v("1.1"), &v("2.0"), Bump::Major));
        assert!(!allows(&v("1.1"), &v("1.2"), Bump::Major));
        assert!(allows(&v("1.1"), &v("1.2"), Bump::Minor));
        assert!(!allows(&v("1.1"), &v("1.1.1"), Bump::Minor));
        assert!(allows(&v("1.1"), &v("1.1.1"), Bump::Patch));
        assert!(!allows(&v("1.1"), &v("1.1"), Bump::Patch));
    }
}
