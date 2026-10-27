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

//! Resolution (Specification §14.5.1): within each major version, the
//! application settles on the highest version any manifest requires. The
//! requirements of every version the walk reads count, also of versions a
//! higher one replaces, so the result follows from the manifests alone and
//! needs no lock file.

use std::collections::{BTreeMap, HashMap, HashSet, VecDeque};
use std::fs;
use std::path::{Path, PathBuf};

use crate::RUNTIME;
use crate::content::{CONTENT_HASH, Layout, content_hash};
use crate::manifest::{Manifest, Source};
use crate::registry::Registry;
use crate::version::Version;

/// Where a resolved package comes from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Origin {
    /// The registry of that name.
    Registry(String),
    /// A folder a `path:` source names, as written.
    Path(String),
}

/// A package the application uses.
#[derive(Clone, Debug)]
pub struct Resolved {
    pub name: String,
    pub version: Version,
    pub dir: PathBuf,
    pub layout: Layout,
    pub origin: Origin,
    pub manifest: Manifest,
    /// The content hash: as published for a registry's package, computed
    /// for a folder.
    pub hash: String,
    /// Why the version was yanked, if it was.
    pub yanked: Option<String>,
}

#[derive(Clone, Debug, Default)]
pub struct Resolution {
    /// By name, one version each.
    pub packages: Vec<Resolved>,
}

impl Resolution {
    pub fn get(&self, name: &str) -> Option<&Resolved> {
        self.packages.iter().find(|p| p.name == name)
    }
}

/// A requirement met on the walk: a package at a version, from the
/// package whose manifest states it.
struct Requirement {
    name: String,
    version: Version,
    by: String,
    /// The source the stating manifest names, against its directory.
    source: Option<(String, PathBuf)>,
}

/// Resolves the dependencies of the package whose manifest `root` stands
/// in `root_dir`, against `registries`. Development imports count for the
/// root only.
pub fn resolve(
    root: &Manifest,
    root_dir: &Path,
    registries: &[Registry],
) -> Result<Resolution, Vec<String>> {
    let mut errors = Vec::new();
    let mut queue: VecDeque<Requirement> = VecDeque::new();
    let push = |queue: &mut VecDeque<Requirement>, manifest: &Manifest, dir: &Path, dev: bool| {
        for dep in manifest.imports.iter().filter(|d| dev || !d.dev) {
            queue.push_back(Requirement {
                name: dep.name.clone(),
                version: dep.version,
                by: manifest.package.clone(),
                source: dep
                    .source
                    .as_ref()
                    .map(|Source::Path(p)| (format!("path:{}", p.display()), dir.join(p))),
            });
        }
    };
    push(&mut queue, root, root_dir, true);
    // The source of each package, settled where it is first met: the root's
    // manifest comes first.
    let mut origins: HashMap<String, (Origin, Option<PathBuf>)> = HashMap::new();
    let mut best: BTreeMap<(String, u32), (Version, Vec<String>)> = BTreeMap::new();
    let mut read: HashSet<(String, Version)> = HashSet::new();
    let mut folders: HashMap<(String, Version), (PathBuf, Manifest)> = HashMap::new();
    while let Some(req) = queue.pop_front() {
        if req.name == root.package {
            errors.push(format!(
                "{} imports {}, the package being built",
                req.by, req.name
            ));
            continue;
        }
        let (origin, folder) = match origins.get(&req.name) {
            Some(known) => known.clone(),
            None => {
                let found = match &req.source {
                    Some((shown, dir)) => Ok((Origin::Path(shown.clone()), Some(dir.clone()))),
                    None => locate(&req.name, registries).map(|r| (Origin::Registry(r), None)),
                };
                match found {
                    Ok(found) => {
                        origins.insert(req.name.clone(), found.clone());
                        found
                    }
                    Err(e) => {
                        errors.push(format!("{} (imported by {})", e, req.by));
                        origins.insert(req.name.clone(), (Origin::Path(String::new()), None));
                        continue;
                    }
                }
            }
        };
        if matches!(&origin, Origin::Path(p) if p.is_empty()) {
            continue;
        }
        let entry = best
            .entry((req.name.clone(), req.version.major))
            .or_insert((req.version, Vec::new()));
        if req.version > entry.0 {
            entry.0 = req.version;
        }
        entry
            .1
            .push(format!("{} requires {} {}", req.by, req.name, req.version));
        if !read.insert((req.name.clone(), req.version)) {
            continue;
        }
        let place = match (&origin, &folder) {
            (Origin::Registry(r), _) => {
                let registry = registries.iter().find(|x| &x.name == r).expect("located");
                match registry.version_dir(&req.name, &req.version) {
                    Some(dir) => dir,
                    None => {
                        let have: Vec<String> = registry
                            .versions(&req.name)
                            .iter()
                            .map(|(v, _)| v.to_string())
                            .collect();
                        errors.push(format!(
                            "{} {} is not in registry `{r}`, which has {} (imported by {})",
                            req.name,
                            req.version,
                            have.join(", "),
                            req.by
                        ));
                        continue;
                    }
                }
            }
            (Origin::Path(_), Some(dir)) => dir.clone(),
            (Origin::Path(_), None) => continue,
        };
        let manifest = match read_manifest(&place) {
            Ok(m) => m,
            Err(e) => {
                errors.push(e);
                continue;
            }
        };
        if manifest.package != req.name {
            errors.push(format!(
                "{} holds package `{}`, not `{}`",
                place.display(),
                manifest.package,
                req.name
            ));
            continue;
        }
        if let (Origin::Path(shown), Some(v)) = (&origin, manifest.version)
            && !req.version.satisfied_by(&v)
        {
            errors.push(format!(
                "{} requires {} {}, but {shown} holds {v}",
                req.by, req.name, req.version
            ));
            continue;
        }
        if let Some(runtime) = manifest.runtime
            && !runtime.satisfied_by(&RUNTIME)
        {
            errors.push(format!(
                "{} {} requires runtime {runtime}; this is runtime {RUNTIME}",
                req.name, req.version
            ));
        }
        push(&mut queue, &manifest, &place, false);
        folders.insert((req.name.clone(), req.version), (place, manifest));
    }
    // One major per package for now: two would need module paths that
    // tell the majors apart.
    let mut majors: BTreeMap<&str, Vec<(u32, &Vec<String>)>> = BTreeMap::new();
    for ((name, major), (_, why)) in &best {
        majors.entry(name).or_default().push((*major, why));
    }
    for (name, list) in &majors {
        if list.len() > 1 {
            let why: Vec<String> = list.iter().flat_map(|(_, w)| w.iter().cloned()).collect();
            errors.push(format!(
                "the application needs several majors of {name} ({}); using two majors of a package in one application is not supported yet",
                why.join("; ")
            ));
        }
    }
    let mut resolution = Resolution::default();
    for ((name, _), (version, _)) in &best {
        let (origin, _) = origins[name].clone();
        let Some((dir, manifest)) = folders.get(&(name.clone(), *version)).cloned() else {
            continue;
        };
        let layout = Layout::of(&dir);
        let hash = match &origin {
            Origin::Registry(_) => {
                let published = fs::read_to_string(dir.join(CONTENT_HASH)).unwrap_or_default();
                let actual = content_hash(&dir).unwrap_or_default();
                if published.trim() != actual {
                    errors.push(format!(
                        "{name} {version} in {} does not match its content hash; the registry was changed after publishing",
                        dir.display()
                    ));
                }
                actual
            }
            Origin::Path(_) => content_hash(&dir).unwrap_or_default(),
        };
        let yanked = match &origin {
            Origin::Registry(r) => registries
                .iter()
                .find(|x| &x.name == r)
                .and_then(|x| x.yanked(name, version)),
            Origin::Path(_) => None,
        };
        resolution.packages.push(Resolved {
            name: name.clone(),
            version: manifest.version.unwrap_or(*version),
            dir,
            layout,
            origin,
            manifest,
            hash,
            yanked,
        });
    }
    if errors.is_empty() {
        Ok(resolution)
    } else {
        Err(errors)
    }
}

/// The registry that has the package: exactly one must (§20.4).
fn locate(name: &str, registries: &[Registry]) -> Result<String, String> {
    let having: Vec<&Registry> = registries.iter().filter(|r| r.has(name)).collect();
    match having[..] {
        [one] => Ok(one.name.clone()),
        [] if registries.is_empty() => Err(format!(
            "package {name} is not found: no registry is set up (registries.crag in the settings directory)"
        )),
        [] => Err(format!("package {name} is in no registry")),
        _ => {
            let names: Vec<&str> = having.iter().map(|r| r.name.as_str()).collect();
            Err(format!(
                "package {name} is in several registries ({}); name the source with `from`",
                names.join(", ")
            ))
        }
    }
}

/// The manifest of a package folder.
pub fn read_manifest(dir: &Path) -> Result<Manifest, String> {
    let file = dir.join("package.crag");
    let text =
        fs::read_to_string(&file).map_err(|e| format!("cannot read {}: {e}", file.display()))?;
    Manifest::parse(&text).map_err(|errors| {
        let lines: Vec<String> = errors
            .iter()
            .map(|e| format!("{}:{}: {}", file.display(), e.line, e.message))
            .collect();
        lines.join("\n")
    })
}
