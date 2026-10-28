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

//! Folder registries and resolution (Specification §14.5.1, §20.4).

use std::fs;
use std::path::{Path, PathBuf};

use crag_package::home::registries;
use crag_package::{Manifest, Origin, Registry, Sbom, Version, resolve};

fn temp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crag-pkg-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// Publishes a package whose manifest has the given imports, with one
/// module.
fn publish(registry: &Registry, name: &str, version: &str, imports: &str) {
    let dir = registry
        .dir
        .join(".staging")
        .join(format!("src-{name}-{version}"));
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("package.crag"),
        format!("package {name} {version}\nruntime 0.0\nexport {name}.main\n{imports}"),
    )
    .unwrap();
    fs::write(dir.join("src/main.crag"), "pub fn one() -> Int { 1 }\n").unwrap();
    registry
        .publish(name, &Version::parse(version).unwrap(), &dir)
        .unwrap();
    fs::remove_dir_all(&dir).unwrap();
}

fn app(imports: &str) -> Manifest {
    Manifest::parse(&format!(
        "package app 0.1\nruntime 0.0\nmain app.main\n{imports}"
    ))
    .unwrap()
}

fn versions(resolution: &crag_package::Resolution) -> Vec<String> {
    resolution
        .packages
        .iter()
        .map(|p| format!("{} {}", p.name, p.version))
        .collect()
}

#[test]
fn each_major_settles_on_the_highest_version_required() {
    let root = temp("highest");
    let team = Registry::create("team", &root.join("team")).unwrap();
    publish(&team, "geo", "1.1", "");
    publish(&team, "geo", "1.3", "import units 2.0\n");
    publish(&team, "geo", "1.4", "");
    publish(&team, "units", "2.0", "");
    publish(&team, "units", "2.1", "");
    publish(
        &team,
        "acme.maps",
        "1.0",
        "import geo 1.3\nimport dev testkit 1.0\n",
    );
    // The app asks for geo 1.1; acme.maps asks for 1.3, which wins and
    // brings units. 1.4 exists but nobody asks for it; testkit is a
    // development import of a dependency and does not count.
    let manifest = app("import geo 1.1\nimport acme.maps 1.0\n");
    let r = resolve(&manifest, &root, std::slice::from_ref(&team)).unwrap();
    assert_eq!(versions(&r), ["acme.maps 1.0", "geo 1.3", "units 2.0"]);
    assert_eq!(
        r.get("geo").unwrap().origin,
        Origin::Registry("team".into())
    );
    assert!(r.get("acme.maps").unwrap().dir.ends_with("acme/maps/1.0"));
    // The SBOM records each with its hash, and reads back.
    let sbom = Sbom::of(&manifest, &r);
    assert_eq!(Sbom::parse(&sbom.write()).unwrap(), sbom);
    assert!(sbom.write().contains(&format!(
        "package geo 1.3 hash \"{}\"",
        r.get("geo").unwrap().hash
    )));
    // Asking for units 2.1 moves only units.
    let manifest = app("import geo 1.1\nimport acme.maps 1.0\nimport units 2.1\n");
    let newer = Sbom::of(
        &manifest,
        &resolve(&manifest, &root, std::slice::from_ref(&team)).unwrap(),
    );
    assert_eq!(sbom.diff(&newer), ["~ units 2.0 -> 2.1"]);
    // Native libraries are recorded with their package.
    let manifest =
        app("import geo 1.1\nimport acme.maps 1.0\nnative m \"libm.so.6\", \"libm.so\"\n");
    let r = resolve(&manifest, &root, std::slice::from_ref(&team)).unwrap();
    let native = Sbom::of(&manifest, &r);
    assert!(
        native
            .write()
            .ends_with("native app m \"libm.so.6\", \"libm.so\"\n"),
        "{}",
        native.write()
    );
    assert_eq!(Sbom::parse(&native.write()).unwrap(), native);
    assert_eq!(sbom.diff(&native), ["+ native app m"]);
    let manifest = app("import geo 1.1\nimport acme.maps 1.0\nnative m \"libm.so.6\"\n");
    let other = Sbom::of(&manifest, &r);
    assert_eq!(native.diff(&other), ["~ native app m: other files"]);
    assert_eq!(other.diff(&sbom), ["- native app m"]);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn what_cannot_resolve_is_explained() {
    let root = temp("errors");
    let team = Registry::create("team", &root.join("team")).unwrap();
    let other = Registry::create("other", &root.join("other")).unwrap();
    publish(&team, "geo", "1.1", "");
    publish(&team, "geo", "2.0", "");
    publish(&team, "both", "1.0", "");
    publish(&other, "both", "1.0", "");
    publish(&team, "old", "1.0", "import geo 2.0\n");
    let registries = [team.clone(), other];
    let errors = |imports: &str| {
        resolve(&app(imports), &root, &registries)
            .unwrap_err()
            .join("\n")
    };
    assert!(
        errors("import geo 1.2\n")
            .contains("geo 1.2 is not in registry `team`, which has 1.1, 2.0")
    );
    assert!(errors("import nothing 1.0\n").contains("package nothing is in no registry"));
    assert!(errors("import both 1.0\n").contains("in several registries (team, other)"));
    assert!(errors("import geo 1.1\nimport old 1.0\n").contains("several majors of geo"));
    // A published version never changes; one that did is refused.
    fs::write(
        team.dir.join("geo/1.1/src/main.crag"),
        "pub fn two() -> Int { 2 }\n",
    )
    .unwrap();
    assert!(errors("import geo 1.1\n").contains("does not match its content hash"));
    assert!(
        team.publish("geo", &Version::parse("1.1").unwrap(), &root)
            .is_err()
    );
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn path_sources_settings_and_yanked_versions() {
    let root = temp("path");
    // A sibling project, named by a `path:` source.
    let billing = root.join("billing");
    fs::create_dir_all(&billing).unwrap();
    fs::write(
        billing.join("package.crag"),
        "package billing 1.2\nruntime 0.0\n",
    )
    .unwrap();
    fs::write(
        billing.join("invoice.crag"),
        "pub fn total() -> Int { 3 }\n",
    )
    .unwrap();
    let home = root.join("home");
    fs::create_dir_all(&home).unwrap();
    Registry::create("team", &home.join("team")).unwrap();
    fs::write(
        home.join("registries.crag"),
        "// Where packages come from.\nregistry team \"team\"\n",
    )
    .unwrap();
    let opened = registries(&home).unwrap();
    assert_eq!(opened[0].name, "team");
    publish(&opened[0], "geo", "1.0", "");
    fs::write(opened[0].dir.join("geo/1.0/yanked"), "wrong areas\n").unwrap();
    let app_dir = root.join("app");
    fs::create_dir_all(&app_dir).unwrap();
    let manifest = app("import billing 1.1 from \"path:../billing\"\nimport geo 1.0\n");
    let r = resolve(&manifest, &app_dir, &opened).unwrap();
    assert_eq!(versions(&r), ["billing 1.2", "geo 1.0"]);
    let billing_r = r.get("billing").unwrap();
    assert_eq!(billing_r.origin, Origin::Path("path:../billing".into()));
    assert_eq!(billing_r.layout, crag_package::content::Layout::Project);
    assert_eq!(r.get("geo").unwrap().yanked.as_deref(), Some("wrong areas"));
    assert!(
        Sbom::of(&manifest, &r)
            .write()
            .contains("package billing 1.2 path \"../billing\"\n")
    );
    // A folder too old for the requirement.
    let manifest = app("import billing 1.3 from \"path:../billing\"\n");
    let errors = resolve(&manifest, &app_dir, &opened)
        .unwrap_err()
        .join("\n");
    assert!(
        errors.contains("app requires billing 1.3, but path:../billing holds 1.2"),
        "{errors}"
    );
    assert!(Path::new(&home).join("team/.staging").is_dir());
    let _ = fs::remove_dir_all(&root);
}
