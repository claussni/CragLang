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

//! Packages from folder registries, through the `crag` command
//! (Specification §14.5, §20.4, §20.6). Each test has a settings directory
//! of its own, named by `CRAG_HOME`.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::Once;
use std::time::Duration;

use crag_package::{Registry, Version};

fn watchdog() {
    static START: Once = Once::new();
    START.call_once(|| {
        std::thread::spawn(|| {
            std::thread::sleep(Duration::from_secs(120));
            eprintln!("the package tests hung");
            std::process::abort();
        });
    });
}

fn temp(name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("crag-packages-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

/// A settings directory with the registry `team`.
fn home(root: &Path) -> (PathBuf, Registry) {
    let home = root.join("home");
    fs::create_dir_all(&home).unwrap();
    fs::write(home.join("registries.crag"), "registry team \"team\"\n").unwrap();
    let registry = Registry::create("team", &home.join("team")).unwrap();
    (home, registry)
}

/// Publishes a package with the given manifest lines and modules.
fn publish(registry: &Registry, name: &str, version: &str, lines: &str, modules: &[(&str, &str)]) {
    let dir = registry.dir.join(format!("source-{name}-{version}"));
    fs::create_dir_all(dir.join("src")).unwrap();
    fs::write(
        dir.join("package.crag"),
        format!("package {name} {version}\nruntime 0.0\n{lines}"),
    )
    .unwrap();
    for (file, text) in modules {
        fs::write(dir.join("src").join(file), text).unwrap();
    }
    registry
        .publish(name, &Version::parse(version).unwrap(), &dir)
        .unwrap();
    fs::remove_dir_all(&dir).unwrap();
}

fn crag(home: &Path, dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(args)
        .current_dir(dir)
        .env("CRAG_HOME", home)
        .output()
        .unwrap()
}

fn text(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

const SHAPE: &str = "pub fn area(w: Int, h: Int) -> Int { w * h }\n";
const INTERNAL: &str = "pub fn secret() -> Int { 42 }\n";

#[test]
fn a_project_adds_uses_and_upgrades_a_package() {
    watchdog();
    let root = temp("use");
    let (home, team) = home(&root);
    let geo = "export geo.shape\n";
    publish(
        &team,
        "geo",
        "1.0",
        geo,
        &[("shape.crag", SHAPE), ("internal.crag", INTERNAL)],
    );
    publish(
        &team,
        "geo",
        "1.1",
        geo,
        &[("shape.crag", SHAPE), ("internal.crag", INTERNAL)],
    );
    publish(&team, "geo", "2.0", geo, &[("shape.crag", SHAPE)]);

    let out = crag(&home, &root, &["new", "app"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let app = root.join("app");
    assert!(app.join("main.crag").is_file() && app.join("test/main_test.crag").is_file());
    // Bare, a command that changes the project only explains itself.
    let out = crag(&home, &app, &["add"]);
    assert_eq!(out.status.code(), Some(2));
    assert!(text(&out).contains("usage: crag add <package> [version]"));

    // Without a version, the newest; the SBOM follows.
    let out = crag(&home, &app, &["add", "geo"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    assert!(
        text(&out).contains("sbom.crag: + geo 2.0") && text(&out).contains("added geo 2.0"),
        "{}",
        text(&out)
    );
    let out = crag(&home, &app, &["upgrade", "geo", "--version=1.0"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    assert!(
        text(&out).contains("sbom.crag: ~ geo 2.0 -> 1.0"),
        "{}",
        text(&out)
    );
    let manifest = fs::read_to_string(app.join("package.crag")).unwrap();
    assert!(
        manifest.ends_with("main app.main\nimport geo 1.0\n"),
        "{manifest}"
    );

    fs::write(
        app.join("main.crag"),
        "import geo.shape\n\nfn main() -> ExitCode {\n  ExitCode(code: area(2, 3))\n}\n",
    )
    .unwrap();
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(6), "{}", text(&out));

    // What geo does not export stays hidden.
    fs::write(
        app.join("main.crag"),
        "import geo.internal\n\nfn main() -> ExitCode {\n  ExitCode(code: secret())\n}\n",
    )
    .unwrap();
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("package geo does not export `geo.internal`"),
        "{}",
        text(&out)
    );
    fs::write(
        app.join("main.crag"),
        "import geo.shape\n\nfn main() -> ExitCode {\n  ExitCode(code: area(2, 3))\n}\n",
    )
    .unwrap();

    // Code still imports geo.
    let out = crag(&home, &app, &["remove", "geo"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("geo is still imported by main.crag"),
        "{}",
        text(&out)
    );

    let out = crag(&home, &app, &["outdated"]);
    assert!(
        text(&out).contains("geo 1.0: 1.1 available, new major 2.0"),
        "{}",
        text(&out)
    );
    let out = crag(&home, &app, &["upgrade", "geo"]);
    assert!(
        text(&out).contains("upgraded geo 1.0 -> 1.1"),
        "{}",
        text(&out)
    );
    let out = crag(&home, &app, &["deps"]);
    assert_eq!(text(&out), "app\n  geo 1.1\n");

    // A manifest edited by hand no longer matches the SBOM, until it is
    // regenerated on purpose.
    let manifest = fs::read_to_string(app.join("package.crag")).unwrap();
    fs::write(
        app.join("package.crag"),
        manifest.replace("geo 1.1", "geo 1.0"),
    )
    .unwrap();
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("sbom.crag does not match") && text(&out).contains("~ geo 1.1 -> 1.0"),
        "{}",
        text(&out)
    );
    let out = crag(&home, &app, &["sbom", "diff"]);
    assert_eq!(text(&out), "~ geo 1.1 -> 1.0\n");
    let out = crag(&home, &app, &["sbom", "regenerate"]);
    assert_eq!(text(&out), "sbom.crag: ~ geo 1.1 -> 1.0\n");
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(6), "{}", text(&out));

    // A published version that changed is refused.
    fs::write(team.dir.join("geo/1.0/src/shape.crag"), INTERNAL).unwrap();
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("does not match its content hash"),
        "{}",
        text(&out)
    );
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn development_imports_are_for_tests_and_yanked_versions_are_refused() {
    watchdog();
    let root = temp("dev");
    let (home, team) = home(&root);
    publish(
        &team,
        "testkit",
        "1.0",
        "export testkit.check\n",
        &[(
            "check.crag",
            "pub fn same(a: Int, b: Int) -> Bool { a == b }\n",
        )],
    );
    publish(
        &team,
        "geo",
        "1.0",
        "export geo.shape\n",
        &[("shape.crag", SHAPE)],
    );
    fs::write(team.dir.join("geo/1.0/yanked"), "wrong areas").unwrap();
    crag(&home, &root, &["new", "app"]);
    let app = root.join("app");
    let manifest = fs::read_to_string(app.join("package.crag")).unwrap();
    fs::write(
        app.join("package.crag"),
        format!("{manifest}import dev testkit 1.0\n"),
    )
    .unwrap();
    let out = crag(&home, &app, &["sbom", "regenerate"]);
    assert_eq!(text(&out), "sbom.crag: + testkit 1.0\n");
    fs::write(
        app.join("test/main_test.crag"),
        "import testkit.check\n\ntest \"one is one\" {\n  same(1, 1)\n}\n",
    )
    .unwrap();
    let out = crag(&home, &app, &["test"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    fs::write(
        app.join("main.crag"),
        "import testkit.check\n\nfn main() {\n}\n",
    )
    .unwrap();
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("testkit is a development import of app; only test and tool modules"),
        "{}",
        text(&out)
    );
    // A yanked version is not taken anew.
    let out = crag(&home, &app, &["add", "geo", "1.0"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("geo 1.0 was yanked (wrong areas); choose another version"),
        "{}",
        text(&out)
    );
    assert!(
        !fs::read_to_string(app.join("package.crag"))
            .unwrap()
            .contains("geo")
    );
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn new_projects_build_run_and_test() {
    watchdog();
    let root = temp("new");
    let (home, _) = home(&root);
    for (name, args) in [
        ("app", &["new", "app"][..]),
        ("lib", &["new", "lib", "--lib"][..]),
    ] {
        let out = crag(&home, &root, args);
        assert_eq!(out.status.code(), Some(0), "{}", text(&out));
        let dir = root.join(name);
        let out = crag(&home, &dir, &["test"]);
        assert_eq!(out.status.code(), Some(0), "{name}: {}", text(&out));
        assert!(text(&out).contains("... ok"), "{name}: {}", text(&out));
    }
    let out = crag(&home, &root.join("app"), &["run"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let out = crag(&home, &root, &["new", "app"]);
    assert_eq!(out.status.code(), Some(1));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn a_library_is_checked_published_and_used() {
    watchdog();
    let root = temp("publish");
    let (home, team) = home(&root);
    crag(&home, &root, &["new", "geo", "--lib"]);
    let geo = root.join("geo");
    // An embed source travels with the package, into res/.
    fs::create_dir_all(geo.join("data")).unwrap();
    fs::write(geo.join("data/unit.txt"), "metre").unwrap();
    fs::write(
        geo.join("greeting.crag"),
        "pub fn greeting() -> Str { \"Hello\" }\n\nembed unit: Str from \"data/unit.txt\"\n\npub fn unitName() -> Str { unit }\n\npub fn area(w: Int, h: Int) -> Int { w * h }\n",
    )
    .unwrap();
    let out = crag(&home, &geo, &["publish"]);
    assert_eq!(out.status.code(), Some(2));
    let out = crag(&home, &geo, &["publish", "elsewhere"]);
    assert!(
        text(&out).contains("no registry is named `elsewhere`; the settings name team"),
        "{}",
        text(&out)
    );
    let out = crag(&home, &geo, &["publish", "team"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    assert!(
        text(&out).contains("published geo 0.1 to team"),
        "{}",
        text(&out)
    );
    let published = team.dir.join("geo/0.1");
    for file in [
        "package.crag",
        "api.crag",
        "content.hash",
        "src/greeting.crag",
        "res/data/unit.txt",
    ] {
        assert!(published.join(file).is_file(), "{file}");
    }
    assert!(
        !published.join("src/test").exists(),
        "tests are not shipped"
    );
    let api = fs::read_to_string(published.join("api.crag")).unwrap();
    assert!(
        api.contains("module geo.greeting\npub fn area(w: Int, h: Int) -> Int\npub fn greeting() -> Str\npub fn unitName() -> Str\n"),
        "{api}"
    );

    // An application uses it, embed and all.
    crag(&home, &root, &["new", "app"]);
    let app = root.join("app");
    let out = crag(&home, &app, &["add", "geo"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    fs::write(
        app.join("main.crag"),
        "import geo.greeting\n\nfn main() -> ExitCode {\n  let metre = if unitName() == \"metre\" { 5 } else { 0 }\n  ExitCode(code: area(2, 3) + metre)\n}\n",
    )
    .unwrap();
    let out = crag(&home, &app, &["run"]);
    assert_eq!(out.status.code(), Some(11), "{}", text(&out));

    // Removing a function needs a new major.
    let manifest = fs::read_to_string(geo.join("package.crag")).unwrap();
    fs::write(
        geo.join("package.crag"),
        manifest.replace("geo 0.1", "geo 0.2"),
    )
    .unwrap();
    fs::write(
        geo.join("greeting.crag"),
        "pub fn greeting() -> Str { \"Hello\" }\n\nembed unit: Str from \"data/unit.txt\"\n\npub fn unitName() -> Str { unit }\n",
    )
    .unwrap();
    let out = crag(&home, &geo, &["publish", "team"]);
    assert_eq!(out.status.code(), Some(1));
    assert!(
        text(&out).contains("from 0.1, the API changed so that it needs a new major version:\n  removed or changed in geo.greeting: pub fn area(w: Int, h: Int) -> Int"),
        "{}",
        text(&out)
    );
    // A type hole is not published, nor is a failing test.
    fs::write(
        geo.join("package.crag"),
        manifest.replace("geo 0.1", "geo 1.0"),
    )
    .unwrap();
    fs::write(
        geo.join("greeting.crag"),
        "pub fn greeting() -> Str { ??? }\n",
    )
    .unwrap();
    let out = crag(&home, &geo, &["publish", "team"]);
    assert!(
        text(&out).contains("greeting.crag:1: a type hole `???` is not published"),
        "{}",
        text(&out)
    );
    fs::write(
        geo.join("greeting.crag"),
        "pub fn greeting() -> Str { \"Hello\" }\n",
    )
    .unwrap();
    fs::write(
        geo.join("test/greeting_test.crag"),
        "test \"fails\" {\n  let xs = [1]\n  let y = xs[3]\n}\n",
    )
    .unwrap();
    let out = crag(&home, &geo, &["publish", "team"]);
    assert!(
        text(&out).contains("the tests do not pass, so nothing is published"),
        "{}",
        text(&out)
    );
    fs::remove_file(geo.join("test/greeting_test.crag")).unwrap();
    let out = crag(&home, &geo, &["package"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    assert!(geo.join("target/package/geo-1.0/api.crag").is_file());
    let out = crag(&home, &geo, &["publish", "team"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let out = crag(&home, &app, &["outdated"]);
    assert!(
        text(&out).contains("geo 0.1: new major 1.0"),
        "{}",
        text(&out)
    );
    let _ = fs::remove_dir_all(&root);
}

/// The counts `CRAG_CACHE_STATS` prints: reused and compiled.
fn cache_stats(home: &Path, dir: &Path, args: &[&str], stdin: &str) -> (usize, usize, String) {
    use std::io::Write;
    let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
        .args(args)
        .current_dir(dir)
        .env("CRAG_HOME", home)
        .env("CRAG_CACHE_STATS", "1")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let all = text(&out);
    let line = all
        .lines()
        .find_map(|l| l.strip_prefix("cache: "))
        .unwrap_or_else(|| panic!("no cache line in {all}"))
        .to_string();
    let numbers: Vec<usize> = line
        .split(|c: char| !c.is_ascii_digit())
        .filter(|w| !w.is_empty())
        .map(|w| w.parse().unwrap())
        .collect();
    (numbers[0], numbers[1], all)
}

#[test]
fn compiled_code_is_kept_for_the_next_session_and_command() {
    watchdog();
    let root = temp("cache");
    let (home, _) = home(&root);
    crag(&home, &root, &["new", "app"]);
    let app = root.join("app");
    let main = "pub fn double(n: Int) -> Int { n * 2 }\n\nfn triple(n: Int) -> Int { n * 3 }\n\nfn main() -> ExitCode {\n  ExitCode(code: double(2) + triple(1))\n}\n\ntest \"doubles\" {\n  double(1)\n}\n";
    fs::write(app.join("main.crag"), main).unwrap();
    let (reused, compiled, out) = cache_stats(&home, &app, &["run"], "");
    assert!(reused == 0 && compiled > 0, "{out}");
    // A second run compiles nothing.
    let (again, none, out) = cache_stats(&home, &app, &["run"], "");
    assert_eq!((again, none), (compiled, 0), "{out}");
    // An edit compiles what it changed only.
    fs::write(app.join("main.crag"), main.replace("n * 3", "n * 4")).unwrap();
    let (reused, recompiled, out) = cache_stats(&home, &app, &["run"], "");
    assert!(
        reused > 0 && recompiled > 0 && recompiled < compiled,
        "{out}"
    );
    // The tests and a REPL session share it.
    let (reused, _, out) = cache_stats(&home, &app, &["test"], "");
    assert!(reused > 0, "{out}");
    let (_, compiled, out) = cache_stats(&home, &app, &[], "import app.main\ndouble(21)\n");
    assert!(out.contains("42"), "{out}");
    let (reused, recompiled, out) = cache_stats(&home, &app, &[], "import app.main\ndouble(21)\n");
    assert!(reused > 0 && recompiled < compiled.max(1), "{out}");
    // The project's roots are recorded, for garbage collection.
    let roots = fs::read_dir(home.join("cache/roots")).unwrap().count();
    assert_eq!(roots, 1);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_repl_adds_a_package_and_uses_it_at_once() {
    use std::io::Write;
    watchdog();
    let root = temp("repl");
    let (home, team) = home(&root);
    publish(
        &team,
        "geo",
        "1.0",
        "export geo.shape\n",
        &[("shape.crag", SHAPE)],
    );
    crag(&home, &root, &["new", "app"]);
    let app = root.join("app");
    let mut child = Command::new(env!("CARGO_BIN_EXE_crag"))
        .current_dir(&app)
        .env("CRAG_HOME", &home)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(
            b":add\n:add geo\nimport geo.shape\narea(6, 7)\n:deps\n:upgrade geo version: 3.0\n",
        )
        .unwrap();
    let out = child.wait_with_output().unwrap();
    let all = text(&out);
    assert!(all.contains("usage: crag add <package> [version]"), "{all}");
    assert!(all.contains("sbom.crag: + geo 1.0\nadded geo 1.0"), "{all}");
    assert!(all.contains("42"), "{all}");
    assert!(all.contains("app\n  geo 1.0\n"), "{all}");
    assert!(
        all.contains("geo 3.0 is not in registry `team`, which has 1.0"),
        "{all}"
    );
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn registries_are_made_added_listed_and_removed() {
    watchdog();
    let root = temp("registry");
    let home = root.join("home");
    let out = crag(&home, &root, &["registry", "list"]);
    assert!(text(&out).contains("no registries"), "{}", text(&out));

    let out = crag(&home, &root, &["registry", "new", "team", "shared"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let shared = root.join("shared").canonicalize().unwrap();
    assert!(Registry::open("team", &shared).is_ok());
    // A folder that holds something already is not made a registry.
    fs::create_dir_all(root.join("full")).unwrap();
    fs::write(root.join("full/file"), "").unwrap();
    let out = crag(&home, &root, &["registry", "new", "other", "full"]);
    assert_eq!(out.status.code(), Some(1), "{}", text(&out));
    let out = crag(&home, &root, &["registry", "new", "team", "elsewhere"]);
    assert!(text(&out).contains("already"), "{}", text(&out));
    assert!(!root.join("elsewhere").exists());
    // `add` takes a registry that exists, under a name of the user's own.
    let out = crag(&home, &root, &["registry", "add", "mine", "full"]);
    assert_eq!(out.status.code(), Some(1), "{}", text(&out));
    let out = crag(&home, &root, &["registry", "add", "mine", "shared"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));

    let out = crag(&home, &root, &["registry", "list"]);
    let listed = String::from_utf8_lossy(&out.stdout).into_owned();
    assert_eq!(
        listed,
        format!("team {0}\nmine {0}\n", shared.display()),
        "{}",
        text(&out)
    );

    // A library published to the new registry is found by another project.
    let out = crag(&home, &root, &["new", "geo", "--lib"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let out = crag(&home, &root.join("geo"), &["publish", "team"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let out = crag(&home, &root, &["registry", "remove", "mine"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let out = crag(&home, &root, &["new", "app"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));
    let out = crag(&home, &root.join("app"), &["add", "geo"]);
    assert_eq!(out.status.code(), Some(0), "{}", text(&out));

    let out = crag(&home, &root, &["registry", "remove", "mine"]);
    assert_eq!(out.status.code(), Some(1), "{}", text(&out));
    let out = crag(&home, &root, &["registry"]);
    assert_eq!(out.status.code(), Some(2), "{}", text(&out));
    fs::remove_dir_all(&root).unwrap();
}
