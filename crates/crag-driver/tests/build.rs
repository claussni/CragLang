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

//! `crag build` and `:build`: the project's tests, then its release
//! executable in `dist/`.

use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use crag_driver::{EvalOutput, Repl, Scratch};
use crag_session::ImageCommand;

/// How long a build of the runtime archive, and a build or run of a
/// project, may take.
const ARCHIVE_LIMIT: Duration = Duration::from_secs(600);
const LIMIT: Duration = Duration::from_secs(120);

const MANIFEST: &str = "package demo 0.1\nruntime 0.0\nmain demo.app\n";

const APP: &str = r#"import std.io

pub fn twice(n: Int) -> Int {
  n * 2
}

fn main() -> ExitCode {
  printLine("twice 21 is {twice(21)}")
  ExitCode(code: 4)
}
"#;

const PASSES: &str = r#"import std.test

import demo.app

test "doubles" { assertEqual(twice(2), 4) }
"#;

const FAILS: &str = r#"import std.test

import demo.app

test "doubles wrongly" { assertEqual(twice(2), 5) }
"#;

/// Builds the runtime archive `crag build` links with, once.
fn archive() {
    static BUILT: OnceLock<()> = OnceLock::new();
    BUILT.get_or_init(|| {
        let workspace = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let mut cargo = Command::new(env!("CARGO"));
        cargo
            .args(["build", "--quiet", "-p", "crag-rt", "--release"])
            .args(["--target", "x86_64-unknown-linux-musl"])
            .current_dir(workspace);
        let out = run(cargo, ARCHIVE_LIMIT);
        assert!(
            out.status.success(),
            "{}",
            String::from_utf8_lossy(&out.stderr)
        );
    });
}

/// Runs a command to its end within `limit`, killing it after.
fn run(mut command: Command, limit: Duration) -> Output {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    let pipe = |mut r: Box<dyn Read + Send>| {
        std::thread::spawn(move || {
            let mut bytes = Vec::new();
            let _ = r.read_to_end(&mut bytes);
            bytes
        })
    };
    let stdout = pipe(Box::new(child.stdout.take().unwrap()));
    let stderr = pipe(Box::new(child.stderr.take().unwrap()));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().unwrap() {
            break status;
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            panic!("{command:?} ran longer than {limit:?}");
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    Output {
        status,
        stdout: stdout.join().unwrap(),
        stderr: stderr.join().unwrap(),
    }
}

/// A fresh project with the app and the test module.
fn project(name: &str, test: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-build-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("test")).unwrap();
    fs::write(root.join("package.crag"), MANIFEST).unwrap();
    fs::write(root.join("app.crag"), APP).unwrap();
    fs::write(root.join("test/app_test.crag"), test).unwrap();
    root
}

/// `crag build` with the arguments in the project.
fn crag_build(root: &Path, args: &[&str]) -> Output {
    archive();
    let mut crag = Command::new(env!("CARGO_BIN_EXE_crag"));
    crag.arg("build").args(args).current_dir(root);
    run(crag, LIMIT)
}

#[test]
fn build_tests_the_project_and_writes_its_executable() {
    let root = project("passes", PASSES);
    let out = crag_build(&root, &[]);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert!(out.status.success(), "{text}");
    assert!(text.contains("\"doubles\" ... ok"), "{text}");
    assert!(text.ends_with("built dist/demo\n"), "{text}");
    let exe = run(Command::new(root.join("dist/demo")), LIMIT);
    let _ = fs::remove_dir_all(&root);
    assert_eq!(String::from_utf8_lossy(&exe.stdout), "twice 21 is 42\n");
    assert_eq!(exe.status.code(), Some(4));
}

#[test]
fn a_failing_test_builds_nothing_unless_tests_are_skipped() {
    let root = project("fails", FAILS);
    let out = crag_build(&root, &[]);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    assert_eq!(out.status.code(), Some(1), "{text}");
    assert!(text.contains("\"doubles wrongly\" ... FAILED"), "{text}");
    assert!(text.contains("nothing was built"), "{text}");
    assert!(!root.join("dist/demo").exists());
    let out = crag_build(&root, &["--skip-tests"]);
    let text = String::from_utf8_lossy(&out.stdout).into_owned();
    let built = root.join("dist/demo").is_file();
    let _ = fs::remove_dir_all(&root);
    assert!(out.status.success(), "{text}");
    assert_eq!(text, "built dist/demo\n");
    assert!(built);
}

#[test]
fn build_refuses_what_it_does_not_take() {
    let root = project("args", PASSES);
    let out = crag_build(&root, &["--release"]);
    let _ = fs::remove_dir_all(&root);
    assert_eq!(out.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&out.stderr).contains("unknown option `--release`"));
}

#[test]
fn the_repl_builds_as_the_shell_does() {
    archive();
    let root = project("repl", FAILS);
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    let mut repl = Repl::new(crag_driver::project::Project::load(&root).unwrap(), scratch);
    let refused = repl.run_command("build");
    let built = repl.run_command("build skip-tests");
    let exists = root.join("dist/demo").is_file();
    let _ = fs::remove_dir_all(&root);
    assert!(matches!(refused, Err(ref text) if text.contains("nothing was built")));
    assert!(matches!(built, Ok(EvalOutput::Text(ref text)) if text == "built dist/demo\n"));
    assert!(exists);
}
