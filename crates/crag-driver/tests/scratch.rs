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

//! Code compiled on the host, shipped to the scratch image and run there.

use std::fs;
use std::path::PathBuf;

use crag_driver::{Project, Scratch};
use crag_hir::{ItemKind, Owner, item_tree};
use crag_mir::InstanceKey;
use crag_session::ImageCommand;

const APP: &str = r#"type Point(x: Int, y: Int)

fn two() -> Int {
  2
}

fn answer() -> Int {
  40 + two()
}

fn twice() -> Int {
  answer() + two()
}

fn area() -> Int {
  let p = Point(x: 3, y: 4)
  p.x * p.y
}

fn total() -> Int {
  sum([Point(x: 1, y: 2), Point(x: 3, y: 4)])
}

fn sum(ps: List[Point]) -> Int {
  var t = 0
  for p in ps {
    t = t + p.x * p.y
  }
  t
}

fn down(n: Int) -> Int {
  if n == 0 { 1 / n } else { down(n - 1) + 1 }
}

fn boom() -> Int {
  down(3)
}
"#;

/// A project of one module, `demo.app`, loaded.
fn project(name: &str, app: &str) -> Project {
    let root = std::env::temp_dir().join(format!("crag-scratch-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    fs::write(root.join("app.crag"), app).unwrap();
    let project = Project::load(&root).unwrap();
    let _ = fs::remove_dir_all(PathBuf::from(&root));
    project
}

/// The body of a function of `demo.app`.
fn function<'a>(project: &'a Project, name: &str) -> InstanceKey<'a> {
    let db = &project.db;
    let module = project.module("demo.app").unwrap();
    let item = item_tree(db, module)
        .items
        .iter()
        .map(|i| i.id)
        .find(|id| *id.kind(db) == ItemKind::Function && id.name(db).text(db) == name)
        .unwrap();
    InstanceKey::body(db, Owner::Item(item))
}

fn scratch() -> Scratch {
    Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap()
}

#[test]
fn shipped_code_runs_in_the_scratch_image() {
    let p = project("runs", APP);
    let mut s = scratch();
    // `answer` and `two`, then only `twice`.
    assert_eq!(s.ship(&p, &[function(&p, "answer")]).unwrap(), 2);
    assert_eq!(s.ship(&p, &[function(&p, "twice")]).unwrap(), 1);
    assert_eq!(s.ship(&p, &[function(&p, "twice")]).unwrap(), 0);
    assert_eq!(s.run(&p, function(&p, "answer")).unwrap(), Ok(vec![42]));
    assert_eq!(s.run(&p, function(&p, "twice")).unwrap(), Ok(vec![44]));
    // Records and lists need the descriptors of their types there.
    assert_eq!(s.run(&p, function(&p, "area")).unwrap(), Ok(vec![12]));
    assert_eq!(s.run(&p, function(&p, "total")).unwrap(), Ok(vec![14]));
}

#[test]
fn a_trap_in_the_image_is_reported_by_the_host() {
    let p = project("trap", APP);
    let mut s = scratch();
    assert_eq!(
        s.run(&p, function(&p, "boom")).unwrap(),
        // `boom` tail-calls `down`, so its frame is gone.
        Err("trap: division by zero\n  --> app.crag:33:15\n   |\n33 |   if n == 0 { 1 / n } else { down(n - 1) + 1 }\n   |               ^\n  in down, 4 frames\n".into())
    );
    // The image runs on.
    assert_eq!(s.run(&p, function(&p, "answer")).unwrap(), Ok(vec![42]));
}

#[test]
fn a_fresh_image_gets_the_code_again() {
    let p = project("fresh", APP);
    let mut s = scratch();
    assert_eq!(s.run(&p, function(&p, "answer")).unwrap(), Ok(vec![42]));
    let old = s.session().scratch().pid();
    s.session().restart().unwrap();
    assert_ne!(s.session().scratch().pid(), old);
    assert_eq!(s.ship(&p, &[function(&p, "answer")]).unwrap(), 2);
    assert_eq!(s.run(&p, function(&p, "answer")).unwrap(), Ok(vec![42]));
}

#[test]
fn changed_code_is_not_shipped_over_the_old() {
    let p = project("old", APP);
    let mut s = scratch();
    assert_eq!(s.run(&p, function(&p, "two")).unwrap(), Ok(vec![2]));
    // The same function in another database is another function, but its
    // id may be the same: that stands in for a definition that changed.
    let q = project("new", &APP.replace("  2\n", "  3\n"));
    let error = s.run(&q, function(&q, "two")).unwrap_err();
    assert!(
        error.ends_with("changed, and the image cannot replace its code yet"),
        "{error}"
    );
    assert_eq!(s.run(&p, function(&p, "two")).unwrap(), Ok(vec![2]));
}
