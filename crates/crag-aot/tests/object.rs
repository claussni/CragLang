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

//! Release code written into an object file, read back as it was written,
//! and the same for the same sources.

use std::collections::HashMap;
use std::fs;

use crag_abi::{CodeObject, FuncId, RelocTarget};
use crag_aot::{MAIN, emit_object, read_object, read_table};
use crag_backend::{code, func_id};
use crag_driver::{Project, main_instance};
use crag_mir::Tier;

const APP: &str = r#"type Point(x: Int, y: Int)

let corner = Point(x: 3, y: 4)

fn greet(name: Str) -> Str {
  "Hello there, {name}, from a literal long enough to have a buffer"
}

fn area(p: Point) -> Int {
  p.x * p.y
}

fn total(ps: List[Point]) -> Int {
  var t = 0
  for p in ps {
    t = t + area(p)
  }
  t
}

fn twice(f: (Int) -> Int, x: Int) -> Int {
  f(f(x))
}

fn main() -> () {
  let n = total([corner, Point(x: 1, y: 2)]) + twice({ k -> k + area(corner) }, 1)
  let text = greet("Ada")
}
"#;

/// A project of one module, `demo.app`, loaded from a directory that is
/// gone again.
fn project(name: &str) -> Project {
    let root = std::env::temp_dir().join(format!("crag-aot-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(&root).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    fs::write(root.join("app.crag"), APP).unwrap();
    let project = Project::load(&root).unwrap();
    let _ = fs::remove_dir_all(&root);
    project
}

fn emit(project: &Project) -> crag_aot::Emitted<'_> {
    let main = main_instance(project).unwrap();
    emit_object(&project.db, project.program, &[(main, MAIN)]).unwrap()
}

#[test]
fn release_code_reads_back_as_it_was_written() {
    let p = project("read");
    let (db, program) = (&p.db, p.program);
    let emitted = emit(&p);
    let read = read_object(&emitted.bytes).unwrap();
    assert_eq!(read.len(), emitted.instances.len());
    let places: HashMap<FuncId, FuncId> = emitted
        .instances
        .iter()
        .enumerate()
        .map(|(n, &key)| (func_id(key), FuncId(n as u32)))
        .collect();
    let (mut cells, mut locals, mut runtime) = (0, 0, 0);
    for (function, &key) in read.iter().zip(&emitted.instances) {
        let compiled = code(db, program, key, Tier::Release)
            .as_ref()
            .unwrap()
            .as_ref()
            .unwrap();
        // As written: functions by their places, and a local relocation's
        // addend in its offset.
        let mut expected: CodeObject = compiled.object.clone();
        for reloc in &mut expected.relocs {
            match &mut reloc.target {
                RelocTarget::Function(f) => *f = places[f],
                RelocTarget::Cell(k) => {
                    k.func = places[&k.func];
                    cells += 1;
                }
                RelocTarget::Local(offset) => {
                    *offset = (i64::from(*offset) + reloc.addend) as u32;
                    reloc.addend = 0;
                    locals += 1;
                }
                RelocTarget::Runtime(_) => runtime += 1,
                other => panic!("release code holds {other:?}"),
            }
        }
        for call in &mut expected.inlined {
            for f in &mut call.frames {
                *f = places[f];
            }
        }
        expected.relocs.sort_by_key(|r| r.offset);
        assert_eq!(function.object, expected, "{}", function.name);
    }
    // The program has cells, static data and calls of the runtime.
    assert!(cells > 0 && locals > 0 && runtime > 0);
    assert!(read.iter().any(|f| f.name == "main"));
    // The table holds the types the code uses and the root.
    let table = read_table(&emitted.bytes).unwrap();
    assert!(!table.types.is_empty());
    assert_eq!(table.roots.len(), 1);
    assert_eq!(table.roots[0].name, MAIN);
    assert_eq!(table.functions[table.roots[0].place as usize].name, "main");
}

#[test]
fn the_same_sources_give_the_same_bytes() {
    let (one, two) = (project("same-1"), project("same-2"));
    let bytes = emit(&one).bytes;
    assert_eq!(bytes, emit(&two).bytes);
    // No build path is in the object.
    let root = std::env::temp_dir();
    let root = root.to_string_lossy();
    assert!(!bytes.windows(root.len()).any(|w| w == root.as_bytes()));
}
