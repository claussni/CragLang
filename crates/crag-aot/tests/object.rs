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

use crag_abi::release::Table;
use crag_abi::{CodeObject, FuncId, Reloc, RelocKind, RelocTarget, RuntimeFn, SlotKey};
use crag_aot::{CODE_SECTION, MAIN, emit_object};
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

/// A function read back from an object file crag-aot wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ReadFunction {
    name: String,
    /// Its code object, naming functions by their places.
    object: CodeObject,
}

/// Reads the table back from an object file crag-aot wrote, its
/// addresses offsets in `.text`.
fn read_table(bytes: &[u8]) -> Result<Table, String> {
    use object::read::{Object as _, ObjectSection as _};
    let file = object::File::parse(bytes).map_err(|e| e.to_string())?;
    let section = file
        .section_by_name(CODE_SECTION)
        .ok_or_else(|| format!("no {CODE_SECTION} section"))?;
    let mut table = section.data().map_err(|e| e.to_string())?.to_vec();
    // The addresses are written by relocations.
    for (offset, reloc) in section.relocations() {
        let at = offset as usize;
        table
            .get_mut(at..at + 8)
            .ok_or("a relocation outside the table")?
            .copy_from_slice(&(reloc.addend() as u64).to_le_bytes());
    }
    Table::decode(&table)
}

/// Reads the functions back from an object file crag-aot wrote, in
/// their places: the code objects as they were written, but that a local
/// relocation's addend is part of its offset.
fn read_object(bytes: &[u8]) -> Result<Vec<ReadFunction>, String> {
    use object::read::{Object as _, ObjectSection as _, ObjectSymbol as _, RelocationTarget};
    let file = object::File::parse(bytes).map_err(|e| e.to_string())?;
    let text = file.section_by_name(".text").ok_or("no .text section")?;
    let code = text.data().map_err(|e| e.to_string())?;
    let table = read_table(bytes)?;
    let mut functions = Vec::with_capacity(table.functions.len());
    let mut ranges = Vec::with_capacity(table.functions.len());
    for f in table.functions {
        let (start, end) = (f.start, f.start + u64::from(f.len));
        let mut object = f.object;
        object.code = code
            .get(start as usize..end as usize)
            .ok_or("code outside .text")?
            .to_vec();
        ranges.push((start, end));
        functions.push(ReadFunction {
            name: f.name,
            object,
        });
    }
    let symbol_place = |index| -> Result<ReadTarget, String> {
        let symbol = file.symbol_by_index(index).map_err(|e| e.to_string())?;
        let name = symbol.name().map_err(|e| e.to_string())?;
        if symbol.kind() == object::SymbolKind::Section {
            return Ok(ReadTarget::Text);
        }
        if let Some(rest) = name.strip_prefix("crag.cell.") {
            let (func, signature) = rest.split_once('.').ok_or("a cell without its key")?;
            let parse = |s: &str| s.parse::<u32>().map_err(|e| e.to_string());
            return Ok(ReadTarget::Exact(RelocTarget::Cell(SlotKey {
                func: FuncId(parse(func)?),
                signature: parse(signature)?,
            })));
        }
        if let Some(rest) = name.strip_prefix("crag.")
            && rest.starts_with(|c: char| c.is_ascii_digit())
        {
            let n = rest.split('.').next().unwrap_or_default();
            let n = n.parse::<u32>().map_err(|e| e.to_string())?;
            return Ok(ReadTarget::Exact(RelocTarget::Function(FuncId(n))));
        }
        RuntimeFn::ALL
            .iter()
            .find(|f| f.symbol() == name)
            .map(|&f| ReadTarget::Exact(RelocTarget::Runtime(f)))
            .ok_or_else(|| format!("a relocation of the unknown symbol {name}"))
    };
    let mut relocs: Vec<(u64, object::read::Relocation)> = text.relocations().collect();
    relocs.sort_by_key(|&(offset, _)| offset);
    for (offset, reloc) in relocs {
        // The stubs come after the functions.
        let Some(n) = ranges
            .iter()
            .position(|&(start, end)| (start..end).contains(&offset))
        else {
            continue;
        };
        let start = ranges[n].0;
        let RelocationTarget::Symbol(index) = reloc.target() else {
            return Err("a relocation without its symbol".into());
        };
        let (target, addend) = match symbol_place(index)? {
            ReadTarget::Exact(target) => (target, reloc.addend()),
            // A place in the function's own code, its addend included.
            ReadTarget::Text => {
                let at = u32::try_from(reloc.addend() - start as i64)
                    .map_err(|_| "a local relocation outside its function")?;
                (RelocTarget::Local(at), 0)
            }
        };
        functions[n].object.relocs.push(Reloc {
            offset: (offset - start) as u32,
            kind: RelocKind::Abs64,
            target,
            addend,
        });
    }
    Ok(functions)
}

/// Where a relocation read back points.
enum ReadTarget {
    Exact(RelocTarget),
    /// Into `.text`, by the addend.
    Text,
}
