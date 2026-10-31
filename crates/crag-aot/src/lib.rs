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

//! The AOT object writer (Implementation Plan §11.10.3): a release build's
//! code in one ELF object file, which the linker combines with the runtime
//! archive into an executable (§11.10.4, §11.10.5).
//!
//! The code is the release tier's (`Tier::Release`): optimized, without
//! steps, and with direct calls instead of slots, so the object carries
//! no reload tables and no debugger hooks (Specification §20.7). Each
//! function is a local symbol named by its place in the order the roots
//! reach it, `crag.<n>.<name>`, which keeps the names deterministic; a root
//! also gets the global symbol its caller names. Calls of the runtime name
//! its functions by the symbols `crag_abi::RuntimeFn::symbol` gives, which
//! the runtime archive defines. The cells of module-level values are
//! zeroed data, empty until their code first computes them.
//!
//! What the runtime needs of the code is a table in the section
//! `.crag_code`, at the global symbol `crag_code` (`crag_abi::release`):
//! each function's start, length, name and code object without code and
//! relocations, which holds its stack maps, handlers and the origins of
//! its traps (§11.6.3); the descriptors of the types the code uses; the
//! entry stubs tasks start in; and each root with the stub it starts in
//! and the shapes of its result. Function ids in it are the functions'
//! places, as in the symbol names.
//!
//! Not built yet: static data stays with the code of the function that
//! uses it, rather than in the one blob of static strings §20.7 asks for,
//! since a static string's buffer carries its header in front of its bytes;
//! cells are not filled with the values the compiler computed; and calls of
//! C functions, whose libraries the runtime opens at start, are refused.

mod link;

use std::collections::HashMap;

use crag_abi::release::{self, Table};
use crag_abi::{
    CELL_SIZE, CodeObject, FuncId, Reloc, RelocKind, RelocTarget, RuntimeFn, Shapes, SlotKey,
    TypeDescriptor,
};
use crag_backend::{code, func_id, shapes};
use crag_codegen::{CodegenSettings, OptLevel, compile_entry_stub, target_for};
use crag_db::Db;
use crag_hir::{Owner, Program};
use crag_mir::{InstanceKey, Tier, collect_instances, mir};
use object::write::{Object, Relocation, StandardSection, Symbol, SymbolId, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, RelocationFlags, SectionKind, SymbolFlags, SymbolKind,
    SymbolScope, elf,
};

pub use link::{LinkError, Target, Toolchain, link, link_with, runtime_archive};

/// The section that holds the table the runtime starts from.
pub const CODE_SECTION: &str = release::SECTION;

/// The root a release executable starts at, which the runtime archive's
/// `main` runs.
pub const MAIN: &str = "crag_main";

/// A program's release code in an object file.
pub struct Emitted<'db> {
    /// The bytes of the ELF object file.
    pub bytes: Vec<u8>,
    /// The functions in it, each at its place: the `n` of its symbol and
    /// its id in `CODE_SECTION`.
    pub instances: Vec<InstanceKey<'db>>,
}

/// Compiles what the roots reach in the release tier into an x86-64 ELF
/// object file. Each root gets a global symbol of its name and an entry
/// stub; the runtime archive starts the root `MAIN`. The program is one
/// without errors, which its caller checked as `crag run` does: code with
/// errors compiles to traps. Fails for code Cranelift rejects, for what
/// release builds cannot hold yet, and for a name given twice.
pub fn emit_object<'db>(
    db: &'db dyn Db,
    program: Program,
    roots: &[(InstanceKey<'db>, &str)],
) -> Result<Emitted<'db>, String> {
    let keys: Vec<InstanceKey<'db>> = roots.iter().map(|&(key, _)| key).collect();
    let instances = collect_instances(db, program, &keys, Tier::Release);
    let places: HashMap<FuncId, u32> = instances
        .iter()
        .enumerate()
        .map(|(n, &key)| (func_id(key), n as u32))
        .collect();
    let place = |func: FuncId| {
        places
            .get(&func)
            .map(|&n| FuncId(n))
            .ok_or_else(|| format!("function {} is not part of the program", func.0))
    };
    let mut objects = Vec::with_capacity(instances.len());
    let mut types: Vec<(u32, TypeDescriptor)> = Vec::new();
    let mut words = HashMap::new();
    for &key in &instances {
        let name = instance_name(db, key);
        let code = match code(db, program, key, Tier::Release) {
            Some(Ok(code)) => code,
            Some(Err(why)) => return Err(format!("cannot compile {name}: {why}")),
            None => return Err(format!("{name} has no code")),
        };
        if let Some(what) = code.unsupported.first() {
            return Err(format!("{name} uses {what}, which is not compiled yet"));
        }
        for t in &code.types {
            if !types.contains(t) {
                types.push(t.clone());
            }
        }
        words.insert(func_id(key), (code.params, code.returns));
        objects.push((name, renumber(&code.object, &place)?));
    }
    types.sort_by_key(|&(index, _)| index);
    let settings = stub_settings()?;
    let stub = |params, returns| {
        compile_entry_stub(params, returns, &settings).map_err(|e| format!("a stub: {e:?}"))
    };
    let mut entries = Vec::with_capacity(roots.len());
    for &(key, name) in roots {
        let (params, returns) = words[&func_id(key)];
        let result = mir(db, program, key, Tier::Release)
            .as_ref()
            .ok_or_else(|| format!("{name} has no body"))?
            .result;
        let (shapes, result) = shapes(db, program, result);
        entries.push(ObjectRoot {
            place: places[&func_id(key)],
            name,
            entry: stub(params, returns)?,
            shapes,
            result,
        });
    }
    let tasks = [stub(1, 0)?, stub(1, 1)?, stub(1, 2)?];
    let bytes = write_object(&objects, &entries, &tasks, &types)?;
    Ok(Emitted { bytes, instances })
}

/// The settings entry stubs are compiled with.
fn stub_settings() -> Result<CodegenSettings, String> {
    Ok(CodegenSettings {
        target: target_for("x86_64-unknown-linux-gnu").map_err(|e| e.to_string())?,
        opt: OptLevel::None,
        metered: false,
        profile: None,
    })
}

/// The name of an instance's owner, as symbols and traps show it.
fn instance_name(db: &dyn Db, key: InstanceKey) -> String {
    match key.owner(db) {
        Owner::Item(item) => item.name(db).text(db).clone(),
        Owner::Test(_) => "test".into(),
    }
}

/// The object with the functions it names by their places.
fn renumber(
    object: &CodeObject,
    place: &impl Fn(FuncId) -> Result<FuncId, String>,
) -> Result<CodeObject, String> {
    let mut object = object.clone();
    for reloc in &mut object.relocs {
        match &mut reloc.target {
            RelocTarget::Function(func) => *func = place(*func)?,
            RelocTarget::Cell(key) => key.func = place(key.func)?,
            RelocTarget::Slot(_) => return Err("release code calls through a slot".into()),
            RelocTarget::Native(_) | RelocTarget::NativeLibrary(_) => {
                return Err("C functions in release builds are not linked yet".into());
            }
            RelocTarget::Runtime(_) | RelocTarget::Local(_) => {}
        }
    }
    for call in &mut object.inlined {
        for func in &mut call.frames {
            *func = place(*func)?;
        }
    }
    Ok(object)
}

/// The symbol of a function at its place.
fn function_symbol(n: u32, name: &str) -> String {
    format!("crag.{n}.{name}")
}

/// The symbol of a value's cell.
fn cell_symbol(key: SlotKey) -> String {
    format!("crag.cell.{}.{}", key.func.0, key.signature)
}

/// A root of an object: the place of its function, the name of its
/// global symbol, the stub it starts in, and the shapes of its result.
pub struct ObjectRoot<'a> {
    pub place: u32,
    pub name: &'a str,
    pub entry: CodeObject,
    pub shapes: Shapes,
    pub result: u32,
}

/// Writes functions, each with the name of its owner and the functions it
/// names by their places, into an ELF object file, with a global symbol
/// for each root, the stubs tasks start in, for none, one and two result
/// words, and the descriptors of the types the code uses.
pub fn write_object(
    functions: &[(String, CodeObject)],
    roots: &[ObjectRoot],
    tasks: &[CodeObject; 3],
    types: &[(u32, TypeDescriptor)],
) -> Result<Vec<u8>, String> {
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = obj.section_id(StandardSection::Text);
    let text_symbol = obj.section_symbol(text);
    let mut starts = Vec::with_capacity(functions.len());
    let mut symbols = Vec::with_capacity(functions.len());
    for (n, (name, object)) in functions.iter().enumerate() {
        let start = obj.append_section_data(text, &object.code, u64::from(object.align.max(1)));
        starts.push(start);
        symbols.push(obj.add_symbol(code_symbol(
            function_symbol(n as u32, name),
            start,
            object,
            SymbolScope::Compilation,
            text,
        )));
    }
    for root in roots {
        let (start, object) = functions
            .get(root.place as usize)
            .map(|(_, o)| (starts[root.place as usize], o))
            .ok_or_else(|| format!("no function {} for the root {}", root.place, root.name))?;
        if obj.symbol_id(root.name.as_bytes()).is_some() {
            return Err(format!("the name {} is given twice", root.name));
        }
        obj.add_symbol(code_symbol(
            root.name.into(),
            start,
            object,
            SymbolScope::Linkage,
            text,
        ));
    }
    // The stubs, after the functions.
    let mut stub = |name: String, object: &CodeObject| {
        let start = obj.append_section_data(text, &object.code, u64::from(object.align.max(1)));
        obj.add_symbol(code_symbol(
            name,
            start,
            object,
            SymbolScope::Compilation,
            text,
        ));
        start
    };
    let entries: Vec<u64> = roots
        .iter()
        .map(|root| stub(format!("crag.entry.{}", root.name), &root.entry))
        .collect();
    let task_starts: Vec<u64> = (0..3)
        .map(|k| stub(format!("crag.task.{k}"), &tasks[k]))
        .collect();
    let mut relocs = Relocator {
        text,
        text_symbol,
        functions: &symbols,
        runtime: HashMap::new(),
        cells: HashMap::new(),
    };
    for (n, (_, object)) in functions.iter().enumerate() {
        relocs.add(&mut obj, starts[n], object)?;
    }
    for (root, &start) in roots.iter().zip(&entries) {
        relocs.add(&mut obj, start, &root.entry)?;
    }
    for (task, &start) in tasks.iter().zip(&task_starts) {
        relocs.add(&mut obj, start, task)?;
    }
    let table = Table {
        task_entries: [0, 1, 2].map(|k| task_starts[k] + u64::from(tasks[k].entry)),
        functions: functions
            .iter()
            .zip(&starts)
            .map(|((name, object), &start)| release::Function {
                start,
                len: object.code.len() as u32,
                name: name.clone(),
                object: object.clone(),
            })
            .collect(),
        types: types.to_vec(),
        roots: roots
            .iter()
            .zip(&entries)
            .map(|(root, &entry)| release::Root {
                name: root.name.into(),
                place: root.place,
                entry: entry + u64::from(root.entry.entry),
                shapes: root.shapes.clone(),
                result: root.result,
            })
            .collect(),
    };
    write_table(&mut obj, text_symbol, &table)?;
    obj.write().map_err(|e| e.to_string())
}

/// The symbol of code at `start` in `.text`, from its entry.
fn code_symbol(
    name: String,
    start: u64,
    object: &CodeObject,
    scope: SymbolScope,
    text: object::write::SectionId,
) -> Symbol {
    Symbol {
        name: name.into_bytes(),
        value: start + u64::from(object.entry),
        size: object.code.len() as u64 - u64::from(object.entry),
        kind: SymbolKind::Text,
        scope,
        weak: false,
        section: SymbolSection::Section(text),
        flags: SymbolFlags::None,
    }
}

/// Writes the relocations of code in `.text`, with the symbols they need.
struct Relocator<'a> {
    text: object::write::SectionId,
    text_symbol: SymbolId,
    /// Each function's symbol, by its place.
    functions: &'a [SymbolId],
    runtime: HashMap<RuntimeFn, SymbolId>,
    cells: HashMap<SlotKey, SymbolId>,
}

impl Relocator<'_> {
    /// Writes the relocations of the code at `start`.
    fn add(&mut self, obj: &mut Object, start: u64, object: &CodeObject) -> Result<(), String> {
        for reloc in &object.relocs {
            let RelocKind::Abs64 = reloc.kind;
            let (symbol, addend) = match reloc.target {
                // A function's symbol is at its entry, which the
                // relocation names too.
                RelocTarget::Function(func) => match self.functions.get(func.0 as usize) {
                    Some(&symbol) => (symbol, reloc.addend),
                    None => return Err(format!("a call of the missing function {}", func.0)),
                },
                RelocTarget::Local(offset) => (
                    self.text_symbol,
                    start as i64 + i64::from(offset) + reloc.addend,
                ),
                RelocTarget::Runtime(func) => {
                    let symbol = *self.runtime.entry(func).or_insert_with(|| {
                        obj.add_symbol(Symbol {
                            name: func.symbol().as_bytes().to_vec(),
                            value: 0,
                            size: 0,
                            kind: SymbolKind::Text,
                            scope: SymbolScope::Dynamic,
                            weak: false,
                            section: SymbolSection::Undefined,
                            flags: SymbolFlags::None,
                        })
                    });
                    (symbol, reloc.addend)
                }
                RelocTarget::Cell(key) => {
                    let symbol = *self.cells.entry(key).or_insert_with(|| {
                        let bss = obj.section_id(StandardSection::UninitializedData);
                        let value = obj.append_section_bss(bss, CELL_SIZE as u64, 8);
                        obj.add_symbol(Symbol {
                            name: cell_symbol(key).into_bytes(),
                            value,
                            size: CELL_SIZE as u64,
                            kind: SymbolKind::Data,
                            scope: SymbolScope::Compilation,
                            weak: false,
                            section: SymbolSection::Section(bss),
                            flags: SymbolFlags::None,
                        })
                    });
                    (symbol, reloc.addend)
                }
                RelocTarget::Slot(_) | RelocTarget::Native(_) | RelocTarget::NativeLibrary(_) => {
                    return Err(format!("release code cannot hold {:?}", reloc.target));
                }
            };
            obj.add_relocation(
                self.text,
                Relocation {
                    offset: start + u64::from(reloc.offset),
                    symbol,
                    addend,
                    flags: ABS64,
                },
            )
            .map_err(|e| e.to_string())?;
        }
        Ok(())
    }
}

/// An absolute address, which executables without PIE hold as it is.
const ABS64: RelocationFlags = RelocationFlags::Elf {
    r_type: elf::R_X86_64_64,
};

/// Writes the table into `CODE_SECTION`, at the global symbol
/// `release::SYMBOL`, its addresses, which are offsets in `.text`, as
/// relocations.
fn write_table(obj: &mut Object, text_symbol: SymbolId, table: &Table) -> Result<(), String> {
    let section = obj.add_section(
        Vec::new(),
        CODE_SECTION.as_bytes().to_vec(),
        SectionKind::ReadOnlyData,
    );
    let (mut bytes, addresses) = table.encode();
    let mut values = Vec::with_capacity(addresses.len());
    for &at in &addresses {
        let word: [u8; 8] = bytes[at..at + 8].try_into().expect("eight bytes");
        values.push((at, u64::from_le_bytes(word)));
        bytes[at..at + 8].fill(0);
    }
    let base = obj.append_section_data(section, &bytes, 8);
    obj.add_symbol(Symbol {
        name: release::SYMBOL.as_bytes().to_vec(),
        value: base,
        size: bytes.len() as u64,
        kind: SymbolKind::Data,
        scope: SymbolScope::Linkage,
        weak: false,
        section: SymbolSection::Section(section),
        flags: SymbolFlags::None,
    });
    for (at, value) in values {
        obj.add_relocation(
            section,
            Relocation {
                offset: base + at as u64,
                symbol: text_symbol,
                addend: value as i64,
                flags: ABS64,
            },
        )
        .map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// A function read back from an object file `write_object` wrote.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReadFunction {
    pub name: String,
    /// Its code object, naming functions by their places.
    pub object: CodeObject,
}

/// Reads the table back from an object file `write_object` wrote, its
/// addresses offsets in `.text`.
pub fn read_table(bytes: &[u8]) -> Result<Table, String> {
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

/// Reads the functions back from an object file `write_object` wrote, in
/// their places: the code objects as they were written, but that a local
/// relocation's addend is part of its offset.
pub fn read_object(bytes: &[u8]) -> Result<Vec<ReadFunction>, String> {
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
