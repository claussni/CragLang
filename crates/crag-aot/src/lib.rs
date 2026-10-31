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
//! code in one ELF object file for the linker (§11.10.5).
//!
//! The code is the release tier's (`Tier::Release`): optimized, without
//! steps, and with direct calls instead of slots, so the object carries
//! no reload tables and no debugger hooks (Specification §20.7). Each
//! function is a local symbol named by its place in the order the roots
//! reach it, `crag.<n>.<name>`, which keeps the names deterministic; a root
//! also gets the global symbol its caller names. Calls of the runtime name
//! its functions by the symbols `crag_abi::RuntimeFn::symbol` gives, which
//! the runtime archive defines (§11.10.4). The cells of module-level values
//! are zeroed data, empty until their code first computes them.
//!
//! What traps and disposal need of each function stays in the section
//! `.crag_code`: where its code starts and ends, its name, and its code
//! object without code and relocations, as the image protocol encodes it,
//! which holds its stack maps, handlers and the origins of its traps
//! (§11.6.3). Function ids in it are the functions' places, as in the
//! symbol names.
//!
//! Not built yet: static data stays with the code of the function that
//! uses it, rather than in the one blob of static strings §20.7 asks for,
//! since a static string's buffer carries its header in front of its bytes;
//! cells are not filled with the values the compiler computed; and calls of
//! C functions, whose libraries the runtime opens at start, are refused.

use std::collections::HashMap;

use crag_abi::{CELL_SIZE, CodeObject, FuncId, Reloc, RelocKind, RelocTarget, RuntimeFn, SlotKey};
use crag_backend::{code, func_id};
use crag_db::Db;
use crag_hir::{Owner, Program};
use crag_mir::{InstanceKey, Tier, collect_instances};
use crag_session::protocol::{decode_object, encode_object};
use object::write::{Object, Relocation, StandardSection, Symbol, SymbolId, SymbolSection};
use object::{
    Architecture, BinaryFormat, Endianness, RelocationFlags, SectionKind, SymbolFlags, SymbolKind,
    SymbolScope, elf,
};

/// The section that holds what traps and disposal need of each function.
pub const CODE_SECTION: &str = ".crag_code";

/// The version of the layout of `CODE_SECTION`.
pub const CODE_VERSION: u32 = 1;

/// A program's release code in an object file.
pub struct Emitted<'db> {
    /// The bytes of the ELF object file.
    pub bytes: Vec<u8>,
    /// The functions in it, each at its place: the `n` of its symbol and
    /// its id in `CODE_SECTION`.
    pub instances: Vec<InstanceKey<'db>>,
}

/// Compiles what the roots reach in the release tier into an x86-64 ELF
/// object file. Each root gets a global symbol of its name. Fails for code
/// Cranelift rejects, for what release builds cannot hold yet, and for a
/// name given twice.
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
        objects.push((name, renumber(&code.object, &place)?));
    }
    let names: Vec<(u32, &str)> = roots
        .iter()
        .map(|&(key, name)| (places[&func_id(key)], name))
        .collect();
    let bytes = write_object(&objects, &names)?;
    Ok(Emitted { bytes, instances })
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

/// Writes functions, each with the name of its owner and the functions it
/// names by their places, into an ELF object file, with a global symbol
/// for each of `roots`, a place and a name.
pub fn write_object(
    functions: &[(String, CodeObject)],
    roots: &[(u32, &str)],
) -> Result<Vec<u8>, String> {
    let mut obj = Object::new(BinaryFormat::Elf, Architecture::X86_64, Endianness::Little);
    let text = obj.section_id(StandardSection::Text);
    let text_symbol = obj.section_symbol(text);
    let mut starts = Vec::with_capacity(functions.len());
    let mut symbols = Vec::with_capacity(functions.len());
    for (n, (name, object)) in functions.iter().enumerate() {
        let start = obj.append_section_data(text, &object.code, u64::from(object.align.max(1)));
        starts.push(start);
        symbols.push(obj.add_symbol(Symbol {
            name: function_symbol(n as u32, name).into_bytes(),
            value: start + u64::from(object.entry),
            size: object.code.len() as u64 - u64::from(object.entry),
            kind: SymbolKind::Text,
            scope: SymbolScope::Compilation,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        }));
    }
    for &(n, name) in roots {
        let (start, object) = functions
            .get(n as usize)
            .map(|(_, o)| (starts[n as usize], o))
            .ok_or_else(|| format!("no function {n} for the root {name}"))?;
        if obj.symbol_id(name.as_bytes()).is_some() {
            return Err(format!("the name {name} is given twice"));
        }
        obj.add_symbol(Symbol {
            name: name.as_bytes().to_vec(),
            value: start + u64::from(object.entry),
            size: object.code.len() as u64 - u64::from(object.entry),
            kind: SymbolKind::Text,
            scope: SymbolScope::Linkage,
            weak: false,
            section: SymbolSection::Section(text),
            flags: SymbolFlags::None,
        });
    }
    let bss = obj.section_id(StandardSection::UninitializedData);
    let mut runtime: HashMap<RuntimeFn, SymbolId> = HashMap::new();
    let mut cells: HashMap<SlotKey, SymbolId> = HashMap::new();
    let abs64 = RelocationFlags::Elf {
        r_type: elf::R_X86_64_64,
    };
    for (n, (_, object)) in functions.iter().enumerate() {
        let start = starts[n];
        for reloc in &object.relocs {
            let RelocKind::Abs64 = reloc.kind;
            let (symbol, addend) = match reloc.target {
                // A function's symbol is at its entry, which the
                // relocation names too.
                RelocTarget::Function(func) => match symbols.get(func.0 as usize) {
                    Some(&symbol) => (symbol, reloc.addend),
                    None => return Err(format!("a call of the missing function {}", func.0)),
                },
                RelocTarget::Local(offset) => {
                    (text_symbol, start as i64 + i64::from(offset) + reloc.addend)
                }
                RelocTarget::Runtime(func) => {
                    let symbol = *runtime.entry(func).or_insert_with(|| {
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
                    let symbol = match cells.get(&key) {
                        Some(&symbol) => symbol,
                        None => {
                            let value = obj.append_section_bss(bss, CELL_SIZE as u64, 8);
                            let symbol = obj.add_symbol(Symbol {
                                name: cell_symbol(key).into_bytes(),
                                value,
                                size: CELL_SIZE as u64,
                                kind: SymbolKind::Data,
                                scope: SymbolScope::Compilation,
                                weak: false,
                                section: SymbolSection::Section(bss),
                                flags: SymbolFlags::None,
                            });
                            cells.insert(key, symbol);
                            symbol
                        }
                    };
                    (symbol, reloc.addend)
                }
                RelocTarget::Slot(_) | RelocTarget::Native(_) | RelocTarget::NativeLibrary(_) => {
                    return Err(format!("release code cannot hold {:?}", reloc.target));
                }
            };
            obj.add_relocation(
                text,
                Relocation {
                    offset: start + u64::from(reloc.offset),
                    symbol,
                    addend,
                    flags: abs64,
                },
            )
            .map_err(|e| e.to_string())?;
        }
    }
    write_code_section(&mut obj, text_symbol, functions, &starts)?;
    obj.write().map_err(|e| e.to_string())
}

/// Writes `CODE_SECTION`: the version, the number of functions, and for
/// each its start, the length of its code, its name and its code object
/// without code and relocations, each of the last two after its length.
fn write_code_section(
    obj: &mut Object,
    text_symbol: SymbolId,
    functions: &[(String, CodeObject)],
    starts: &[u64],
) -> Result<(), String> {
    let section = obj.add_section(
        Vec::new(),
        CODE_SECTION.as_bytes().to_vec(),
        SectionKind::ReadOnlyData,
    );
    let mut bytes = Vec::new();
    bytes.extend(CODE_VERSION.to_le_bytes());
    bytes.extend((functions.len() as u32).to_le_bytes());
    let mut places = Vec::with_capacity(functions.len());
    for ((name, object), &start) in functions.iter().zip(starts) {
        places.push((bytes.len() as u64, start));
        bytes.extend(0u64.to_le_bytes());
        bytes.extend((object.code.len() as u32).to_le_bytes());
        bytes.extend((name.len() as u32).to_le_bytes());
        bytes.extend(name.as_bytes());
        let meta = encode_object(&CodeObject {
            code: Vec::new(),
            relocs: Vec::new(),
            ..object.clone()
        });
        bytes.extend((meta.len() as u32).to_le_bytes());
        bytes.extend(meta);
    }
    let base = obj.append_section_data(section, &bytes, 8);
    for (offset, start) in places {
        obj.add_relocation(
            section,
            Relocation {
                offset: base + offset,
                symbol: text_symbol,
                addend: start as i64,
                flags: RelocationFlags::Elf {
                    r_type: elf::R_X86_64_64,
                },
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

/// Reads the functions back from an object file `write_object` wrote, in
/// their places: the code objects as they were written, but that a local
/// relocation's addend is part of its offset.
pub fn read_object(bytes: &[u8]) -> Result<Vec<ReadFunction>, String> {
    use object::read::{Object as _, ObjectSection as _, ObjectSymbol as _, RelocationTarget};
    let file = object::File::parse(bytes).map_err(|e| e.to_string())?;
    let text = file.section_by_name(".text").ok_or("no .text section")?;
    let code = text.data().map_err(|e| e.to_string())?;
    let section = file
        .section_by_name(CODE_SECTION)
        .ok_or_else(|| format!("no {CODE_SECTION} section"))?;
    let meta = section.data().map_err(|e| e.to_string())?;
    // The starts are written by relocations.
    let mut starts: HashMap<u64, u64> = HashMap::new();
    for (offset, reloc) in section.relocations() {
        starts.insert(offset, reloc.addend() as u64);
    }
    let mut r = Bytes(meta);
    if r.u32()? != CODE_VERSION {
        return Err(format!("{CODE_SECTION} of another version"));
    }
    let count = r.u32()?;
    let mut functions = Vec::with_capacity(count as usize);
    let mut ranges = Vec::with_capacity(count as usize);
    for _ in 0..count {
        let at = (meta.len() - r.0.len()) as u64;
        r.take(8)?;
        let start = *starts.get(&at).ok_or("a function without its start")?;
        let len = u64::from(r.u32()?);
        let name_len = r.u32()? as usize;
        let name = String::from_utf8(r.take(name_len)?.to_vec()).map_err(|e| e.to_string())?;
        let meta_len = r.u32()? as usize;
        let mut object = decode_object(r.take(meta_len)?).map_err(|e| e.to_string())?;
        object.code = code
            .get(start as usize..(start + len) as usize)
            .ok_or("code outside .text")?
            .to_vec();
        ranges.push((start, start + len));
        functions.push(ReadFunction { name, object });
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
        if let Some(rest) = name.strip_prefix("crag.") {
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
        let n = ranges
            .iter()
            .position(|&(start, end)| (start..end).contains(&offset))
            .ok_or("a relocation outside every function")?;
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

/// Bytes read from the front.
struct Bytes<'a>(&'a [u8]);

impl<'a> Bytes<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        if self.0.len() < n {
            return Err(format!("{CODE_SECTION} ends early"));
        }
        let (head, rest) = self.0.split_at(n);
        self.0 = rest;
        Ok(head)
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four bytes"),
        ))
    }
}
