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

//! The table a release executable starts from (Implementation Plan
//! §11.10.3 to §11.10.5): what the object writer puts in the section
//! [`SECTION`], at the global symbol [`SYMBOL`], and the runtime archive's
//! start reads in memory once the linker has placed the code.
//!
//! The table holds what the runtime needs of the code: each function's
//! start, the length of its code, its name and its code object without
//! code and relocations, which holds its stack maps, handlers and the
//! origins of its traps (§11.6.3); the descriptors of the types the code
//! uses; the entry stubs tasks start in; and the roots, each with its
//! function, the stub it starts in, and the shapes of its result. A
//! program that runs received code carries what its receiver needs
//! (Implementation Plan §11.10.9): the bundle it rebuilds the program from,
//! and the cells of the program's values. Function ids in it are places in
//! the table.
//!
//! Integers are little-endian, and a sequence is its length as a `u32` and
//! then its items. Addresses are words the linker fills, at the offsets
//! [`Table::encode`] gives, so the table is read from memory as it was
//! written; in the object file they are the addends of their relocations.

use crate::protocol::{decode_object, decode_types, encode_object, encode_types};
use crate::wire::{self, Writer};
use crate::{CodeObject, Shapes, TypeDescriptor};

/// The section that holds the table.
pub const SECTION: &str = ".crag_code";

/// The global symbol at the start of the table.
pub const SYMBOL: &str = "crag_code";

/// The version of the table's layout.
pub const VERSION: u32 = 4;

/// The length of the header: the version and the length of the table.
pub const HEADER: usize = 8;

/// What a release executable starts from.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    /// The stubs a task starts in, for none, one and two result words.
    pub task_entries: [u64; 3],
    pub functions: Vec<Function>,
    pub types: Vec<(u32, TypeDescriptor)>,
    pub roots: Vec<Root>,
    /// What the receiver of code needs, for a program that runs received
    /// code.
    pub receiving: Option<Receiving>,
}

/// What the receiver of a release executable needs (Plan §11.10.9).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Receiving {
    /// The bundle of the program, `crag_receive::Bundle`'s bytes.
    pub bundle: Vec<u8>,
    /// The cells of the program's values, by `module.name`, with their
    /// addresses, or in the object zero.
    pub cells: Vec<(String, u64)>,
}

/// A function of the program, at its place.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Function {
    /// The address of its code, or in the object its offset in `.text`.
    pub start: u64,
    /// The length of its code.
    pub len: u32,
    pub name: String,
    /// Its code object without code and relocations.
    pub object: CodeObject,
}

/// A function the program is started at, with a global symbol of its own.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Root {
    pub name: String,
    /// Its function's place.
    pub place: u32,
    /// The stub it starts in, for its parameter and result words.
    pub entry: u64,
    /// The shapes of its result, and the root of them.
    pub shapes: Shapes,
    pub result: u32,
}

impl Table {
    /// The table's bytes, and the offsets of its addresses in them: the
    /// task entries, each function's start, each root's entry and each
    /// cell of the receiving, in that order.
    pub fn encode(&self) -> (Vec<u8>, Vec<usize>) {
        let mut w = Writer::default();
        let mut addresses = Vec::new();
        let mut address = |w: &mut Writer, x: u64| {
            addresses.push(w.0.len());
            w.u64(x);
        };
        w.u32(VERSION);
        // The length, once known.
        w.u32(0);
        for &entry in &self.task_entries {
            address(&mut w, entry);
        }
        w.u32(self.functions.len() as u32);
        for f in &self.functions {
            address(&mut w, f.start);
            w.u32(f.len);
            w.bytes(f.name.as_bytes());
            w.bytes(&encode_object(&CodeObject {
                code: Vec::new(),
                relocs: Vec::new(),
                ..f.object.clone()
            }));
        }
        w.bytes(&encode_types(&self.types));
        w.u32(self.roots.len() as u32);
        for root in &self.roots {
            w.bytes(root.name.as_bytes());
            w.u32(root.place);
            address(&mut w, root.entry);
            w.bytes(&root.shapes.encode());
            w.u32(root.result);
        }
        match &self.receiving {
            None => w.u32(0),
            Some(receiving) => {
                w.u32(1);
                w.bytes(&receiving.bundle);
                w.u32(receiving.cells.len() as u32);
                for (name, at) in &receiving.cells {
                    w.bytes(name.as_bytes());
                    address(&mut w, *at);
                }
            }
        }
        let len = w.0.len() as u32;
        w.0[4..8].copy_from_slice(&len.to_le_bytes());
        (w.0, addresses)
    }

    /// The length of the table whose first `HEADER` bytes these are, or
    /// an error for a table of another version.
    pub fn len(header: &[u8; HEADER]) -> Result<usize, String> {
        let version = u32::from_le_bytes(header[..4].try_into().expect("four bytes"));
        if version != VERSION {
            return Err(format!("a table of version {version}, not {VERSION}"));
        }
        Ok(u32::from_le_bytes(header[4..].try_into().expect("four bytes")) as usize)
    }

    /// The table `encode` gave the bytes of, its addresses filled in.
    pub fn decode(bytes: &[u8]) -> Result<Table, String> {
        let header = bytes.first_chunk().ok_or("the table ends early")?;
        if Table::len(header)? != bytes.len() {
            return Err("the table's length is not its own".into());
        }
        let mut r = Reader::new(&bytes[HEADER..]);
        let task_entries = [r.u64()?, r.u64()?, r.u64()?];
        let functions = (0..r.u32()?)
            .map(|_| {
                Ok(Function {
                    start: r.u64()?,
                    len: r.u32()?,
                    name: r.text()?,
                    object: decode_object(r.bytes()?).map_err(|e| e.to_string())?,
                })
            })
            .collect::<Result<_, String>>()?;
        let types = decode_types(r.bytes()?).map_err(|e| e.to_string())?;
        let roots = (0..r.u32()?)
            .map(|_| {
                Ok(Root {
                    name: r.text()?,
                    place: r.u32()?,
                    entry: r.u64()?,
                    shapes: Shapes::decode(r.bytes()?)?,
                    result: r.u32()?,
                })
            })
            .collect::<Result<_, String>>()?;
        let receiving = match r.u32()? {
            0 => None,
            _ => Some(Receiving {
                bundle: r.bytes()?.to_vec(),
                cells: (0..r.u32()?)
                    .map(|_| Ok((r.text()?, r.u64()?)))
                    .collect::<Result<_, String>>()?,
            }),
        };
        match r.is_empty() {
            true => Ok(Table {
                task_entries,
                functions,
                types,
                roots,
                receiving,
            }),
            false => Err("bytes after the table".into()),
        }
    }
}

/// Bytes read from the front.
type Reader<'a> = wire::Reader<'a, String>;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Number, Shape, StackCheck};

    #[test]
    fn a_table_reads_back_with_its_addresses() {
        let table = Table {
            task_entries: [1, 2, 3],
            functions: vec![Function {
                start: 0x40,
                len: 12,
                name: "main".into(),
                object: CodeObject {
                    code: Vec::new(),
                    align: 16,
                    entry: 0,
                    relocs: Vec::new(),
                    footprint: 0,
                    stack_check: StackCheck::Margin,
                    stack_maps: Vec::new(),
                    handlers: Vec::new(),
                    module: "demo.app".into(),
                    origins: Vec::new(),
                    inlined: Vec::new(),
                    inlined_at: Vec::new(),
                    details: Vec::new(),
                    natives: Vec::new(),
                },
            }],
            types: Vec::new(),
            roots: vec![Root {
                name: "crag_main".into(),
                place: 0,
                entry: 0x80,
                shapes: Shapes {
                    shapes: vec![Shape::Number(Number::Signed)],
                    ..Shapes::default()
                },
                result: 0,
            }],
            receiving: Some(Receiving {
                bundle: vec![1, 2, 3],
                cells: vec![("demo.app.table".into(), 0x100)],
            }),
        };
        let (bytes, addresses) = table.encode();
        assert_eq!(Table::decode(&bytes), Ok(table.clone()));
        let words: Vec<u64> = addresses
            .iter()
            .map(|&at| u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap()))
            .collect();
        assert_eq!(words, [1, 2, 3, 0x40, 0x80, 0x100]);
        assert!(Table::decode(&bytes[..bytes.len() - 1]).is_err());
    }
}
