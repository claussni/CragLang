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

//! What a receiver rebuilds the program from (Implementation Plan
//! §11.10.9): the source of every module, the resources its `embed`s
//! read, its packages, the type indices of its code and the cells of its
//! module-level values. The host sends it to an image, and a release
//! executable carries it, so that the program checks and compiles code it
//! receives against itself.
//!
//! The bytes are a version, then each part in turn: integers
//! little-endian, a sequence as its length, a `u32`, and then its items,
//! a string as its bytes. They come from the program's own build, so a
//! malformed bundle is a fault of the toolchain, reported as an error.

use crag_abi::{FuncId, SlotKey};
use crag_db::{Db, RootDatabase, Setter};
use crag_hir::{ModuleId, PackageScope, Packages, Program, Resource, TypeIndices};

/// The version of the bundle's layout.
const VERSION: u32 = 1;

/// A program, as a receiver rebuilds it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Bundle {
    /// Each module's path and source, in the program's order.
    pub modules: Vec<(String, String)>,
    /// The resources: the module, the source as written, and the content
    /// or why it could not be read.
    pub resources: Vec<(String, String, Result<Vec<u8>, String>)>,
    pub packages: Packages,
    /// The type indices of the program's code (`crag_backend::program_indices`).
    pub indices: TypeIndices,
    /// The cells of the module-level values the program's code computes:
    /// the value as `module.name`, and the slot key of its cell in the
    /// program.
    pub cells: Vec<(String, SlotKey)>,
}

impl Bundle {
    /// The sources, resources and packages of a program, with the indices
    /// and cells of its code.
    pub fn of(
        db: &dyn Db,
        program: Program,
        indices: TypeIndices,
        cells: Vec<(String, SlotKey)>,
    ) -> Bundle {
        let modules = program
            .modules(db)
            .iter()
            .map(|m| (m.path(db).clone(), m.file(db).text(db).clone()))
            .collect();
        let resources = program
            .resources(db)
            .iter()
            .map(|(m, source, resource)| {
                let content = match resource.content(db) {
                    Ok(c) => Ok(c.to_vec()),
                    Err(e) => Err(e.clone()),
                };
                (m.path(db).clone(), source.clone(), content)
            })
            .collect();
        Bundle {
            modules,
            resources,
            packages: program.packages(db).clone(),
            indices,
            cells,
        }
    }

    /// A database with the program the bundle holds.
    pub fn open(&self) -> (RootDatabase, Program) {
        let mut db = RootDatabase::new();
        let modules: Vec<ModuleId> = self
            .modules
            .iter()
            .map(|(path, text)| ModuleId::of(&db, path, text))
            .collect();
        let resources = self
            .resources
            .iter()
            .filter_map(|(path, source, content)| {
                let module = *modules.iter().find(|m| m.path(&db) == path)?;
                let content = content.clone().map(|c| c.into());
                Some((module, source.clone(), Resource::new(&db, content)))
            })
            .collect();
        let program = Program::new(&db, modules, resources);
        program.set_packages(&mut db).to(self.packages.clone());
        program.set_type_indices(&mut db).to(self.indices.clone());
        (db, program)
    }

    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer(Vec::new());
        w.u32(VERSION);
        w.seq(&self.modules, |w, (path, text)| {
            w.str(path);
            w.str(text);
        });
        w.seq(&self.resources, |w, (module, source, content)| {
            w.str(module);
            w.str(source);
            match content {
                Ok(bytes) => {
                    w.u8(0);
                    w.bytes(bytes);
                }
                Err(why) => {
                    w.u8(1);
                    w.str(why);
                }
            }
        });
        w.seq(&self.packages.packages, |w, p| {
            w.str(&p.name);
            w.u32(p.major);
            w.seq(&p.exports, |w, s| w.str(s));
            w.seq(&p.imports, |w, s| w.str(s));
            w.seq(&p.dev_imports, |w, s| w.str(s));
            w.seq(&p.natives, |w, (name, files)| {
                w.str(name);
                w.seq(files, |w, s| w.str(s));
            });
        });
        let indices: Vec<_> = self.indices.by_hash.iter().collect();
        w.seq(&indices, |w, (hash, index)| {
            w.0.extend_from_slice(&hash[..]);
            w.u32(**index);
        });
        w.u32(self.indices.base);
        w.seq(&self.cells, |w, (name, key)| {
            w.str(name);
            w.u32(key.func.0);
            w.u32(key.signature);
        });
        w.0
    }

    pub fn decode(bytes: &[u8]) -> Result<Bundle, String> {
        let mut r = Reader { bytes, at: 0 };
        let version = r.u32()?;
        if version != VERSION {
            return Err(format!("a bundle of version {version}, not {VERSION}"));
        }
        let modules = r.seq(|r| Ok((r.str()?, r.str()?)))?;
        let resources = r.seq(|r| {
            let module = r.str()?;
            let source = r.str()?;
            let content = match r.u8()? {
                0 => Ok(r.bytes()?.to_vec()),
                _ => Err(r.str()?),
            };
            Ok((module, source, content))
        })?;
        let packages = r.seq(|r| {
            Ok(PackageScope {
                name: r.str()?,
                major: r.u32()?,
                exports: r.seq(Reader::str)?,
                imports: r.seq(Reader::str)?,
                dev_imports: r.seq(Reader::str)?,
                natives: r.seq(|r| Ok((r.str()?, r.seq(Reader::str)?)))?,
            })
        })?;
        let mut indices = TypeIndices::default();
        for (hash, index) in r.seq(|r| {
            let hash: [u8; 16] = r.take(16)?.try_into().expect("sixteen bytes");
            Ok((hash, r.u32()?))
        })? {
            indices.by_hash.insert(hash, index);
        }
        indices.base = r.u32()?;
        let cells = r.seq(|r| {
            let name = r.str()?;
            let key = SlotKey {
                func: FuncId(r.u32()?),
                signature: r.u32()?,
            };
            Ok((name, key))
        })?;
        if r.at != bytes.len() {
            return Err("bytes after the bundle".into());
        }
        Ok(Bundle {
            modules,
            resources,
            packages: Packages { packages },
            indices,
            cells,
        })
    }
}

struct Writer(Vec<u8>);

impl Writer {
    fn u8(&mut self, n: u8) {
        self.0.push(n);
    }

    fn u32(&mut self, n: u32) {
        self.0.extend(n.to_le_bytes());
    }

    fn bytes(&mut self, b: &[u8]) {
        self.u32(b.len() as u32);
        self.0.extend_from_slice(b);
    }

    fn str(&mut self, s: &str) {
        self.bytes(s.as_bytes());
    }

    fn seq<T>(&mut self, items: &[T], mut f: impl FnMut(&mut Writer, &T)) {
        self.u32(items.len() as u32);
        for item in items {
            f(self, item);
        }
    }
}

struct Reader<'b> {
    bytes: &'b [u8],
    at: usize,
}

impl<'b> Reader<'b> {
    fn take(&mut self, n: usize) -> Result<&'b [u8], String> {
        let end = self
            .at
            .checked_add(n)
            .filter(|&e| e <= self.bytes.len())
            .ok_or("the bundle ends early")?;
        let out = &self.bytes[self.at..end];
        self.at = end;
        Ok(out)
    }

    fn u8(&mut self) -> Result<u8, String> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(
            self.take(4)?.try_into().expect("four bytes"),
        ))
    }

    fn bytes(&mut self) -> Result<&'b [u8], String> {
        let n = self.u32()? as usize;
        self.take(n)
    }

    fn str(&mut self) -> Result<String, String> {
        String::from_utf8(self.bytes()?.to_vec()).map_err(|_| "a string that is no UTF-8".into())
    }

    fn seq<T>(
        &mut self,
        mut f: impl FnMut(&mut Self) -> Result<T, String>,
    ) -> Result<Vec<T>, String> {
        let n = self.u32()? as usize;
        // Each item takes at least a byte, which bounds a forged length.
        if n > self.bytes.len() - self.at {
            return Err("a sequence longer than the bundle".into());
        }
        (0..n).map(|_| f(self)).collect()
    }
}
