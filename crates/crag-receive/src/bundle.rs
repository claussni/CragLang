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
//! The bytes are a version, then each part in turn, as `crag_abi::wire`
//! writes them. They come from the program's own build, so a malformed
//! bundle is a fault of the toolchain, reported as an error.

use crag_abi::wire::{self, Writer};
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
        let mut w = Writer::default();
        w.u32(VERSION);
        w.seq(&self.modules, |w, (path, text)| {
            w.text(path);
            w.text(text);
        });
        w.seq(&self.resources, |w, (module, source, content)| {
            w.text(module);
            w.text(source);
            match content {
                Ok(bytes) => {
                    w.u8(0);
                    w.bytes(bytes);
                }
                Err(why) => {
                    w.u8(1);
                    w.text(why);
                }
            }
        });
        w.seq(&self.packages.packages, |w, p| {
            w.text(&p.name);
            w.u32(p.major);
            w.seq(&p.exports, |w, s| w.text(s));
            w.seq(&p.imports, |w, s| w.text(s));
            w.seq(&p.dev_imports, |w, s| w.text(s));
            w.seq(&p.natives, |w, (name, files)| {
                w.text(name);
                w.seq(files, |w, s| w.text(s));
            });
        });
        let indices: Vec<_> = self.indices.by_hash.iter().collect();
        w.seq(&indices, |w, (hash, index)| {
            w.raw(&hash[..]);
            w.u32(**index);
        });
        w.u32(self.indices.base);
        w.seq(&self.cells, |w, (name, key)| {
            w.text(name);
            w.u32(key.func.0);
            w.u32(key.signature);
        });
        w.0
    }

    pub fn decode(bytes: &[u8]) -> Result<Bundle, String> {
        let mut r = Reader::new(bytes);
        let version = r.u32()?;
        if version != VERSION {
            return Err(format!("a bundle of version {version}, not {VERSION}"));
        }
        let modules = r.seq(|r| Ok((r.text()?, r.text()?)))?;
        let resources = r.seq(|r| {
            let module = r.text()?;
            let source = r.text()?;
            let content = match r.u8()? {
                0 => Ok(r.bytes()?.to_vec()),
                _ => Err(r.text()?),
            };
            Ok((module, source, content))
        })?;
        let packages = r.seq(|r| {
            Ok(PackageScope {
                name: r.text()?,
                major: r.u32()?,
                exports: r.seq(Reader::text)?,
                imports: r.seq(Reader::text)?,
                dev_imports: r.seq(Reader::text)?,
                natives: r.seq(|r| Ok((r.text()?, r.seq(Reader::text)?)))?,
            })
        })?;
        let mut indices = TypeIndices::default();
        for (hash, index) in r.seq(|r| {
            let hash: [u8; 16] = r.array()?;
            Ok((hash, r.u32()?))
        })? {
            indices.by_hash.insert(hash, index);
        }
        indices.base = r.u32()?;
        let cells = r.seq(|r| {
            let name = r.text()?;
            let key = SlotKey {
                func: FuncId(r.u32()?),
                signature: r.u32()?,
            };
            Ok((name, key))
        })?;
        if !r.is_empty() {
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

type Reader<'a> = wire::Reader<'a, String>;
