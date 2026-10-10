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

//! The shapes values are printed by (Implementation Plan §11.6.5), from
//! the layouts code generation gives their types.

use std::collections::HashMap;

use crag_abi::{LIST_SIZE, MAP_SIZE, Number, Shape, ShapeField, Shapes};
use crag_db::Db;
use crag_hir::Program;
use crag_types::{Builtin, Ty, TyKind, declared_fields};

use crate::layout::{Layout, layout, record_layout, record_subtypes, type_index};

/// The shapes a value of `ty` is printed by, and the index of its own.
pub fn shapes<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> (Shapes, u32) {
    let mut b = Builder {
        db,
        program,
        shapes: Shapes::default(),
        done: HashMap::new(),
    };
    let root = b.shape(ty);
    (b.shapes, root)
}

struct Builder<'db> {
    db: &'db dyn Db,
    program: Program,
    shapes: Shapes,
    done: HashMap<Ty<'db>, u32>,
}

impl<'db> Builder<'db> {
    fn shape(&mut self, ty: Ty<'db>) -> u32 {
        if let Some(&index) = self.done.get(&ty) {
            return index;
        }
        // In place before its parts, which may contain it.
        let index = self.shapes.shapes.len() as u32;
        self.shapes.shapes.push(Shape::Unit);
        self.done.insert(ty, index);
        let (db, program) = (self.db, self.program);
        let opaque = |words| Shape::Opaque {
            name: ty.display(db),
            words,
        };
        let shape = match (layout(db, program, ty), ty.kind(db)) {
            // As source writes the value: without type arguments.
            (Some(Layout::Zero), TyKind::Named(item, _)) => {
                Shape::Tag(item.name(db).text(db).clone())
            }
            (Some(Layout::Zero), _) => Shape::Unit,
            (Some(Layout::Imm(b)), _) => match number(b) {
                Some(n) => Shape::Number(n),
                None => opaque(1),
            },
            (Some(l @ (Layout::Tag | Layout::Union)), TyKind::Union(members)) => Shape::Union {
                members: members
                    .clone()
                    .into_iter()
                    .map(|m| (type_index(m) as u32, self.shape(m)))
                    .collect(),
                words: l.words() as u32,
            },
            (Some(Layout::Box), TyKind::Builtin(b, args)) => match (b, &args[..]) {
                (Builtin::List, &[element]) => Shape::List(self.shape(element)),
                (Builtin::Set, &[element]) => Shape::Set(self.shape(element)),
                (Builtin::Map, &[key, value]) => Shape::Map(self.shape(key), self.shape(value)),
                _ => opaque(1),
            },
            (Some(Layout::Box), TyKind::Named(..) | TyKind::Record { .. }) => {
                match self.record(ty) {
                    Some(shape) => shape,
                    None => opaque(1),
                }
            }
            (Some(Layout::Closure), _) => Shape::Function,
            (Some(l), _) => opaque(l.words() as u32),
            (None, _) => opaque(0),
        };
        let size = match &shape {
            Shape::List(_) => Some(LIST_SIZE),
            // A set is a map whose values have no words.
            Shape::Set(_) | Shape::Map(..) => Some(MAP_SIZE),
            Shape::Record { .. } => record_layout(db, program, ty).map(|(_, size)| size),
            _ => None,
        };
        if let Some(size) = size {
            self.shapes.boxes.push((index, type_index(ty) as u32, size));
        }
        self.shapes.shapes[index as usize] = shape;
        if let TyKind::Named(..) = ty.kind(db)
            && matches!(self.shapes.shapes[index as usize], Shape::Record { .. })
        {
            self.shapes.records.push((type_index(ty) as u32, index));
            // A value may be of a subtype, which its box says.
            for sub in record_subtypes(db, program, ty) {
                self.shape(sub);
            }
        }
        index
    }

    /// A record's fields at their offsets: a named type's in the order it
    /// declares them, an anonymous record's by name.
    fn record(&mut self, ty: Ty<'db>) -> Option<Shape> {
        let (db, program) = (self.db, self.program);
        let (mut slots, _) = record_layout(db, program, ty)?;
        let name = match ty.kind(db) {
            TyKind::Named(item, _) => Some(item.name(db).text(db).clone()),
            _ => None,
        };
        if let Some(declared) = declared_fields(db, program, ty) {
            let place = |n| declared.iter().position(|(d, ..)| *d == n);
            slots.sort_by_key(|s| place(s.name));
        }
        let fields = slots
            .into_iter()
            .map(|s| ShapeField {
                name: s.name.text(db).clone(),
                offset: s.offset,
                shape: self.shape(s.ty),
            })
            .collect();
        Some(Shape::Record { name, fields })
    }
}

fn number(builtin: Builtin) -> Option<Number> {
    Some(match builtin {
        Builtin::Int | Builtin::Int8 | Builtin::Int16 | Builtin::Int32 => Number::Signed,
        Builtin::UInt8 | Builtin::UInt16 | Builtin::UInt32 | Builtin::UInt64 => Number::Unsigned,
        Builtin::Float => Number::Float,
        Builtin::Fixed(digits) => Number::Fixed(digits),
        Builtin::CodePoint => Number::CodePoint,
        _ => return None,
    })
}
