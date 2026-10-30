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

use crag_abi::{HEADER_SIZE, LIST_SIZE, MAP_SIZE, Number, Shape, ShapeField, Shapes};
use crag_db::Db;
use crag_hir::{Name, Program};
use crag_types::{Builtin, Ty, TyKind, declared_fields, record_subtypes};

use crate::boxes::{box_form, rebase, select, span, stored_slots};
use crate::layout::{Layout, layout, type_index};
use crate::split::{Form, Slot, SlotKind, form};

/// The shapes a value of `ty` is printed by, and the index of its own.
pub fn shapes<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> (Shapes, u32) {
    let mut b = Builder {
        db,
        program,
        shapes: Shapes::default(),
        done: HashMap::new(),
        inlined: Vec::new(),
        stored: HashMap::new(),
    };
    let root = b.shape(ty);
    (b.shapes, root)
}

/// The shapes of a value of `ty` kept split in registers (Plan
/// §11.10.10), as a step passes a split local: its root is inline.
pub fn split_shapes<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> (Shapes, u32) {
    let mut b = Builder {
        db,
        program,
        shapes: Shapes::default(),
        done: HashMap::new(),
        inlined: Vec::new(),
        stored: HashMap::new(),
    };
    let root = match form(db, program, ty) {
        Some(f) => b.inline(ty, &f),
        None => b.shape(ty),
    };
    (b.shapes, root)
}

struct Builder<'db> {
    db: &'db dyn Db,
    program: Program,
    shapes: Shapes,
    done: HashMap<Ty<'db>, u32>,
    /// The shapes of split values by type and form, and of stored fields,
    /// made once, so that a subtype's box keeps its parent's.
    inlined: Vec<(Ty<'db>, Form<'db>, u32)>,
    stored: HashMap<Shape, u32>,
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
        // A conditioned alias's values are its target's (§3.10.1).
        let ty = crag_types::unrefined(db, program, ty);
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
            (Some(Layout::Pair), TyKind::Builtin(Builtin::Str, _)) => Shape::Str,
            (Some(Layout::Pair), TyKind::Builtin(Builtin::Bytes, _)) => Shape::Bytes,
            (Some(l), _) => opaque(l.words() as u32),
            (None, _) => opaque(0),
        };
        let size = match &shape {
            Shape::List(_) => Some(LIST_SIZE),
            // A set is a map whose values have no words.
            Shape::Set(_) | Shape::Map(..) => Some(MAP_SIZE),
            Shape::Record { .. } => box_form(db, program, ty).map(|b| b.size),
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

    /// A split record: its fields' words in its register form, shown as a
    /// record's are.
    fn inline(&mut self, ty: Ty<'db>, f: &Form<'db>) -> u32 {
        if let Form::Words(_) = f {
            return self.shape(ty);
        }
        if let Some(&(_, _, index)) = self.inlined.iter().find(|(t, g, _)| *t == ty && g == f) {
            return index;
        }
        let index = self.split(ty, f);
        self.inlined.push((ty, f.clone(), index));
        index
    }

    fn split(&mut self, ty: Ty<'db>, f: &Form<'db>) -> u32 {
        let db = self.db;
        if let Form::Union(members) = f {
            let index = self.shapes.shapes.len() as u32;
            self.shapes.shapes.push(Shape::Unit);
            let members = members
                .iter()
                .map(|(m, inner)| (type_index(*m) as u32, self.inline(*m, inner)))
                .collect();
            self.shapes.shapes[index as usize] = Shape::Variant {
                members,
                words: f.words() as u32,
            };
            return index;
        }
        let Form::Fields(places) = f else {
            return self.shape(ty);
        };
        let index = self.shapes.shapes.len() as u32;
        self.shapes.shapes.push(Shape::Unit);
        let mut fields = Vec::new();
        let mut at = 0;
        for (name, t, inner) in places {
            fields.push(ShapeField {
                name: name.text(db).clone(),
                offset: at as u32,
                shape: self.inline(*t, inner),
            });
            at += inner.words();
        }
        match declared_fields(db, self.program, ty) {
            Some(declared) => {
                let place = |n: &str| declared.iter().position(|(d, ..)| d.text(db) == n);
                fields.sort_by_key(|f| place(&f.name));
            }
            None => fields.sort_by(|a, b| a.name.cmp(&b.name)),
        }
        let name = match ty.kind(db) {
            TyKind::Named(item, _) => Some(item.name(db).text(db).clone()),
            _ => None,
        };
        self.shapes.shapes[index as usize] = Shape::Inline {
            name,
            fields,
            words: f.words() as u32,
        };
        index
    }

    /// A record's fields at their offsets in its box: a named type's in
    /// the order it declares them, an anonymous record's by name.
    fn record(&mut self, ty: Ty<'db>) -> Option<Shape> {
        let (db, program) = (self.db, self.program);
        let b = box_form(db, program, ty)?;
        let Form::Fields(places) = &b.form else {
            return None;
        };
        let mut fields = Vec::new();
        let mut at = 0;
        for (name, t, f) in places {
            let n = f.words();
            let slots = select(&b.slots, at, n);
            at += n;
            fields.push((*name, self.field(*name, *t, f, &slots)));
        }
        match declared_fields(db, program, ty) {
            Some(declared) => {
                let place = |n| declared.iter().position(|(d, ..)| *d == n);
                fields.sort_by_key(|(n, _)| place(*n));
            }
            None => fields.sort_by(|a, b| a.1.name.cmp(&b.1.name)),
        }
        let name = match ty.kind(db) {
            TyKind::Named(item, _) => Some(item.name(db).text(db).clone()),
            _ => None,
        };
        let fields = fields.into_iter().map(|(_, f)| f).collect();
        Some(Shape::Record { name, fields })
    }

    /// A field of a box: its words at a word offset as they are, or
    /// stored flat (Compiler Architecture §A11.4).
    fn field(&mut self, name: Name<'db>, ty: Ty<'db>, f: &Form<'db>, slots: &[Slot]) -> ShapeField {
        let name_text = name.text(self.db).clone();
        let Some((from, to)) = span(slots) else {
            // Nothing is stored: a unit or a tag.
            return ShapeField {
                name: name_text,
                offset: HEADER_SIZE,
                shape: self.shape(ty),
            };
        };
        if let (Form::Words(_), [slot]) = (f, slots)
            && slot.kind == SlotKind::Words
            && slot.offset.is_multiple_of(8)
        {
            return ShapeField {
                name: name_text,
                offset: slot.offset,
                shape: self.shape(ty),
            };
        }
        let form = self.inline(ty, f);
        let slots: Vec<Slot> = slots.iter().map(|s| rebase(s, from)).collect();
        let stored = Shape::Stored {
            form,
            size: to - from,
            slots: stored_slots(&slots),
            words: f.words() as u32,
        };
        let shape = match self.stored.get(&stored) {
            Some(&index) => index,
            None => {
                let index = self.shapes.shapes.len() as u32;
                self.shapes.shapes.push(stored.clone());
                self.stored.insert(stored, index);
                index
            }
        };
        ShapeField {
            name: name_text,
            offset: from,
            shape,
        }
    }
}

pub(crate) fn number(builtin: Builtin) -> Option<Number> {
    Some(match builtin {
        Builtin::Int | Builtin::Int8 | Builtin::Int16 | Builtin::Int32 => Number::Signed,
        Builtin::UInt8 | Builtin::UInt16 | Builtin::UInt32 | Builtin::UInt64 => Number::Unsigned,
        Builtin::Float => Number::Float,
        Builtin::Fixed(digits) => Number::Fixed(digits),
        Builtin::CodePoint => Number::CodePoint,
        _ => return None,
    })
}
