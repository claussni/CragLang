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

//! How values are laid out in machine words (Compiler Architecture §11).
//!
//! A value is zero, one or two words. Unit and tags take none; numbers and
//! box pointers one. A union is its type index plus a payload word, or the
//! index alone when every member is a tag, as for `Bool`. Strings, bytes
//! and closures take two words.

use crag_abi::{CountedField, ElementLayout, HEADER_SIZE, TypeDescriptor};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{ItemKind, Name, Program, item_tree, module_index};
use crag_types::{
    Builtin, Ty, TyKind, TypeDefKind, fields_of, is_subtype, parent, type_def, type_header,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    /// Unit and tags: their type is all there is to them.
    Zero,
    /// A number, a code point or a `Fixed`, by its builtin.
    Imm(Builtin),
    /// A pointer to a box: a record or a collection.
    Box,
    /// A union of tags: the type index of the value's tag.
    Tag,
    /// A union: the type index of the value's member, then its payload,
    /// which is zero for a tag.
    Union,
    /// Two words of a string, bytes or a closure.
    Pair,
}

impl Layout {
    pub fn words(self) -> usize {
        match self {
            Layout::Zero => 0,
            Layout::Imm(_) | Layout::Box | Layout::Tag => 1,
            Layout::Union | Layout::Pair => 2,
        }
    }
}

/// The layout of a type; none for what code generation does not handle
/// yet: open records, type parameters, and unions with a member of two
/// words.
pub fn layout<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Layout> {
    Some(match ty.kind(db) {
        TyKind::Error | TyKind::Param(..) => return None,
        TyKind::Builtin(b, _) => match b {
            Builtin::Oks | Builtin::Errs => return None,
            Builtin::Str | Builtin::Bytes => Layout::Pair,
            Builtin::List
            | Builtin::Map
            | Builtin::Set
            | Builtin::Grid
            | Builtin::Ref
            | Builtin::Lazy => Layout::Box,
            b => Layout::Imm(*b),
        },
        TyKind::Named(item, _) => match type_def(db, program, *item).kind {
            TypeDefKind::Tag => Layout::Zero,
            TypeDefKind::Record { .. } => Layout::Box,
            _ => return None,
        },
        TyKind::Record { open: true, .. } => return None,
        TyKind::Record { fields, .. } if fields.is_empty() => Layout::Zero,
        TyKind::Record { .. } => Layout::Box,
        TyKind::Fn { .. } => Layout::Pair,
        TyKind::Union(members) => {
            let mut tags = true;
            for &m in members {
                match layout(db, program, m)? {
                    Layout::Zero => {}
                    Layout::Imm(_) | Layout::Box => tags = false,
                    _ => return None,
                }
            }
            if tags { Layout::Tag } else { Layout::Union }
        }
    })
}

/// The index of a type in the descriptor table (Compiler Architecture
/// §11.2). Types are interned, so equal types have one index.
pub fn type_index(ty: Ty<'_>) -> i64 {
    i64::from(ty.as_id().index())
}

/// A field of a box: its name, type, layout and offset.
#[derive(Clone, Copy, Debug)]
pub struct FieldSlot<'db> {
    pub name: Name<'db>,
    pub ty: Ty<'db>,
    pub layout: Layout,
    pub offset: u32,
}

/// The fields of a record type at their offsets, and the box's size. A type
/// lays out its parent's fields first, at the same offsets, then its own
/// by name (Compiler Architecture §11.1); every field is word-aligned.
pub fn record_layout<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<(Vec<FieldSlot<'db>>, u32)> {
    let all = fields_of(db, program, ty)?;
    let mut slots: Vec<FieldSlot<'db>> = Vec::new();
    let mut end = HEADER_SIZE;
    if let TyKind::Named(..) = ty.kind(db)
        && let Some(p) = parent(db, program, ty)
    {
        let (inherited, size) = record_layout(db, program, p)?;
        slots = inherited;
        end = size;
    }
    let mut own: Vec<(Name<'db>, Ty<'db>)> = Vec::new();
    for (name, field_ty) in all {
        match slots.iter_mut().find(|s| s.name == name) {
            // An amended field keeps its parent's place, so it must keep
            // its size too.
            Some(slot) => {
                let layout = layout(db, program, field_ty)?;
                if layout.words() != slot.layout.words() {
                    return None;
                }
                slot.ty = field_ty;
                slot.layout = layout;
            }
            None => own.push((name, field_ty)),
        }
    }
    own.sort_by(|a, b| a.0.text(db).cmp(b.0.text(db)));
    for (name, field_ty) in own {
        let layout = layout(db, program, field_ty)?;
        slots.push(FieldSlot {
            name,
            ty: field_ty,
            layout,
            offset: end,
        });
        end += 8 * layout.words() as u32;
    }
    Some((slots, end))
}

/// The indices of the types known to fit `ty` that a value of it may have
/// at run time: the record types of the program without type parameters
/// that are subtypes of it, or `ty` alone.
pub fn subtypes<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Vec<i64> {
    let mut out = vec![type_index(ty)];
    if !matches!(ty.kind(db), TyKind::Named(_, args) if args.is_empty()) {
        return out;
    }
    for &module in module_index(db, program).modules.values() {
        for item in &item_tree(db, module).items {
            let id = item.id;
            if *id.kind(db) != ItemKind::Type || !type_header(db, program, id).params.is_empty() {
                continue;
            }
            let candidate = Ty::new(db, TyKind::Named(id, Vec::new()));
            if candidate != ty
                && matches!(type_def(db, program, id).kind, TypeDefKind::Record { .. })
                && is_subtype(db, program, candidate, ty)
            {
                out.push(type_index(candidate));
            }
        }
    }
    out.sort_unstable();
    out
}

/// The type indices a value of the union `ty` may carry with a box as its
/// payload: those of its members that are boxes, and of their subtypes.
/// None when a member has no layout yet.
pub fn boxed_indices<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Vec<u32>> {
    let mut out = Vec::new();
    for m in ty.members(db) {
        if layout(db, program, m)? == Layout::Box {
            out.extend(subtypes(db, program, m).into_iter().map(|i| i as u32));
        }
    }
    out.sort_unstable();
    out.dedup();
    Some(out)
}

/// The words of a value of `ty` in a collection. None for what has no
/// layout yet, and for strings, bytes and closures, whose references are
/// not counted yet.
pub fn element_layout<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<ElementLayout> {
    let (words, counted) = match layout(db, program, ty)? {
        Layout::Zero => (0, Vec::new()),
        Layout::Imm(_) | Layout::Tag => (1, Vec::new()),
        Layout::Box => (1, vec![CountedField::Box(0)]),
        Layout::Union => {
            let boxed = boxed_indices(db, program, ty)?;
            let counted = match boxed.is_empty() {
                true => Vec::new(),
                false => vec![CountedField::Union { offset: 0, boxed }],
            };
            (2, counted)
        }
        Layout::Pair => return None,
    };
    Some(ElementLayout { words, counted })
}

/// Whether two values of `ty` are equal exactly when their words are, as
/// the runtime compares map keys: numbers but `Float`, code points, tags,
/// and unions of these.
pub fn equal_by_words<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    ty.members(db)
        .into_iter()
        .all(|m| match layout(db, program, m) {
            Some(Layout::Zero | Layout::Tag) => true,
            Some(Layout::Imm(b)) => b != Builtin::Float,
            _ => false,
        })
}

/// The descriptor of a record or collection type: for a record the fields
/// that hold references, which the runtime releases when it frees a box of
/// the type, and for a collection the layouts of what it holds. None when
/// a field or an element is a string, bytes or a closure, whose references
/// are not counted yet, or a map's key is not equal by its words.
pub fn type_descriptor<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<TypeDescriptor> {
    let map = |key: Ty<'db>, value: Option<Ty<'db>>| {
        if !equal_by_words(db, program, key) {
            return None;
        }
        let value = match value {
            Some(v) => element_layout(db, program, v)?,
            None => ElementLayout::default(),
        };
        let key = element_layout(db, program, key)?;
        Some(TypeDescriptor::Map { key, value })
    };
    match ty.as_builtin(db) {
        Some((Builtin::List, [element])) => {
            let element = element_layout(db, program, *element)?;
            return Some(TypeDescriptor::List { element });
        }
        Some((Builtin::Map, [key, value])) => return map(*key, Some(*value)),
        Some((Builtin::Set, [key])) => return map(*key, None),
        _ => {}
    }
    let (slots, _) = record_layout(db, program, ty)?;
    let mut counted = Vec::new();
    for slot in slots {
        match slot.layout {
            Layout::Box => counted.push(CountedField::Box(slot.offset)),
            Layout::Union => {
                let boxed = boxed_indices(db, program, slot.ty)?;
                if !boxed.is_empty() {
                    counted.push(CountedField::Union {
                        offset: slot.offset,
                        boxed,
                    });
                }
            }
            Layout::Pair => return None,
            Layout::Zero | Layout::Imm(_) | Layout::Tag => {}
        }
    }
    Some(TypeDescriptor::Record { counted })
}
