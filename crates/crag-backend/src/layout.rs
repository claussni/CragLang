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
//! index alone when every member is a tag, as for `Bool`. Strings and
//! bytes take two words, their bytes inline or a buffer with where they are
//! in it (§11.6.9), and so does a function value: the address of its code
//! and its environment, a box or null (§11.5.9). A union holds a member of
//! two words in a member box, whose pointer is the payload (`crag_abi`).

use crate::flat;
use crate::split::{element_storage, flat_layouts, ref_storage};
use crag_abi::{CountedField, ElementLayout, FieldGuard, HEADER_SIZE, TypeDescriptor};
use crag_db::Db;
use crag_db::plumbing::AsId;
use crag_hir::{ItemKind, Name, Program, item_tree, module_index};
use crag_types::{
    Builtin, Ty, TyKind, TypeDefKind, dispose_handler, fields_of, is_subtype, parent,
    record_subtypes, type_def, type_header,
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
    /// A string or bytes: up to 15 bytes inline, or a buffer, a box,
    /// and where the bytes are in it (see `crag_abi`).
    Pair,
    /// A function value: its code's address, then its environment, a box
    /// or null.
    Closure,
}

impl Layout {
    pub fn words(self) -> usize {
        match self {
            Layout::Zero => 0,
            Layout::Imm(_) | Layout::Box | Layout::Tag => 1,
            Layout::Union | Layout::Pair | Layout::Closure => 2,
        }
    }
}

/// The layout of a type; none for what code generation does not handle
/// yet: open records and type parameters.
pub fn layout<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Layout> {
    Some(match ty.kind(db) {
        TyKind::Error | TyKind::Param(..) => return None,
        TyKind::Builtin(b, _) => match b {
            Builtin::Oks | Builtin::Errs => return None,
            Builtin::Str | Builtin::Bytes => Layout::Pair,
            Builtin::List
            | Builtin::Map
            | Builtin::Set
            | Builtin::Ref
            | Builtin::Ext
            | Builtin::Lazy
            | Builtin::RuntimeStream
            | Builtin::RuntimeHub
            | Builtin::RuntimeSocket => Layout::Box,
            b => Layout::Imm(*b),
        },
        TyKind::Named(item, _) => match type_def(db, program, *item).kind {
            TypeDefKind::Tag => Layout::Zero,
            TypeDefKind::Record { .. } => Layout::Box,
            // A conditioned alias's values are its target's (§3.10.1).
            TypeDefKind::Refined(_) => {
                let target = crag_types::unrefined(db, program, ty);
                if target == ty {
                    return None;
                }
                return layout(db, program, target);
            }
            _ => return None,
        },
        TyKind::Record { open: true, .. } => return None,
        TyKind::Record { fields, .. } if fields.is_empty() => Layout::Zero,
        TyKind::Record { .. } => Layout::Box,
        TyKind::Fn { .. } => Layout::Closure,
        TyKind::Union(members) => {
            let mut tags = true;
            for &m in members {
                match layout(db, program, m)? {
                    Layout::Zero => {}
                    Layout::Imm(_) | Layout::Box | Layout::Pair | Layout::Closure => tags = false,
                    Layout::Tag | Layout::Union => return None,
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
/// by name (Compiler Architecture §11.1); every field is word-aligned. The
/// first type with a dispose handler among a type and those it spreads has
/// a word of its own before its fields, `dispose_word`.
pub fn record_layout<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<(Vec<FieldSlot<'db>>, u32)> {
    let all = fields_of(db, program, ty)?;
    let mut slots: Vec<FieldSlot<'db>> = Vec::new();
    let (inherited, mut end) = inherited_layout(db, program, ty)?;
    if let Some(inherited) = inherited {
        slots = inherited;
    }
    if own_dispose_word(db, program, ty) {
        end += 8;
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

/// A named type's parent's slots and size, or the header's size alone.
#[allow(clippy::type_complexity)]
fn inherited_layout<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<(Option<Vec<FieldSlot<'db>>>, u32)> {
    if let TyKind::Named(..) = ty.kind(db)
        && let Some(p) = parent(db, program, ty)
    {
        let (slots, size) = record_layout(db, program, p)?;
        return Some((Some(slots), size));
    }
    Some((None, HEADER_SIZE))
}

/// Whether a type has a dispose handler that none of the types it spreads
/// has, so its boxes need a word for the address of their dispose code.
pub(crate) fn own_dispose_word<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    matches!(ty.kind(db), TyKind::Named(..))
        && dispose_handler(db, program, ty).is_some()
        && parent(db, program, ty).is_none_or(|p| dispose_handler(db, program, p).is_none())
}

/// The offset of the word that holds the address of a box's dispose code,
/// for a type with a dispose handler: after the fields of the parents
/// without one.
pub fn dispose_word<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<u32> {
    if !matches!(ty.kind(db), TyKind::Named(..)) || dispose_handler(db, program, ty).is_none() {
        return None;
    }
    if own_dispose_word(db, program, ty) {
        return Some(inherited_layout(db, program, ty)?.1);
    }
    dispose_word(db, program, parent(db, program, ty)?)
}

/// The indices of the types known to fit `ty` that a value of it may have
/// at run time: the record types of the program without type parameters
/// that are subtypes of it, or `ty` alone.
pub fn subtypes<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Vec<i64> {
    let mut out: Vec<i64> = std::iter::once(ty)
        .chain(record_subtypes(db, program, ty))
        .map(type_index)
        .collect();
    out.sort_unstable();
    out
}

/// The type indices of the signal types a handler of `ty` takes (§11.3):
/// `ty` and every named type without parameters that is a subtype of it,
/// records and tags alike, sorted; and how many parent types `ty` has, which
/// makes it more specific.
pub fn signal_types<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> (Vec<u32>, u32) {
    let mut out = vec![type_index(ty) as u32];
    for &module in module_index(db, program).modules.values() {
        for item in &item_tree(db, module).items {
            let id = item.id;
            if *id.kind(db) != ItemKind::Type || !type_header(db, program, id).params.is_empty() {
                continue;
            }
            let candidate = Ty::new(db, TyKind::Named(id, Vec::new()));
            if candidate != ty && is_subtype(db, program, candidate, ty) {
                out.push(type_index(candidate) as u32);
            }
        }
    }
    out.sort_unstable();
    out.dedup();
    let mut parents = 0;
    let mut at = ty;
    while let Some(p) = parent(db, program, at) {
        parents += 1;
        at = p;
    }
    (out, parents)
}

/// The type indices a value of the union `ty` may carry with a box as its
/// payload: those of its members that are boxes, and of their subtypes,
/// and of its members of two words, in member boxes. None when a member
/// has no layout yet.
pub fn boxed_indices<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Vec<u32>> {
    let mut out = Vec::new();
    for m in ty.members(db) {
        match layout(db, program, m)? {
            Layout::Box => out.extend(subtypes(db, program, m).into_iter().map(|i| i as u32)),
            Layout::Pair | Layout::Closure => out.push(type_index(m) as u32),
            _ => {}
        }
    }
    out.sort_unstable();
    out.dedup();
    Some(out)
}

/// The words of a value of `ty` where a ref, a lazy value, a stream, a hub
/// or a signal holds it, a record in its box, as a collection did before
/// flat layouts (`collection_element`). None for what has no layout yet.
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
        Layout::Closure => (2, vec![CountedField::Box(8)]),
        // A buffer, unless the first word's lowest bit says the bytes are
        // inline.
        Layout::Pair => (2, vec![CountedField::Box(0)]),
    };
    Some(ElementLayout::of_words(words, counted))
}

/// How a value of `ty` lies in a list, map or grid: in its storage form
/// where it is stored flat (`split::element_storage`), whose pointer map
/// says where the references are, and anything else as in a cell. None
/// for what has no layout yet.
pub fn collection_element<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<ElementLayout> {
    let Some((size, _)) = element_storage(db, program, ty) else {
        return element_layout(db, program, ty);
    };
    let l = flat::layout(db, program, ty).as_ref()?;
    Some(ElementLayout {
        size,
        align: l.align,
        counted: l.pointers.iter().map(|p| counted_pointer(p, 0)).collect(),
    })
}

/// How a ref cell holds a value of `ty`: in its storage form where it
/// stores it flat (`split::ref_storage`), anything else as other cells
/// do. None for what has no layout yet.
pub fn ref_cell<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<ElementLayout> {
    let Some((size, _)) = ref_storage(db, program, ty) else {
        return element_layout(db, program, ty);
    };
    let l = flat::layout(db, program, ty).as_ref()?;
    Some(ElementLayout {
        size,
        align: l.align,
        counted: l.pointers.iter().map(|p| counted_pointer(p, 0)).collect(),
    })
}

/// Whether two values of `ty` are equal exactly when their words are, as
/// the runtime compares map keys unless they are strings or bytes:
/// numbers but `Float`, code points, tags, and unions of these.
pub fn equal_by_words<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    ty.members(db)
        .into_iter()
        .all(|m| match layout(db, program, m) {
            Some(Layout::Zero | Layout::Tag) => true,
            Some(Layout::Imm(b)) => b != Builtin::Float,
            _ => false,
        })
}

/// Whether values of `ty` can be keys the runtime compares by their words:
/// those equal by their words, and a `Float`, whose -0.0 generated code
/// turns into 0.0 before the runtime sees it (Specification §12.2).
pub fn word_keys<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    equal_by_words(db, program, ty) || matches!(ty.as_builtin(db), Some((Builtin::Float, _)))
}

/// Whether values of `ty` are strings or bytes, which the runtime compares
/// as map keys by their bytes.
pub fn is_text<'db>(db: &'db dyn Db, ty: Ty<'db>) -> bool {
    matches!(ty.as_builtin(db), Some((Builtin::Str | Builtin::Bytes, _)))
}

/// The descriptor of a record or collection type: for a record the fields
/// that hold references, which the runtime releases when it frees a box of
/// the type, and for a collection the layouts of what it holds. None when
/// a field or an element has no layout yet, or a map's key is neither one
/// of `word_keys` nor a string or bytes.
pub fn type_descriptor<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
) -> Option<TypeDescriptor> {
    let map = |key: Ty<'db>, value: Option<Ty<'db>>| {
        let text_keys = is_text(db, key);
        if !text_keys && !word_keys(db, program, key) {
            return None;
        }
        let value = match value {
            Some(v) => collection_element(db, program, v)?,
            None => ElementLayout::default(),
        };
        let key = element_layout(db, program, key)?;
        Some(TypeDescriptor::Map {
            key,
            value,
            text_keys,
        })
    };
    match ty.as_builtin(db) {
        Some((Builtin::List, [element])) => {
            return Some(TypeDescriptor::List {
                element: collection_element(db, program, *element)?,
                cell: element_layout(db, program, *element)?,
                ref_cell: ref_cell(db, program, *element)?,
            });
        }
        Some((Builtin::Map, [key, value])) => return map(*key, Some(*value)),
        Some((Builtin::Set, [key])) => return map(*key, None),
        // The box of an end of a stream or of a hub: its runtime handle.
        Some((Builtin::RuntimeStream, [])) => {
            return Some(TypeDescriptor::Record {
                counted: vec![CountedField::Stream(HEADER_SIZE)],
                dispose: None,
            });
        }
        Some((Builtin::RuntimeHub, [])) => {
            return Some(TypeDescriptor::Record {
                counted: vec![CountedField::Hub(HEADER_SIZE)],
                dispose: None,
            });
        }
        Some((Builtin::RuntimeSocket, [])) => {
            return Some(TypeDescriptor::Record {
                counted: vec![CountedField::Socket(HEADER_SIZE)],
                dispose: None,
            });
        }
        // A lazy value's box: the runtime's cell, which holds the value,
        // then the function value that computes it.
        Some((Builtin::Lazy, [_])) => {
            return Some(TypeDescriptor::Record {
                counted: vec![
                    CountedField::Lazy(HEADER_SIZE),
                    CountedField::Box(HEADER_SIZE + 16),
                ],
                dispose: None,
            });
        }
        // A ref cell's box: the cell's version word, then the value as
        // `ref_cell` lays it out (`crag_abi::REF_CELL_SIZE`); an `ext`'s:
        // the lock, then the value as other cells hold it.
        Some((b @ (Builtin::Ref | Builtin::Ext), [value])) => {
            let base = HEADER_SIZE + 8;
            if b == Builtin::Ref && ref_storage(db, program, *value).is_some() {
                let l = flat::layout(db, program, *value).as_ref()?;
                return Some(TypeDescriptor::Record {
                    counted: l
                        .pointers
                        .iter()
                        .map(|p| counted_pointer(p, base))
                        .collect(),
                    dispose: None,
                });
            }
            let mut counted: Vec<CountedField> = element_layout(db, program, *value)?
                .counted
                .into_iter()
                .map(|field| match field {
                    CountedField::Box(offset) => CountedField::Box(base + offset),
                    CountedField::Union { offset, boxed } => CountedField::Union {
                        offset: base + offset,
                        boxed,
                    },
                    CountedField::Ext(offset) => CountedField::Ext(base + offset),
                    field => field,
                })
                .collect();
            if b == Builtin::Ext {
                counted.push(CountedField::Ext(HEADER_SIZE));
            }
            return Some(TypeDescriptor::Record {
                counted,
                dispose: None,
            });
        }
        _ => {}
    }
    // A box stores its record flat: its pointer map says where the
    // references are, and when a union's member holds one.
    if flat_layouts() {
        let l = flat::box_layout(db, program, ty).as_ref()?;
        let counted = l
            .pointers
            .iter()
            .map(|p| counted_pointer(p, HEADER_SIZE))
            .collect();
        return Some(TypeDescriptor::Record {
            counted,
            dispose: l.dispose.map(|d| HEADER_SIZE + d),
        });
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
            Layout::Closure => counted.push(CountedField::Box(slot.offset + 8)),
            Layout::Pair => counted.push(CountedField::Box(slot.offset)),
            Layout::Zero | Layout::Imm(_) | Layout::Tag => {}
        }
    }
    Some(TypeDescriptor::Record {
        counted,
        dispose: dispose_word(db, program, ty),
    })
}

/// A pointer of a storage form that starts at `base`, after a box's
/// header or at an element's first word, as the runtime releases it.
fn counted_pointer(p: &flat::Pointer, base: u32) -> CountedField {
    let offset = base + p.offset;
    if p.guards.is_empty() {
        return CountedField::Box(offset);
    }
    let guards = p
        .guards
        .iter()
        .map(|g| match g {
            flat::Guard::Tag { offset, tags } => FieldGuard::Tag {
                offset: base + offset,
                tags: tags.clone(),
            },
            flat::Guard::NotNiche(n) => match n.kind {
                flat::NicheKind::Value { size, value } => FieldGuard::NotValue {
                    offset: base + n.offset,
                    size,
                    value,
                },
                flat::NicheKind::Bit(bit) => FieldGuard::BitClear {
                    offset: base + n.offset,
                    bit,
                },
            },
        })
        .collect();
    CountedField::Guarded { offset, guards }
}

/// Whether a value of `ty` goes through deferred teardown when its last
/// reference goes (Specification §13.3, §13.5): a collection, whose chain
/// of boxes may be long, that holds nothing `Immediate`. The runtime's
/// handles are: a socket closes, a stream end is abandoned and a lock is
/// freed at the drop. So is what may hold anything, a function value or a
/// type parameter.
pub fn deferred<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> bool {
    match ty.as_builtin(db) {
        Some((Builtin::List | Builtin::Map | Builtin::Set, args)) => args
            .iter()
            .all(|&a| !immediate(db, program, a, &mut Vec::new())),
        _ => false,
    }
}

/// Whether a value of `ty` may hold something `Immediate`.
fn immediate<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>, seen: &mut Vec<Ty<'db>>) -> bool {
    if seen.contains(&ty) {
        return false;
    }
    seen.push(ty);
    match ty.kind(db) {
        TyKind::Builtin(b, args) => match b {
            Builtin::Ext
            | Builtin::Lazy
            | Builtin::RuntimeStream
            | Builtin::RuntimeHub
            | Builtin::RuntimeSocket => true,
            _ => args.iter().any(|&a| immediate(db, program, a, seen)),
        },
        TyKind::Named(..) | TyKind::Record { .. } => fields_of(db, program, ty)
            .is_some_and(|fields| fields.iter().any(|&(_, f)| immediate(db, program, f, seen))),
        TyKind::Union(members) => members.iter().any(|&m| immediate(db, program, m, seen)),
        TyKind::Fn { .. } | TyKind::Param(..) | TyKind::Error => true,
    }
}
