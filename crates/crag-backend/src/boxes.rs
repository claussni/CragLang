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

//! Flat fields (Implementation Plan §11.10.10, Compiler Architecture
//! §A11.4.4): how a record's box holds its fields.
//!
//! With flat layouts a box holds its record's storage form after the
//! header (`flat::box_layout`): a field of a flat record type is inline,
//! split into its fields' places, a union keeps a local tag or a niche,
//! integers a `where` condition bounds are narrowed and `Bool`s are bits.
//! Code sees each field in the register form a split value gives it
//! (`split::Form`), and the box's slots say where those registers are in
//! it. A box is made by packing all its registers into words at once,
//! which is why records are written only whole; a field is read by
//! loading the words that hold it and unpacking its registers. A record
//! or union stored inline is a value of its own once read out of the box:
//! it is loaded into a split local, or boxed where a box is needed.
//!
//! Without flat layouts every field is a word or two at a word offset, as
//! `layout::record_layout` places it.

use crag_abi::{HEADER_SIZE, StoredKind, StoredSlot, StoredTag, widen};
use crag_db::Db;
use crag_hir::Program;
use crag_types::{Builtin, Step, Ty};

use crate::flat;
use crate::layout::{self, type_index};
use crate::split::{
    Form, NicheTest, Slot, SlotKind, UnionTag, element_storage, fields_form, fields_slots,
    flat_layouts,
};

/// A record's box as code makes and reads it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoxForm<'db> {
    /// Its bytes, the header's too, a multiple of eight.
    pub size: u32,
    /// Its fields, each in its register form: a `Form::Fields`.
    pub form: Form<'db>,
    /// Where those registers are in the box, from its start.
    pub slots: Vec<Slot>,
    /// The offset of the word with the address of its dispose code.
    pub dispose: Option<u32>,
}

/// How a box of a record type holds its fields (see the module's
/// comment); none for a type without a layout.
pub fn box_form<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<BoxForm<'db>> {
    if !flat_layouts() {
        let (fields, size) = layout::record_layout(db, program, ty)?;
        let mut places = Vec::new();
        let mut slots = Vec::new();
        let mut at = 0;
        for f in fields {
            let n = f.layout.words();
            places.push((f.name, f.ty, Form::Words(f.layout)));
            if n > 0 {
                slots.push(Slot {
                    at,
                    offset: f.offset,
                    size: 8 * n as u32,
                    bits: None,
                    kind: SlotKind::Words,
                });
            }
            at += n;
        }
        return Some(BoxForm {
            size,
            form: Form::Fields(places),
            slots,
            dispose: layout::dispose_word(db, program, ty),
        });
    }
    let l = flat::box_layout(db, program, ty).as_ref()?;
    let form = fields_form(db, program, &l.fields)?;
    let Form::Fields(fields) = &form else {
        return None;
    };
    let mut slots = Vec::new();
    fields_slots(db, program, &l.fields, fields, 0, HEADER_SIZE, &mut slots)?;
    Some(BoxForm {
        size: (HEADER_SIZE + l.size).next_multiple_of(8),
        form,
        slots,
        dispose: l.dispose.map(|d| HEADER_SIZE + d),
    })
}

/// The slots of the registers `at..at + n`, the value there, from its own
/// first register.
pub fn select(slots: &[Slot], at: usize, n: usize) -> Vec<Slot> {
    slots
        .iter()
        .filter(|s| (at..at + n).contains(&s.at))
        .map(|s| shift(s, at))
        .collect()
}

/// The slots of a union's member, from the member's first register:
/// `slots` are the union's.
pub fn member_slots(slots: &[Slot], member: Ty<'_>) -> Option<Vec<Slot>> {
    let [union] = slots else {
        return None;
    };
    let SlotKind::Union { members, .. } = &union.kind else {
        return None;
    };
    let (_, own) = members.iter().find(|(m, _)| *m == type_index(member))?;
    Some(own.iter().map(|s| shift(s, union.at + 1)).collect())
}

/// A slot with its registers `by` earlier.
fn shift(slot: &Slot, by: usize) -> Slot {
    let mut slot = slot.clone();
    slot.at -= by;
    if let SlotKind::Union { members, .. } = &mut slot.kind {
        for (_, own) in members {
            *own = own.iter().map(|s| shift(s, by)).collect();
        }
    }
    slot
}

/// A slot with its bytes `by` earlier.
pub fn rebase(slot: &Slot, by: u32) -> Slot {
    let mut slot = slot.clone();
    slot.offset -= by;
    if let SlotKind::Union { tag, members } = &mut slot.kind {
        match tag {
            UnionTag::Bytes { offset, .. } | UnionTag::Niche { offset, .. } => *offset -= by,
        }
        for (_, own) in members {
            *own = own.iter().map(|s| rebase(s, by)).collect();
        }
    }
    slot
}

/// The bytes the slots read: the first, and the one after the last.
pub fn span(slots: &[Slot]) -> Option<(u32, u32)> {
    let mut out: Option<(u32, u32)> = None;
    let mut cover = |from: u32, to: u32| {
        out = Some(match out {
            Some((a, b)) => (a.min(from), b.max(to)),
            None => (from, to),
        });
    };
    for slot in slots {
        cover(slot.offset, slot.offset + slot.size.max(1));
        if let SlotKind::Union { tag, members } = &slot.kind {
            match *tag {
                UnionTag::Bytes { offset, size } => cover(offset, offset + size),
                UnionTag::Niche { offset, test, .. } => {
                    let size = match test {
                        NicheTest::Value { size, .. } => u32::from(size),
                        NicheTest::Bit(_) => 1,
                    };
                    cover(offset, offset + size)
                }
            }
            for (_, own) in members {
                if let Some((a, b)) = span(own) {
                    cover(a, b);
                }
            }
        }
    }
    out
}

/// The slots as the runtime reads them.
pub fn stored_slots(slots: &[Slot]) -> Vec<StoredSlot> {
    slots
        .iter()
        .map(|s| StoredSlot {
            at: s.at as u32,
            offset: s.offset,
            size: s.size,
            bits: s.bits,
            kind: match &s.kind {
                SlotKind::Int { signed } => StoredKind::Int { signed: *signed },
                SlotKind::Words => StoredKind::Words,
                SlotKind::Tag(members) => {
                    StoredKind::Tag(members.iter().map(|&m| m as u32).collect())
                }
                SlotKind::Union { tag, members } => StoredKind::Union {
                    tag: match *tag {
                        UnionTag::Bytes { offset, size } => StoredTag::Bytes { offset, size },
                        UnionTag::Niche {
                            empty,
                            offset,
                            test,
                        } => {
                            let (size, value) = match test {
                                NicheTest::Value { size, value } => (size, value),
                                NicheTest::Bit(bit) => (0, u64::from(bit)),
                            };
                            StoredTag::Niche {
                                empty: empty as u32,
                                offset,
                                size,
                                value,
                            }
                        }
                    },
                    members: members
                        .iter()
                        .map(|(m, own)| (*m as u32, stored_slots(own)))
                        .collect(),
                },
            },
        })
        .collect()
}

/// The words of the field `name` of a record's box, in its register
/// form, as the host reads them.
///
/// # Safety
///
/// `ptr` points at a live box of `ty`.
pub unsafe fn field_words<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    name: &str,
    ptr: *const u8,
) -> Option<Vec<u64>> {
    let b = box_form(db, program, ty)?;
    let Form::Fields(fields) = &b.form else {
        return None;
    };
    let field = fields.iter().find(|(n, ..)| n.text(db) == name)?.0;
    let (at, _, f) = b.form.field(field)?;
    let slots = stored_slots(&select(&b.slots, at, f.words()));
    // SAFETY: as the caller promises.
    let bytes = unsafe { std::slice::from_raw_parts(ptr, b.size as usize) };
    let mut out = vec![0; f.words()];
    widen(&slots, bytes, &mut out);
    Some(out)
}

/// The form of the value a place's path reaches from a value of `ty` in
/// its layout's words, when it lies inline in a box or in a list: a record
/// or a union stored flat, which a read loads or boxes.
pub fn stored_form<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    path: &[Step<'db>],
) -> Option<Form<'db>> {
    let mut ty = ty;
    let mut form: Option<Form<'db>> = None;
    for step in path {
        let inner = match (&form, step) {
            (None, Step::Field(name)) => {
                let b = box_form(db, program, ty)?;
                let (_, t, f) = b.form.field(*name)?;
                ty = t;
                f.clone()
            }
            (None, Step::As(t)) => {
                ty = *t;
                continue;
            }
            // A list stores an element flat in its storage form.
            (None, Step::Elem(_) | Step::ElemBack(_)) => {
                let Some((Builtin::List, [element])) = ty.as_builtin(db) else {
                    return None;
                };
                ty = *element;
                if element_storage(db, program, ty).is_none() {
                    continue;
                }
                crate::split::form(db, program, ty)?
            }
            (None, Step::Slice { .. }) => continue,
            (Some(f), Step::Field(name)) => {
                let (_, t, inner) = f.field(*name)?;
                ty = t;
                inner.clone()
            }
            (Some(_), Step::As(t)) if *t == ty => continue,
            (Some(f), Step::As(t)) => {
                let inner = f.member(*t)?.clone();
                ty = *t;
                inner
            }
            (Some(_), _) => return None,
        };
        form = match inner {
            Form::Words(_) => None,
            f => Some(f),
        };
    }
    form
}
