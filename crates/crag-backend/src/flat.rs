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

//! Flat layouts (Implementation Plan §11.10.10, Compiler Architecture
//! §A11.4): how a value of a type is stored when it need not live in a box
//! of its own.
//!
//! `layout` gives a type its class and its storage form: the offsets of
//! its fields, `Bool`s and tag-only unions as bits of a flag byte after the
//! other fields, integers a `where` condition bounds narrowed, a union's
//! local tag, the niche a `T | Empty` can use instead of a tag, and the
//! pointer map. It depends on the type alone. Code does not use it yet:
//! every record is still boxed as `layout::record_layout` places it, and
//! the REPL's `:layout` shows what flattening would do.
//!
//! A field that would contain its own type is the recursive edge, and
//! holds a box: a field's member is boxed when it reaches the record it is
//! a field of through flat fields, so every type of a cycle boxes its edges
//! into the cycle. A member whose fields unfold into ever new types, as in
//! polymorphic recursion, is boxed the same way once its unfolding passes
//! `MAX_UNFOLD` types.

use crag_db::Db;
use crag_hir::{Name, Owner, Program, hir_body, type_identity};
use crag_types::{
    Builtin, Ty, TyKind, TypeDefKind, dispose_handler, fields_of, int_bounds, parent, prelude_item,
    record_subtypes, subst, type_def,
};

/// The most bytes a flat value takes (§A11.4).
pub const MAX_FLAT_SIZE: u32 = 32;

/// The most managed pointers a flat value holds: copying it retains each.
pub const MAX_FLAT_POINTERS: u32 = 2;

/// How many types a field's member may unfold into before it counts as
/// unbounded.
const MAX_UNFOLD: usize = 256;

/// The storage form of a type.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Layout<'db> {
    pub size: u32,
    pub align: u32,
    pub class: LayoutClass,
    /// A record's fields, in storage order.
    pub fields: Vec<FieldPlace<'db>>,
    /// A union's tag and members.
    pub union: Option<UnionPlace<'db>>,
    /// The interval an integer's values lie in, and the builtin it is
    /// stored as when that is narrower than its own.
    pub range: Option<(i128, i128)>,
    pub narrowed: Option<Builtin>,
    /// Where the managed pointers are.
    pub pointers: Vec<Pointer>,
    /// The most managed pointers a value holds at once.
    pub managed: u32,
    /// A pattern no value has, which a union with one tag can use for it.
    pub niche: Option<Niche>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum LayoutClass {
    /// `()` and tags: nothing is stored.
    Zero,
    /// The one-word values: numbers, code points and tag-only unions.
    Immediate,
    /// Fixed size, no managed pointers, at most `MAX_FLAT_SIZE` bytes.
    Plain,
    /// At most `MAX_FLAT_SIZE` bytes and `MAX_FLAT_POINTERS` managed
    /// pointers.
    Inline,
    /// One box pointer.
    Boxed(BoxReason),
}

/// Why a type is boxed (§A11.4.6).
#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum BoxReason {
    /// A field's member that contains the record again.
    Recursion,
    /// Larger than `MAX_FLAT_SIZE` bytes, or with more than
    /// `MAX_FLAT_POINTERS` managed pointers, as it would be flat.
    Size { size: u32, pointers: u32 },
    /// A `Dispose` handler, `is Secret`, a `CPtr` or a runtime object.
    Lifecycle,
    /// A parent that may hold a subtype, or an open record.
    OpenParent,
    /// A member that unfolds into ever new types.
    UnboundedInstantiation,
    /// A list, map, set or grid, whose size varies.
    Collection,
}

/// A field of a record in storage form.
#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct FieldPlace<'db> {
    pub name: Name<'db>,
    pub ty: Ty<'db>,
    pub offset: u32,
    /// Its bytes; zero for a field stored as bits or not at all.
    pub size: u32,
    /// Its first bit and width in the flag byte at `offset`.
    pub bits: Option<(u8, u8)>,
    /// The builtin an integer field is narrowed to.
    pub narrowed: Option<Builtin>,
    /// Why its members that contain the record are boxed.
    pub boxed: Option<BoxReason>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct UnionPlace<'db> {
    pub tag: TagPlace,
    /// The members by their local tags.
    pub members: Vec<MemberPlace<'db>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum TagPlace {
    /// A tag of this many bytes at the start.
    Bytes(u32),
    /// The one tag is the niche of the other member.
    Niche(Niche),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct MemberPlace<'db> {
    pub ty: Ty<'db>,
    /// Where its payload starts.
    pub offset: u32,
    pub boxed: Option<BoxReason>,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Pointer {
    pub offset: u32,
    pub kind: PointerKind,
    /// What must hold for the pointer to be there.
    pub guards: Vec<Guard>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum PointerKind {
    /// A box pointer, or null.
    Box,
    /// The first word of a string or bytes: a buffer unless its bytes are
    /// inline.
    Text,
    /// The environment of a function value, a box or null.
    Env,
}

#[derive(Clone, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum Guard {
    /// The tag byte at `offset` is one of `tags`.
    Tag { offset: u32, tags: Vec<u8> },
    /// The value is not the niche.
    NotNiche(Niche),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub struct Niche {
    pub offset: u32,
    pub kind: NicheKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, crag_db::SalsaValue)]
pub enum NicheKind {
    /// The `size` bytes at the offset hold `value`, little-endian.
    Value { size: u8, value: u64 },
    /// The bit of the flag byte at the offset is set.
    Bit(u8),
}

impl Layout<'_> {
    fn empty(class: LayoutClass) -> Self {
        Layout {
            size: 0,
            align: 1,
            class,
            fields: Vec::new(),
            union: None,
            range: None,
            narrowed: None,
            pointers: Vec::new(),
            managed: 0,
            niche: None,
        }
    }

    fn sized(size: u32, class: LayoutClass) -> Self {
        Layout {
            size,
            align: size.max(1),
            ..Layout::empty(class)
        }
    }

    /// A box pointer: what a boxed type stores in its parent.
    fn boxed(reason: BoxReason) -> Self {
        Layout {
            pointers: vec![Pointer {
                offset: 0,
                kind: PointerKind::Box,
                guards: Vec::new(),
            }],
            managed: 1,
            niche: Some(Niche {
                offset: 0,
                kind: NicheKind::Value { size: 8, value: 0 },
            }),
            ..Layout::sized(8, LayoutClass::Boxed(reason))
        }
    }

    /// A string or bytes, or a function value: two words, of which one may
    /// be managed.
    fn pair(kind: PointerKind, offset: u32) -> Self {
        Layout {
            align: 8,
            pointers: vec![Pointer {
                offset,
                kind,
                guards: Vec::new(),
            }],
            managed: 1,
            ..Layout::sized(16, LayoutClass::Inline)
        }
    }

    fn integer(builtin: Builtin) -> Self {
        Layout {
            range: builtin.int_range(),
            ..Layout::sized(int_size(builtin), LayoutClass::Immediate)
        }
    }

    pub fn is_boxed(&self) -> bool {
        matches!(self.class, LayoutClass::Boxed(_))
    }

    /// Whether the type is a `Bool` or another union of tags, which a
    /// record stores in bits.
    fn tag_bits(&self) -> Option<u8> {
        let union = self.union.as_ref()?;
        let n = union.members.len() as u32;
        let tags_only =
            union.members.iter().all(|m| m.offset == 0) && self.class == LayoutClass::Immediate;
        let width = (32 - (n - 1).leading_zeros()) as u8;
        (tags_only && width <= 8).then_some(width)
    }
}

fn int_size(builtin: Builtin) -> u32 {
    match builtin {
        Builtin::Int8 | Builtin::UInt8 => 1,
        Builtin::Int16 | Builtin::UInt16 => 2,
        Builtin::Int32 | Builtin::UInt32 | Builtin::CodePoint | Builtin::CF32 => 4,
        _ => 8,
    }
}

/// The storage form of a type, after monomorphization; none for a type
/// parameter or what failed to type.
#[crag_db::tracked(returns(ref))]
pub fn layout<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Layout<'db>> {
    if let Some(reason) = forced(db, program, ty) {
        return Some(Layout::boxed(reason));
    }
    Some(match ty.kind(db) {
        TyKind::Error | TyKind::Param(..) => return None,
        TyKind::Builtin(b, _) => builtin(*b)?,
        TyKind::Named(item, args) => match type_def(db, program, *item).kind {
            TypeDefKind::Tag => Layout::empty(LayoutClass::Zero),
            TypeDefKind::Builtin(b) => builtin(b)?,
            TypeDefKind::Alias(target) => {
                layout(db, program, subst(db, program, target, *item, args)).clone()?
            }
            // A conditioned alias's values are its target's, within its
            // bounds (§3.10.1).
            TypeDefKind::Refined(_) => {
                let target = parent(db, program, ty)?;
                let base = layout(db, program, target).clone()?;
                let bounds = int_bounds(db, program, *item);
                match bounds.iter().find(|(s, _, _)| s.is_none()) {
                    Some(&(_, lo, hi)) => narrow(base, lo, hi),
                    None => base,
                }
            }
            TypeDefKind::Record { .. } => record(db, program, ty)?,
            TypeDefKind::Form => return None,
        },
        TyKind::Record { fields, .. } if fields.is_empty() => Layout::empty(LayoutClass::Zero),
        TyKind::Record { .. } => record(db, program, ty)?,
        TyKind::Fn { .. } => Layout::pair(PointerKind::Env, 8),
        TyKind::Union(members) => {
            let mut placed = Vec::new();
            for &m in members {
                placed.push((m, layout(db, program, m).clone()?, None));
            }
            union(db, placed)
        }
    })
}

fn builtin(b: Builtin) -> Option<Layout<'static>> {
    Some(match b {
        Builtin::Int
        | Builtin::Int8
        | Builtin::Int16
        | Builtin::Int32
        | Builtin::UInt8
        | Builtin::UInt16
        | Builtin::UInt32
        | Builtin::UInt64 => Layout::integer(b),
        Builtin::Float | Builtin::Fixed(_) | Builtin::CodePoint | Builtin::CF32 => {
            Layout::sized(int_size(b), LayoutClass::Immediate)
        }
        Builtin::Str | Builtin::Bytes => Layout::pair(PointerKind::Text, 0),
        Builtin::List | Builtin::Map | Builtin::Set => Layout::boxed(BoxReason::Collection),
        Builtin::Ref
        | Builtin::Ext
        | Builtin::Lazy
        | Builtin::RuntimeStream
        | Builtin::RuntimeHub
        | Builtin::RuntimeSocket
        | Builtin::CPtr => Layout::boxed(BoxReason::Lifecycle),
        Builtin::COut | Builtin::Oks | Builtin::Errs => return None,
    })
}

/// Why a declared type or an open record is boxed whatever its size.
fn forced<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<BoxReason> {
    match ty.kind(db) {
        TyKind::Record { open: true, .. } => Some(BoxReason::OpenParent),
        TyKind::Named(item, _) => {
            let grid = prelude_item(db, program, "Grid").map(|g| type_identity(db, program, g));
            if grid == Some(*item) {
                return Some(BoxReason::Collection);
            }
            if !matches!(
                type_def(db, program, *item).kind,
                TypeDefKind::Record { .. } | TypeDefKind::Tag
            ) {
                return None;
            }
            let secret = hir_body(db, program, Owner::Item(*item))
                .type_decl
                .as_ref()
                .is_some_and(|d| {
                    d.markers
                        .iter()
                        .any(|(m, negated)| !negated && m.text(db) == "Secret")
                });
            if secret || dispose_handler(db, program, ty).is_some() {
                return Some(BoxReason::Lifecycle);
            }
            (!record_subtypes(db, program, ty).is_empty()).then_some(BoxReason::OpenParent)
        }
        _ => None,
    }
}

/// An integer's layout narrowed to the interval `lo..=hi`: the narrowest
/// builtin that holds it, and a value outside it as the niche.
fn narrow(base: Layout<'_>, lo: i128, hi: i128) -> Layout<'_> {
    let Some((own_lo, own_hi)) = base.range else {
        return base;
    };
    let (lo, hi) = (lo.max(own_lo), hi.min(own_hi));
    if lo > hi {
        return base;
    }
    let candidates = [
        Builtin::UInt8,
        Builtin::Int8,
        Builtin::UInt16,
        Builtin::Int16,
        Builtin::UInt32,
        Builtin::Int32,
        Builtin::UInt64,
        Builtin::Int,
    ];
    let Some(to) = candidates.into_iter().find(|b| {
        let (min, max) = b.int_range().expect("an integer");
        min <= lo && hi <= max
    }) else {
        return base;
    };
    let (min, max) = to.int_range().expect("an integer");
    let size = int_size(to);
    let spare = if lo > min {
        Some(lo - 1)
    } else if hi < max {
        Some(hi + 1)
    } else {
        None
    };
    let mask = if size == 8 {
        u64::MAX
    } else {
        (1u64 << (8 * size)) - 1
    };
    Layout {
        range: Some((lo, hi)),
        narrowed: (size < base.size).then_some(to),
        niche: spare.map(|v| Niche {
            offset: 0,
            kind: NicheKind::Value {
                size: size as u8,
                value: (v as u64) & mask,
            },
        }),
        ..Layout::sized(size.min(base.size), LayoutClass::Immediate)
    }
}

/// A union of members laid out as given, each with why it is boxed if it
/// is an edge of a record's cycle. Tags are numbered members with payloads
/// first, then the tags, each group by name.
fn union<'db>(
    db: &'db dyn Db,
    mut members: Vec<(Ty<'db>, Layout<'db>, Option<BoxReason>)>,
) -> Layout<'db> {
    members.sort_by_cached_key(|(ty, l, _)| (l.class == LayoutClass::Zero, ty.display(db)));
    let zeros = members
        .iter()
        .filter(|(_, l, _)| l.class == LayoutClass::Zero)
        .count();
    let n = members.len() as u32;
    let places = |offset: u32| {
        members
            .iter()
            .map(|&(ty, ref l, boxed)| MemberPlace {
                ty,
                offset: if l.class == LayoutClass::Zero {
                    0
                } else {
                    offset
                },
                boxed,
            })
            .collect()
    };
    let tag_size = if n <= 256 { 1 } else { 2 };
    let spare_tag = (n < 256).then_some(Niche {
        offset: 0,
        kind: NicheKind::Value {
            size: 1,
            value: n.into(),
        },
    });
    if zeros == members.len() {
        return Layout {
            union: Some(UnionPlace {
                tag: TagPlace::Bytes(tag_size),
                members: places(0),
            }),
            niche: spare_tag,
            ..Layout::sized(tag_size, LayoutClass::Immediate)
        };
    }
    // `T | Empty`, with a pattern `T` never has.
    if let [(_, payload, _), (_, _, _)] = members.as_slice()
        && zeros == 1
        && let Some(niche) = payload.niche
    {
        let pointers = payload
            .pointers
            .iter()
            .map(|p| {
                let null = p.kind == PointerKind::Box
                    && niche
                        == Niche {
                            offset: p.offset,
                            kind: NicheKind::Value { size: 8, value: 0 },
                        };
                let mut p = p.clone();
                if !null {
                    p.guards.push(Guard::NotNiche(niche));
                }
                p
            })
            .collect();
        return Layout {
            size: payload.size,
            align: payload.align,
            class: classify(payload.size, payload.managed),
            fields: Vec::new(),
            union: Some(UnionPlace {
                tag: TagPlace::Niche(niche),
                members: places(0),
            }),
            range: None,
            narrowed: None,
            pointers,
            managed: payload.managed,
            niche: None,
        };
    }
    let align = members.iter().map(|(_, l, _)| l.align).max().unwrap_or(1);
    let offset = tag_size.next_multiple_of(align);
    let payload = members.iter().map(|(_, l, _)| l.size).max().unwrap_or(0);
    let size = (offset + payload).next_multiple_of(align);
    let mut pointers = Vec::new();
    for (tag, (_, l, _)) in members.iter().enumerate() {
        for p in &l.pointers {
            let mut guards = vec![Guard::Tag {
                offset: 0,
                tags: vec![tag as u8],
            }];
            guards.extend(p.guards.iter().map(|g| shift_guard(g, offset)));
            pointers.push(Pointer {
                offset: p.offset + offset,
                kind: p.kind,
                guards,
            });
        }
    }
    let managed = members.iter().map(|(_, l, _)| l.managed).max().unwrap_or(0);
    Layout {
        size,
        align,
        class: classify(size, managed),
        fields: Vec::new(),
        union: Some(UnionPlace {
            tag: TagPlace::Bytes(tag_size),
            members: places(offset),
        }),
        range: None,
        narrowed: None,
        pointers,
        managed,
        niche: spare_tag,
    }
}

/// The class of a record or union of this size and this many managed
/// pointers; one that does not fit is boxed.
fn classify(size: u32, managed: u32) -> LayoutClass {
    if size == 0 {
        LayoutClass::Zero
    } else if size > MAX_FLAT_SIZE || managed > MAX_FLAT_POINTERS {
        LayoutClass::Boxed(BoxReason::Size {
            size,
            pointers: managed,
        })
    } else if managed == 0 {
        LayoutClass::Plain
    } else {
        LayoutClass::Inline
    }
}

fn shift_guard(g: &Guard, by: u32) -> Guard {
    match g {
        Guard::Tag { offset, tags } => Guard::Tag {
            offset: offset + by,
            tags: tags.clone(),
        },
        Guard::NotNiche(n) => Guard::NotNiche(shift_niche(*n, by)),
    }
}

fn shift_niche(n: Niche, by: u32) -> Niche {
    Niche {
        offset: n.offset + by,
        ..n
    }
}

/// A record's storage form: its parent's fields first, at their places,
/// then its own by alignment, largest first, and name, then its flag
/// bytes. One that does not fit is boxed.
fn record<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<Layout<'db>> {
    let flat = record_form(db, program, ty, &[ty])?;
    Some(match flat.class {
        LayoutClass::Boxed(reason) => Layout::boxed(reason),
        _ => flat,
    })
}

/// A record's storage form, of whatever size. `owners` are the record
/// and the types that spread it, whose layout is being made: a field's
/// member that contains one of them is boxed.
fn record_form<'db>(
    db: &'db dyn Db,
    program: Program,
    ty: Ty<'db>,
    owners: &[Ty<'db>],
) -> Option<Layout<'db>> {
    let all = fields_of(db, program, ty)?;
    let mut out = Layout::empty(LayoutClass::Zero);
    if let TyKind::Named(..) = ty.kind(db)
        && let Some(p) = parent(db, program, ty)
    {
        let mut owners = owners.to_vec();
        owners.push(p);
        out = record_form(db, program, p, &owners)?;
    }
    let bounds = match ty.kind(db) {
        TyKind::Named(item, _) => int_bounds(db, program, *item),
        _ => Vec::new(),
    };
    let mut bytes: Vec<(FieldPlace<'db>, Layout<'db>)> = Vec::new();
    let mut flags: Vec<(FieldPlace<'db>, u8)> = Vec::new();
    for (name, field_ty) in all {
        let (mut l, boxed) = field_layout(db, program, owners, field_ty)?;
        if let Some(&(_, lo, hi)) = bounds.iter().find(|(s, _, _)| *s == Some(name)) {
            l = narrow(l, lo, hi);
        }
        // An amended field keeps its parent's place if it keeps its size.
        if let Some(i) = out.fields.iter().position(|f| f.name == name) {
            let place = &out.fields[i];
            if place.ty == field_ty || (place.bits.is_none() && place.size == l.size) {
                out.fields[i].ty = field_ty;
                continue;
            }
            out.fields.remove(i);
        }
        let place = FieldPlace {
            name,
            ty: field_ty,
            offset: 0,
            size: l.size,
            bits: None,
            narrowed: l.narrowed,
            boxed,
        };
        match l.tag_bits() {
            Some(width) => flags.push((place, width)),
            None => bytes.push((place, l)),
        }
    }
    bytes.sort_by(|(a, la), (b, lb)| {
        lb.align
            .cmp(&la.align)
            .then_with(|| a.name.text(db).cmp(b.name.text(db)))
    });
    let mut end = out.size;
    for (mut place, l) in bytes {
        end = end.next_multiple_of(l.align);
        place.offset = end;
        out.align = out.align.max(l.align);
        out.pointers.extend(l.pointers.iter().map(|p| Pointer {
            offset: p.offset + end,
            kind: p.kind,
            guards: p.guards.iter().map(|g| shift_guard(g, end)).collect(),
        }));
        out.managed += l.managed;
        if out.niche.is_none() {
            out.niche = l.niche.map(|n| shift_niche(n, end));
        }
        end += l.size;
        out.fields.push(place);
    }
    flags.sort_by(|(a, _), (b, _)| a.name.text(db).cmp(b.name.text(db)));
    let mut bit = 8u8;
    for (mut place, width) in flags {
        if bit + width > 8 {
            bit = 0;
            end += 1;
        }
        place.offset = end - 1;
        place.bits = Some((bit, width));
        bit += width;
        out.fields.push(place);
    }
    if bit < 8 && out.niche.is_none() {
        out.niche = Some(Niche {
            offset: end - 1,
            kind: NicheKind::Bit(bit),
        });
    }
    out.size = end.next_multiple_of(out.align);
    out.class = classify(out.size, out.managed);
    Some(out)
}

/// The layout of a field of a record that `owners` are being laid out
/// for, with its members that contain one of them boxed, and why.
fn field_layout<'db>(
    db: &'db dyn Db,
    program: Program,
    owners: &[Ty<'db>],
    ty: Ty<'db>,
) -> Option<(Layout<'db>, Option<BoxReason>)> {
    let mut edges = false;
    let mut members = Vec::new();
    let mut boxed = None;
    for m in ty.members(db) {
        let reason = match reaches(db, program, m, owners) {
            Reach::No => None,
            Reach::Yes => Some(BoxReason::Recursion),
            Reach::Unbounded => Some(BoxReason::UnboundedInstantiation),
        };
        edges |= reason.is_some();
        boxed = boxed.or(reason);
        members.push((m, reason));
    }
    if !edges {
        return Some((layout(db, program, ty).clone()?, None));
    }
    let mut placed = Vec::new();
    for (m, reason) in members {
        let l = match reason {
            Some(r) => Layout::boxed(r),
            None => layout(db, program, m).clone()?,
        };
        placed.push((m, l, reason));
    }
    let l = match placed.len() {
        1 => placed.pop().expect("one member").1,
        _ => union(db, placed),
    };
    Some((l, boxed))
}

enum Reach {
    Yes,
    No,
    Unbounded,
}

/// Whether a value of `from` stored flat would contain one of `to`: `from`
/// is one of them, or one of its fields' members contains one, through
/// types that are not boxed whatever their size.
fn reaches<'db>(db: &'db dyn Db, program: Program, from: Ty<'db>, to: &[Ty<'db>]) -> Reach {
    let mut seen = vec![from];
    let mut stack = vec![from];
    while let Some(ty) = stack.pop() {
        if to.contains(&ty) {
            return Reach::Yes;
        }
        for next in contained(db, program, ty) {
            if !seen.contains(&next) {
                if seen.len() == MAX_UNFOLD {
                    return Reach::Unbounded;
                }
                seen.push(next);
                stack.push(next);
            }
        }
    }
    Reach::No
}

/// The types a value of `ty` stored flat holds flat: its fields' members,
/// or an alias's target.
fn contained<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Vec<Ty<'db>> {
    if forced(db, program, ty).is_some() {
        return Vec::new();
    }
    match ty.kind(db) {
        TyKind::Named(item, args) => match type_def(db, program, *item).kind {
            TypeDefKind::Alias(target) => vec![subst(db, program, target, *item, args)],
            TypeDefKind::Refined(_) => parent(db, program, ty).into_iter().collect(),
            TypeDefKind::Record { .. } => fields_of(db, program, ty)
                .unwrap_or_default()
                .into_iter()
                .flat_map(|(_, f)| f.members(db))
                .collect(),
            _ => Vec::new(),
        },
        TyKind::Record { .. } => fields_of(db, program, ty)
            .unwrap_or_default()
            .into_iter()
            .flat_map(|(_, f)| f.members(db))
            .collect(),
        _ => Vec::new(),
    }
}

/// What `:layout` shows of a type, after its name: its class, size and
/// alignment, then its fields or members with their places, and its niche
/// and pointers.
pub fn describe<'db>(db: &'db dyn Db, program: Program, ty: Ty<'db>) -> Option<String> {
    let l = layout(db, program, ty).as_ref()?;
    let bytes = |n: u32| match n {
        1 => "1 byte".to_string(),
        n => format!("{n} bytes"),
    };
    let mut out = String::new();
    match l.class {
        LayoutClass::Boxed(reason) => {
            out += &format!("Boxed, {}\n", reason_text(reason));
            return Some(out);
        }
        class => {
            out += &format!("{class:?}, {}, aligned to {}\n", bytes(l.size), l.align);
        }
    }
    let mut rows: Vec<(String, String)> = Vec::new();
    if let Some(n) = l.narrowed {
        rows.push(("stored as".into(), n.name().into()));
    }
    for f in &l.fields {
        let mut place = match (f.bits, f.size) {
            (Some((bit, 1)), _) => format!("offset {}, bit {bit}", f.offset),
            (Some((bit, width)), _) => {
                format!("offset {}, bits {bit}–{}", f.offset, bit + width - 1)
            }
            (None, 0) => "nothing stored".into(),
            (None, size) => format!("offset {}, {}", f.offset, bytes(size)),
        };
        if let Some(n) = f.narrowed {
            place += &format!(" as {}", n.name());
        }
        if let Some(reason) = f.boxed {
            place += &format!(", boxed: {}", reason_text(reason));
        }
        rows.push((format!("{}: {}", f.name.text(db), f.ty.display(db)), place));
    }
    if let Some(u) = &l.union {
        if let TagPlace::Bytes(size) = u.tag {
            rows.push(("tag".into(), format!("offset 0, {}", bytes(size))));
        }
        for (tag, m) in u.members.iter().enumerate() {
            let ml = layout(db, program, m.ty).as_ref();
            let zero = ml.is_some_and(|ml| ml.class == LayoutClass::Zero);
            let mut place = match (u.tag, zero) {
                (TagPlace::Niche(n), true) => niche_text(n),
                (TagPlace::Niche(_), false) => format!("offset 0, {}", bytes(l.size)),
                (TagPlace::Bytes(_), true) => format!("tag {tag}"),
                (TagPlace::Bytes(_), false) => {
                    let size = match m.boxed {
                        Some(_) => 8,
                        None => ml.map_or(0, |ml| ml.size),
                    };
                    format!("tag {tag}, offset {}, {}", m.offset, bytes(size))
                }
            };
            if let Some(reason) = m.boxed {
                place += &format!(", boxed: {}", reason_text(reason));
            }
            rows.push((m.ty.display(db), place));
        }
    }
    if let Some(n) = l.niche {
        rows.push(("niche".into(), niche_text(n)));
    }
    if !l.pointers.is_empty() {
        let pointers: Vec<String> = l.pointers.iter().map(pointer_text).collect();
        rows.push(("pointers".into(), pointers.join("; ")));
    }
    let width = rows
        .iter()
        .map(|(a, _)| a.chars().count())
        .max()
        .unwrap_or(0);
    for (a, b) in rows {
        out += &format!("  {a:width$}  {b}\n");
    }
    Some(out)
}

fn reason_text(reason: BoxReason) -> String {
    match reason {
        BoxReason::Recursion => "it contains itself".into(),
        BoxReason::Size { size, pointers } => format!(
            "flat it would take {size} bytes and {pointers} managed pointers, more than \
             {MAX_FLAT_SIZE} and {MAX_FLAT_POINTERS}"
        ),
        BoxReason::Lifecycle => "it has a lifecycle: a Dispose handler, is Secret, a CPtr or a \
                                 runtime object"
            .into(),
        BoxReason::OpenParent => "it may hold a subtype".into(),
        BoxReason::UnboundedInstantiation => "its fields unfold into ever new types".into(),
        BoxReason::Collection => "a collection, whose size varies".into(),
    }
}

fn niche_text(n: Niche) -> String {
    match n.kind {
        NicheKind::Value { size: 8, value: 0 } => format!("null at offset {}", n.offset),
        NicheKind::Value { value, .. } => format!("{value} at offset {}", n.offset),
        NicheKind::Bit(bit) => format!("bit {bit} at offset {}", n.offset),
    }
}

fn pointer_text(p: &Pointer) -> String {
    let kind = match p.kind {
        PointerKind::Box => "box",
        PointerKind::Text => "text",
        PointerKind::Env => "environment",
    };
    let mut out = format!("{kind} at {}", p.offset);
    for g in &p.guards {
        out += &match g {
            Guard::Tag { offset, tags } => {
                let tags: Vec<String> = tags.iter().map(|t| t.to_string()).collect();
                format!(" if the tag at {offset} is {}", tags.join(" or "))
            }
            Guard::NotNiche(n) => format!(" unless {}", niche_text(*n)),
        };
    }
    out
}
