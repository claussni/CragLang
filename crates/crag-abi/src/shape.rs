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

//! Shapes (Implementation Plan §11.6.5): how a value of a type is laid
//! out for printing and storing, its words and what they point to, and
//! the stored form a value narrows to and widens from.

use crate::{FUNCTION_BOX_HEADER, TEXT_BOX_HEADER, wire};

/// How a value of a type is printed (Implementation Plan §11.6.5): what
/// its words are and what they point to. The host describes the type; the
/// image walks the value. A type that contains itself refers back to its
/// shape by index, so a shape is a table.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct Shapes {
    pub shapes: Vec<Shape>,
    /// The shapes of the record types a box may have, by the type index
    /// in its header: a value of a record type may be one of a subtype.
    pub records: Vec<(u32, u32)>,
    /// For each shape of a box, a record, a list, a set or a map: the
    /// shape, the type index in the box's header and the box's bytes, so
    /// a value can be built from its encoding (§11.6.8).
    pub boxes: Vec<(u32, u32, u32)>,
    /// For each shape of a Plain type, in a box or split, the `Stored`
    /// shape of its storage form, which the codec writes it in (Compiler
    /// Architecture §A11.4).
    pub plain: Vec<(u32, u32)>,
    /// For each shape of a box of a named record type, the hash of the
    /// type's canonical form (Compiler Architecture §A11.2), by which the
    /// codec names the type of a box: every program agrees on it.
    pub identities: Vec<(u32, [u8; 16])>,
}

impl Shapes {
    /// The shape of a record by the type index of its box, if known.
    pub fn record(&self, index: u32) -> Option<u32> {
        self.records.iter().find(|r| r.0 == index).map(|r| r.1)
    }

    /// The type index and the bytes of the boxes of a shape, if known.
    pub fn boxed(&self, shape: u32) -> Option<(u32, u32)> {
        self.boxes
            .iter()
            .find(|b| b.0 == shape)
            .map(|&(_, index, size)| (index, size))
    }

    /// The `Stored` shape of the storage form of a shape of a Plain type,
    /// if it is one.
    pub fn plain(&self, shape: u32) -> Option<u32> {
        self.plain.iter().find(|p| p.0 == shape).map(|p| p.1)
    }

    /// The identity of the named record type of a shape's boxes, if known.
    pub fn identity(&self, shape: u32) -> Option<[u8; 16]> {
        self.identities.iter().find(|i| i.0 == shape).map(|i| i.1)
    }

    /// The shape of the boxes of the named record type of an identity, if
    /// known.
    pub fn by_identity(&self, identity: [u8; 16]) -> Option<u32> {
        self.identities
            .iter()
            .find(|i| i.1 == identity)
            .map(|i| i.0)
    }

    /// The table as bytes, as the session protocol sends it and generated
    /// code keeps it for the runtime's value functions.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        let u32 = |out: &mut Vec<u8>, n: u32| out.extend_from_slice(&n.to_le_bytes());
        let text = |out: &mut Vec<u8>, t: &str| {
            u32(out, t.len() as u32);
            out.extend_from_slice(t.as_bytes());
        };
        u32(&mut out, self.shapes.len() as u32);
        for shape in &self.shapes {
            match shape {
                Shape::Unit => out.push(0),
                Shape::Tag(name) => {
                    out.push(1);
                    text(&mut out, name);
                }
                Shape::Number(n) => {
                    out.push(2);
                    match n {
                        Number::Signed => out.push(0),
                        Number::Unsigned => out.push(1),
                        Number::Float => out.push(2),
                        Number::Fixed(digits) => {
                            out.push(3);
                            u32(&mut out, *digits);
                        }
                        Number::CodePoint => out.push(4),
                    }
                }
                Shape::Union { members, words } | Shape::Variant { members, words } => {
                    out.push(match shape {
                        Shape::Union { .. } => 3,
                        _ => 13,
                    });
                    u32(&mut out, members.len() as u32);
                    for &(index, shape) in members {
                        u32(&mut out, index);
                        u32(&mut out, shape);
                    }
                    u32(&mut out, *words);
                }
                Shape::Record { name, fields } | Shape::Inline { name, fields, .. } => {
                    out.push(match shape {
                        Shape::Record { .. } => 4,
                        _ => 12,
                    });
                    match name {
                        None => out.push(0),
                        Some(name) => {
                            out.push(1);
                            text(&mut out, name);
                        }
                    }
                    u32(&mut out, fields.len() as u32);
                    for f in fields {
                        text(&mut out, &f.name);
                        u32(&mut out, f.offset);
                        u32(&mut out, f.shape);
                    }
                    if let Shape::Inline { words, .. } = shape {
                        u32(&mut out, *words);
                    }
                }
                Shape::List(element) => {
                    out.push(5);
                    u32(&mut out, *element);
                }
                Shape::Set(element) => {
                    out.push(6);
                    u32(&mut out, *element);
                }
                Shape::Map(key, value) => {
                    out.push(7);
                    u32(&mut out, *key);
                    u32(&mut out, *value);
                }
                Shape::Function => out.push(8),
                Shape::Opaque { name, words } => {
                    out.push(9);
                    text(&mut out, name);
                    u32(&mut out, *words);
                }
                Shape::Str => out.push(10),
                Shape::Bytes => out.push(11),
                Shape::Stored {
                    form,
                    size,
                    slots,
                    words,
                } => {
                    out.push(14);
                    u32(&mut out, *form);
                    u32(&mut out, *size);
                    stored_slots(&mut out, slots);
                    u32(&mut out, *words);
                }
            }
        }
        u32(&mut out, self.records.len() as u32);
        for &(index, shape) in &self.records {
            u32(&mut out, index);
            u32(&mut out, shape);
        }
        u32(&mut out, self.boxes.len() as u32);
        for &(shape, index, size) in &self.boxes {
            u32(&mut out, shape);
            u32(&mut out, index);
            u32(&mut out, size);
        }
        u32(&mut out, self.plain.len() as u32);
        for &(shape, stored) in &self.plain {
            u32(&mut out, shape);
            u32(&mut out, stored);
        }
        u32(&mut out, self.identities.len() as u32);
        for &(shape, identity) in &self.identities {
            u32(&mut out, shape);
            out.extend_from_slice(&identity);
        }
        out
    }

    /// The table `encode` wrote, checked: every shape a shape names is in
    /// it.
    pub fn decode(bytes: &[u8]) -> Result<Shapes, String> {
        let mut r = ShapeReader::new(bytes);
        let shapes = Shapes {
            shapes: r.seq(ShapeReader::shape)?,
            records: r.seq(|r| Ok((r.u32()?, r.u32()?)))?,
            boxes: r.seq(|r| Ok((r.u32()?, r.u32()?, r.u32()?)))?,
            plain: r.seq(|r| Ok((r.u32()?, r.u32()?)))?,
            identities: r.seq(|r| {
                let shape = r.u32()?;
                let mut identity = [0; 16];
                identity[..8].copy_from_slice(&r.u64()?.to_le_bytes());
                identity[8..].copy_from_slice(&r.u64()?.to_le_bytes());
                Ok((shape, identity))
            })?,
        };
        if !r.is_empty() {
            return Err("bytes after the shapes".into());
        }
        let n = shapes.shapes.len() as u32;
        let inside = |i: &u32| *i < n;
        let named = shapes.shapes.iter().all(|s| match s {
            Shape::Union { members, .. } | Shape::Variant { members, .. } => {
                members.iter().map(|m| &m.1).all(inside)
            }
            Shape::Record { fields, .. } | Shape::Inline { fields, .. } => {
                fields.iter().map(|f| &f.shape).all(inside)
            }
            Shape::List(e) | Shape::Set(e) | Shape::Stored { form: e, .. } => inside(e),
            Shape::Map(k, v) => inside(k) && inside(v),
            _ => true,
        });
        if !named
            || !shapes.records.iter().map(|r| &r.1).all(inside)
            || !shapes.boxes.iter().map(|b| &b.0).all(inside)
            || !shapes.identities.iter().map(|i| &i.0).all(inside)
            || !shapes.plain.iter().all(|p| {
                inside(&p.0)
                    && matches!(shapes.shapes.get(p.1 as usize), Some(Shape::Stored { .. }))
            })
        {
            return Err("a shape that names no shape of its table".into());
        }
        Ok(shapes)
    }
}

/// Reads what `Shapes::encode` wrote.
type ShapeReader<'a> = wire::Reader<'a, String>;

/// What a shape table holds beyond `wire`'s bytes.
trait ReadShape {
    fn shape(&mut self) -> Result<Shape, String>;
    fn slots(&mut self) -> Result<Vec<StoredSlot>, String>;
}

impl ReadShape for ShapeReader<'_> {
    fn shape(&mut self) -> Result<Shape, String> {
        Ok(match self.u8()? {
            0 => Shape::Unit,
            1 => Shape::Tag(self.text()?),
            2 => Shape::Number(match self.u8()? {
                0 => Number::Signed,
                1 => Number::Unsigned,
                2 => Number::Float,
                3 => Number::Fixed(self.u32()?),
                4 => Number::CodePoint,
                tag => return Err(format!("a number with the tag {tag}")),
            }),
            3 => Shape::Union {
                members: self.seq(|r| Ok((r.u32()?, r.u32()?)))?,
                words: self.u32()?,
            },
            13 => Shape::Variant {
                members: self.seq(|r| Ok((r.u32()?, r.u32()?)))?,
                words: self.u32()?,
            },
            4 => Shape::Record {
                name: match self.u8()? {
                    0 => None,
                    1 => Some(self.text()?),
                    tag => return Err(format!("an option with the tag {tag}")),
                },
                fields: self.seq(|r| {
                    Ok(ShapeField {
                        name: r.text()?,
                        offset: r.u32()?,
                        shape: r.u32()?,
                    })
                })?,
            },
            5 => Shape::List(self.u32()?),
            6 => Shape::Set(self.u32()?),
            7 => Shape::Map(self.u32()?, self.u32()?),
            8 => Shape::Function,
            9 => Shape::Opaque {
                name: self.text()?,
                words: self.u32()?,
            },
            10 => Shape::Str,
            11 => Shape::Bytes,
            12 => Shape::Inline {
                name: match self.u8()? {
                    0 => None,
                    1 => Some(self.text()?),
                    tag => return Err(format!("an option with the tag {tag}")),
                },
                fields: self.seq(|r| {
                    Ok(ShapeField {
                        name: r.text()?,
                        offset: r.u32()?,
                        shape: r.u32()?,
                    })
                })?,
                words: self.u32()?,
            },
            14 => Shape::Stored {
                form: self.u32()?,
                size: self.u32()?,
                slots: self.slots()?,
                words: self.u32()?,
            },
            tag => return Err(format!("a shape with the tag {tag}")),
        })
    }

    fn slots(&mut self) -> Result<Vec<StoredSlot>, String> {
        self.seq(|r| {
            Ok(StoredSlot {
                at: r.u32()?,
                offset: r.u32()?,
                size: r.u32()?,
                bits: match r.u8()? {
                    0 => None,
                    _ => Some((r.u8()?, r.u8()?)),
                },
                kind: match r.u8()? {
                    0 => StoredKind::Int {
                        signed: r.u8()? != 0,
                    },
                    1 => StoredKind::Words,
                    2 => StoredKind::Tag(r.seq(ShapeReader::u32)?),
                    3 => StoredKind::Union {
                        tag: match r.u8()? {
                            0 => StoredTag::Bytes {
                                offset: r.u32()?,
                                size: r.u32()?,
                            },
                            1 => StoredTag::Niche {
                                empty: r.u32()?,
                                offset: r.u32()?,
                                size: r.u8()?,
                                value: r.u64()?,
                            },
                            tag => return Err(format!("a union tag with the tag {tag}")),
                        },
                        members: r.seq(|r| Ok((r.u32()?, r.slots()?)))?,
                    },
                    tag => return Err(format!("a stored slot with the tag {tag}")),
                },
            })
        })
    }
}

/// Writes the slots of a stored shape, as `ReadShape::slots` reads them.
fn stored_slots(out: &mut Vec<u8>, slots: &[StoredSlot]) {
    let u32 = |out: &mut Vec<u8>, n: u32| out.extend_from_slice(&n.to_le_bytes());
    u32(out, slots.len() as u32);
    for slot in slots {
        u32(out, slot.at);
        u32(out, slot.offset);
        u32(out, slot.size);
        match slot.bits {
            None => out.push(0),
            Some((bit, width)) => out.extend([1, bit, width]),
        }
        match &slot.kind {
            StoredKind::Int { signed } => out.extend([0, u8::from(*signed)]),
            StoredKind::Words => out.push(1),
            StoredKind::Tag(members) => {
                out.push(2);
                u32(out, members.len() as u32);
                for &m in members {
                    u32(out, m);
                }
            }
            StoredKind::Union { tag, members } => {
                out.push(3);
                match *tag {
                    StoredTag::Bytes { offset, size } => {
                        out.push(0);
                        u32(out, offset);
                        u32(out, size);
                    }
                    StoredTag::Niche {
                        empty,
                        offset,
                        size,
                        value,
                    } => {
                        out.push(1);
                        u32(out, empty);
                        u32(out, offset);
                        out.push(size);
                        out.extend_from_slice(&value.to_le_bytes());
                    }
                }
                u32(out, members.len() as u32);
                for (index, member) in members {
                    u32(out, *index);
                    stored_slots(out, member);
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// `()`: no words.
    Unit,
    /// A tag, by its name: no words.
    Tag(String),
    /// A word.
    Number(Number),
    /// A union: the type index of the member, then in a two-word union the
    /// member's word, which for a member of two words points at the member
    /// box that holds them. Each member by its type index.
    Union {
        members: Vec<(u32, u32)>,
        words: u32,
    },
    /// A box of a record type, named or anonymous, whose fields are at
    /// their offsets in it, in the order they are shown.
    Record {
        name: Option<String>,
        fields: Vec<ShapeField>,
    },
    /// A box of a list or a set: the element's shape.
    List(u32),
    Set(u32),
    /// A box of a map: the shapes of key and value.
    Map(u32, u32),
    /// A function value: two words.
    Function,
    /// A string or bytes value: two words.
    Str,
    Bytes,
    /// What cannot be shown yet, by its type, and its words.
    Opaque {
        name: String,
        words: u32,
    },
    /// A record split into registers (Implementation Plan §11.10.10): its
    /// fields' words one after another, each field's offset the index of
    /// its first word, in the order they are shown.
    Inline {
        name: Option<String>,
        fields: Vec<ShapeField>,
        words: u32,
    },
    /// A union split into registers: the type index of the member, then
    /// the member's own words, a record's inline. Each member by its type
    /// index.
    Variant {
        members: Vec<(u32, u32)>,
        words: u32,
    },
    /// A field of a box, or an element of a collection, stored flat
    /// (Compiler Architecture §A11.4): the `size` bytes at its offset, or
    /// the element's, hold, as `slots` say, the words of a value of the
    /// shape `form`.
    Stored {
        form: u32,
        size: u32,
        slots: Vec<StoredSlot>,
        words: u32,
    },
}

/// Where a value of a register form is in a storage form (Compiler
/// Architecture §A11.4): the word it starts at, and how bytes or bits hold
/// it from `offset` on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct StoredSlot {
    pub at: u32,
    pub offset: u32,
    pub size: u32,
    /// Its first bit and width in the byte at `offset`.
    pub bits: Option<(u8, u8)>,
    pub kind: StoredKind,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StoredKind {
    /// An integer of `size` bytes, extended with its sign or with zeros.
    Int { signed: bool },
    /// Words as they are.
    Words,
    /// A union of tags: its local tag, which numbers the members whose
    /// type indices these are.
    Tag(Vec<u32>),
    /// A union whose word at `at` holds its member's type index: how
    /// storage tells the member, and each member's type index and slots.
    Union {
        tag: StoredTag,
        members: Vec<(u32, Vec<StoredSlot>)>,
    },
}

/// How the storage form of a union tells its member.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum StoredTag {
    /// The member's local tag in `size` bytes at `offset`.
    Bytes { offset: u32, size: u32 },
    /// The member `empty`, of no words, is the other's niche: `size` bytes
    /// at `offset` that hold `value`, or with `size` zero, the bit `value`
    /// of the byte there set.
    Niche {
        empty: u32,
        offset: u32,
        size: u8,
        value: u64,
    },
}

/// The `size` bytes at `offset`, little-endian.
pub(crate) fn read_le(bytes: &[u8], offset: u32, size: u32) -> u64 {
    let mut out = [0u8; 8];
    let (from, n) = (offset as usize, size as usize);
    out[..n].copy_from_slice(&bytes[from..from + n]);
    u64::from_le_bytes(out)
}

/// The low `width` bits of `value` put at bit `bit` of the bytes from
/// `offset` on, which hold zeros there.
fn or_le(bytes: &mut [u8], offset: u32, bit: u32, width: u32, value: u64) {
    let value = match width {
        64 => value,
        w => value & ((1u64 << w) - 1),
    };
    let wide = u128::from(value) << bit;
    let n = (bit + width).div_ceil(8) as usize;
    for (k, b) in wide.to_le_bytes()[..n].iter().enumerate() {
        bytes[offset as usize + k] |= b;
    }
}

impl StoredTag {
    /// The index of the member the bytes hold.
    fn member(&self, bytes: &[u8]) -> usize {
        match *self {
            StoredTag::Bytes { offset, size } => read_le(bytes, offset, size) as usize,
            StoredTag::Niche {
                empty,
                offset,
                size,
                value,
            } => {
                let niche = match size {
                    0 => u64::from(bytes[offset as usize] >> value & 1) == 1,
                    size => read_le(bytes, offset, u32::from(size)) == value,
                };
                match niche {
                    true => empty as usize,
                    false => 1 - empty as usize,
                }
            }
        }
    }
}

/// Puts the register form of a value stored as `slots` in `bytes` into
/// `out`, as generated code loads it.
pub fn widen(slots: &[StoredSlot], bytes: &[u8], out: &mut [u64]) {
    for slot in slots {
        let at = slot.at as usize;
        match &slot.kind {
            StoredKind::Words => {
                for k in 0..(slot.size / 8) {
                    out[at + k as usize] = read_le(bytes, slot.offset + 8 * k, 8);
                }
            }
            StoredKind::Int { signed } => {
                let raw = read_le(bytes, slot.offset, slot.size);
                let unused = 64 - 8 * slot.size;
                out[at] = match (signed, unused) {
                    (_, 0) | (false, _) => raw,
                    (true, _) => ((raw << unused) as i64 >> unused) as u64,
                };
            }
            StoredKind::Tag(members) => {
                let tag = match slot.bits {
                    Some((bit, width)) => {
                        u64::from(bytes[slot.offset as usize] >> bit) & ((1 << width) - 1)
                    }
                    None => read_le(bytes, slot.offset, slot.size),
                };
                out[at] = members.get(tag as usize).copied().map_or(0, u64::from);
            }
            StoredKind::Union { tag, members } => {
                let Some((index, member)) = members.get(tag.member(bytes)) else {
                    continue;
                };
                out[at] = u64::from(*index);
                widen(member, bytes, out);
            }
        }
    }
}

/// Puts the register form of a value in `words` into `bytes` as `slots`
/// store it, as generated code stores it. The bytes the slots take hold
/// zeros before.
pub fn narrow(slots: &[StoredSlot], words: &[u64], bytes: &mut [u8]) {
    for slot in slots {
        let at = slot.at as usize;
        match &slot.kind {
            StoredKind::Words => {
                for k in 0..(slot.size / 8) {
                    or_le(bytes, slot.offset + 8 * k, 0, 64, words[at + k as usize]);
                }
            }
            StoredKind::Int { .. } => or_le(bytes, slot.offset, 0, 8 * slot.size, words[at]),
            StoredKind::Tag(members) => {
                let tag = members
                    .iter()
                    .position(|&m| u64::from(m) == words[at])
                    .unwrap_or(0) as u64;
                match slot.bits {
                    Some((bit, width)) => or_le(bytes, slot.offset, bit.into(), width.into(), tag),
                    None => or_le(bytes, slot.offset, 0, 8 * slot.size, tag),
                }
            }
            StoredKind::Union { tag, members } => {
                let Some(k) = members.iter().position(|m| u64::from(m.0) == words[at]) else {
                    continue;
                };
                match *tag {
                    StoredTag::Bytes { offset, size } => {
                        or_le(bytes, offset, 0, 8 * size, k as u64)
                    }
                    StoredTag::Niche {
                        empty,
                        offset,
                        size: 0,
                        value,
                    } if empty as usize == k => or_le(bytes, offset, value as u32, 1, 1),
                    StoredTag::Niche {
                        empty,
                        offset,
                        size,
                        value,
                    } if empty as usize == k => or_le(bytes, offset, 0, 8 * u32::from(size), value),
                    StoredTag::Niche { .. } => {}
                }
                narrow(&members[k].1, words, bytes);
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ShapeField {
    pub name: String,
    pub offset: u32,
    pub shape: u32,
}

/// How a word holds a number.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Number {
    /// A signed integer, sign-extended.
    Signed,
    /// An unsigned integer, zero-extended.
    Unsigned,
    /// The bits of a `Float`.
    Float,
    /// A `Fixed` with this many digits after the point, scaled.
    Fixed(u32),
    CodePoint,
}

impl Number {
    /// The number as one word, for `rt_text_show`.
    pub fn code(self) -> u64 {
        match self {
            Number::Signed => 0,
            Number::Unsigned => 1,
            Number::Float => 2,
            Number::CodePoint => 3,
            Number::Fixed(digits) => 4 + u64::from(digits),
        }
    }

    /// The number of a code, if any.
    pub fn from_code(code: u64) -> Option<Number> {
        Some(match code {
            0 => Number::Signed,
            1 => Number::Unsigned,
            2 => Number::Float,
            3 => Number::CodePoint,
            _ => Number::Fixed(u32::try_from(code.checked_sub(4)?).ok()?),
        })
    }
}

impl Shape {
    /// The words of a value of the shape.
    pub fn words(&self) -> u32 {
        match self {
            Shape::Unit | Shape::Tag(_) => 0,
            Shape::Number(_)
            | Shape::Record { .. }
            | Shape::List(_)
            | Shape::Set(_)
            | Shape::Map(..) => 1,
            Shape::Union { words, .. }
            | Shape::Opaque { words, .. }
            | Shape::Inline { words, .. }
            | Shape::Variant { words, .. }
            | Shape::Stored { words, .. } => *words,
            Shape::Function | Shape::Str | Shape::Bytes => 2,
        }
    }

    /// The words a value of the shape takes in a collection: a stored
    /// one's storage form, which `widen` turns into its `words`.
    pub fn element_words(&self) -> u32 {
        match self {
            Shape::Stored { size, .. } => size.div_ceil(8),
            shape => shape.words(),
        }
    }

    /// The type index word of the member box that holds a value of the
    /// shape in a union; none for a shape of fewer than two words, which
    /// a union holds as it is.
    pub fn member_box(&self) -> Option<u64> {
        match self {
            Shape::Str | Shape::Bytes => Some(TEXT_BOX_HEADER),
            Shape::Function => Some(FUNCTION_BOX_HEADER),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FieldGuard;

    #[test]
    fn stored_values_widen_to_what_they_narrowed_from() {
        let slot = |at, offset, size, bits, kind| StoredSlot {
            at,
            offset,
            size,
            bits,
            kind,
        };
        let slots = vec![
            slot(0, 0, 1, None, StoredKind::Int { signed: false }),
            slot(1, 1, 1, Some((0, 1)), StoredKind::Tag(vec![7, 8])),
            slot(2, 1, 1, Some((1, 2)), StoredKind::Tag(vec![9, 10, 11])),
            slot(3, 2, 2, None, StoredKind::Int { signed: true }),
            slot(
                4,
                4,
                12,
                None,
                StoredKind::Union {
                    tag: StoredTag::Bytes { offset: 4, size: 1 },
                    members: vec![
                        (20, vec![slot(5, 8, 8, None, StoredKind::Words)]),
                        (21, vec![]),
                    ],
                },
            ),
            slot(
                6,
                16,
                2,
                None,
                StoredKind::Union {
                    tag: StoredTag::Niche {
                        empty: 1,
                        offset: 16,
                        size: 2,
                        value: 0,
                    },
                    members: vec![
                        (
                            30,
                            vec![slot(7, 16, 2, None, StoredKind::Int { signed: true })],
                        ),
                        (31, vec![]),
                    ],
                },
            ),
        ];
        for words in [
            [
                200,
                8,
                11,
                -5i64 as u64,
                20,
                0xdead_beef,
                30,
                -1234i64 as u64,
            ],
            [0, 7, 9, 5, 21, 0, 31, 0],
        ] {
            let mut bytes = [0u8; 24];
            narrow(&slots, &words, &mut bytes);
            let mut out = [0u64; 8];
            widen(&slots, &bytes, &mut out);
            assert_eq!(out, words);
        }
        let mut bytes = [0u8; 24];
        narrow(&slots, &[0, 7, 9, 0, 20, 0, 31, 0], &mut bytes);
        assert!(
            FieldGuard::Tag {
                offset: 4,
                tags: vec![0]
            }
            .holds(&bytes)
        );
        assert!(
            !FieldGuard::NotValue {
                offset: 16,
                size: 2,
                value: 0
            }
            .holds(&bytes)
        );
        assert!(FieldGuard::BitClear { offset: 1, bit: 0 }.holds(&bytes));
    }
}
