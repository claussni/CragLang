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

//! The memcomparable key encoding (Implementation Plan §11.11.6,
//! Specification §21.5): a `Storable`, `Ordered` value as bytes whose
//! unsigned byte order is the order of `compare`, so slot range queries
//! follow the key type. The format is in the style of the FoundationDB
//! tuple layer, walked through the shape of the type as the codec walks
//! it. The slot table (Plan §11.11.7) writes the key type's identity
//! before these bytes, so keys of different types never collide.
//!
//! - `()` and a tag: nothing.
//! - A signed integer, or a `Fixed`: eight bytes big-endian with the
//!   sign bit flipped. Unsigned integers and code points: big-endian.
//! - A `Float`: its bits, all flipped for a negative, only the sign bit
//!   for the rest; `-0.0` is written as `0.0`, since they compare
//!   `Equal` and equal keys must encode alike (§21.5).
//! - A string or bytes: the bytes with `0x00` escaped as `0x00 0xFF`,
//!   then a `0x00` terminator.
//! - A union: the member's place among the shape's members, four bytes
//!   big-endian, then the member; `compare` orders members the same way.
//! - A record: the box's own type index, four bytes big-endian, since
//!   the box may be one of a subtype and `compare` orders subtypes by
//!   it; then its fields in declaration order. A record split into
//!   registers has no subtypes and writes its fields alone.
//! - A list: `0x01` before each element and `0x00` after the last, so a
//!   list orders by its elements first and its length last, as
//!   `compare` orders it.
//! - A map, a set, a function or an opaque value has no structural
//!   order, as `compare` has none, so it cannot be a key.

use crag_abi::{Number, Shape, Shapes};

use crate::list;
use crate::print::{field_words, member_words};
use crate::rc::Types;
use crate::text::bytes_of;
use crate::values::box_index;

/// Why a value cannot be a key: the part of its type that `compare` does
/// not order.
#[derive(Debug)]
pub struct Unkeyable(pub String);

/// Writes a value of the shape as memcomparable bytes: for values `a`
/// and `b` of one shape, the unsigned byte order of their encodings is
/// exactly the order of `compare` (§4.7, §21.5).
///
/// # Safety
///
/// The words are a live value of the shape of `shapes`, which the caller
/// holds.
pub unsafe fn encode_key(
    words: &[u64],
    shapes: &Shapes,
    types: &Types,
    shape: u32,
    out: &mut Vec<u8>,
) -> Result<(), Unkeyable> {
    let at = |s: u32| &shapes.shapes[s as usize];
    // SAFETY: as the caller promises, for every part walked.
    unsafe {
        match at(shape) {
            Shape::Unit | Shape::Tag(_) => {}
            Shape::Number(n) => match n {
                Number::Unsigned | Number::CodePoint => out.extend(words[0].to_be_bytes()),
                Number::Signed | Number::Fixed(_) => {
                    out.extend((words[0] ^ (1 << 63)).to_be_bytes());
                }
                Number::Float => {
                    // `-0.0 + 0.0` is `0.0`, which keeps equal keys alike.
                    let bits = (f64::from_bits(words[0]) + 0.0).to_bits();
                    let flipped = match bits >> 63 {
                        0 => bits ^ (1 << 63),
                        _ => !bits,
                    };
                    out.extend(flipped.to_be_bytes());
                }
            },
            Shape::Str | Shape::Bytes => {
                for &byte in bytes_of(words) {
                    out.push(byte);
                    if byte == 0 {
                        out.push(0xff);
                    }
                }
                out.push(0);
            }
            Shape::Union { members, words: n } => {
                let place = members.iter().position(|m| u64::from(m.0) == words[0]);
                let Some(place) = place else {
                    return Err(Unkeyable("a union member the shape does not know".into()));
                };
                out.extend((place as u32).to_be_bytes());
                let (_, m) = members[place];
                let payload = member_words(&words[1..*n as usize], at(m));
                encode_key(payload, shapes, types, m, out)?;
            }
            Shape::Variant { members, .. } => {
                let place = members.iter().position(|m| u64::from(m.0) == words[0]);
                let Some(place) = place else {
                    return Err(Unkeyable("a union member the shape does not know".into()));
                };
                out.extend((place as u32).to_be_bytes());
                let (_, m) = members[place];
                let n = at(m).words() as usize;
                encode_key(&words[1..1 + n], shapes, types, m, out)?;
            }
            Shape::Record { .. } => {
                let ptr = words[0] as *const u8;
                let index = box_index(ptr);
                out.extend(index.to_be_bytes());
                let own = shapes.record(index).unwrap_or(shape);
                let Shape::Record { fields, .. } = at(own) else {
                    return Err(Unkeyable("a record box of no record shape".into()));
                };
                for f in fields {
                    let (words, s) = field_words(shapes, ptr, f);
                    encode_key(&words, shapes, types, s, out)?;
                }
            }
            Shape::Inline { fields, .. } => {
                for f in fields {
                    let (at, n) = (f.offset as usize, shapes.shapes[f.shape as usize].words());
                    encode_key(&words[at..at + n as usize], shapes, types, f.shape, out)?;
                }
            }
            Shape::List(element) => {
                let ptr = words[0] as *mut u8;
                for i in 0..list::length(ptr) {
                    out.push(1);
                    let at = list::get(types, ptr, i);
                    let (words, s) = crate::print::value_at(shapes, at.cast(), *element);
                    encode_key(&words, shapes, types, s, out)?;
                }
                out.push(0);
            }
            Shape::Set(_) | Shape::Map(..) => {
                return Err(Unkeyable("a map or a set has no order".into()));
            }
            Shape::Function => {
                return Err(Unkeyable("a function has no order".into()));
            }
            Shape::Opaque { name, .. } => {
                return Err(Unkeyable(format!("the opaque type {name} has no order")));
            }
            Shape::Stored { .. } => {
                return Err(Unkeyable("a storage form stands in no key".into()));
            }
        }
    }
    Ok(())
}
