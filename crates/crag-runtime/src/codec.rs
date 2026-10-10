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

//! The Solid value codec's encoder (Implementation Plan §11.6.7 and
//! §11.6.8): a value as bytes, walked through the shape of its type as
//! printing walks it. The bytes are canonical, so equal values give equal
//! bytes and equal hashes:
//!
//! - `()` and a tag: nothing.
//! - A number: its word, eight bytes little-endian.
//! - A union: the member's place among the shape's members, four bytes,
//!   then the member.
//! - A record: the index of the shape of the box's own type in the table,
//!   four bytes, since the box may be one of a subtype, then its fields in
//!   the shape's order.
//! - A list: its length, eight bytes, then its elements.
//! - A map or a set: its length, then its entries in the order of their
//!   keys' bytes, each the key and then the value.
//!
//! A function value or what the shape cannot show is not encoded: it holds
//! code addresses, or words whose meaning the shape does not know.

use crag_abi::{Shape, Shapes, TYPE_INDEX_OFFSET};

use crate::rc::Types;
use crate::{list, map};

/// What a value held that has no encoding, by its type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NotSolid(pub String);

/// The bytes of a value: its words, of the shape `shape` of `shapes`.
///
/// # Safety
///
/// The words are a live value of the shape, and `types` describes its
/// collections.
pub unsafe fn encode_value(
    words: &[u64],
    shapes: &Shapes,
    shape: u32,
    types: &Types,
) -> Result<Vec<u8>, NotSolid> {
    let mut out = Vec::new();
    // SAFETY: as the caller promises.
    unsafe { encode(words, shapes, shape, types, &mut out)? };
    Ok(out)
}

unsafe fn encode(
    words: &[u64],
    shapes: &Shapes,
    shape: u32,
    types: &Types,
    out: &mut Vec<u8>,
) -> Result<(), NotSolid> {
    let word = words.first().copied().unwrap_or(0);
    match &shapes.shapes[shape as usize] {
        Shape::Unit | Shape::Tag(_) => {}
        Shape::Number(_) => out.extend(word.to_le_bytes()),
        Shape::Union { members, words: n } => {
            let Some(at) = members.iter().position(|m| u64::from(m.0) == word) else {
                return Err(NotSolid(format!("a member of type {word}")));
            };
            out.extend((at as u32).to_le_bytes());
            // SAFETY: the payload is the member's.
            unsafe { encode(&words[1..*n as usize], shapes, members[at].1, types, out)? };
        }
        Shape::Record { .. } => {
            let ptr = word as *const u8;
            // SAFETY: the word points at a live box of a record type.
            let index = unsafe { ptr.offset(TYPE_INDEX_OFFSET as isize).cast::<u32>().read() };
            let own = shapes.record(index).unwrap_or(shape);
            let Shape::Record { fields, .. } = &shapes.shapes[own as usize] else {
                return Err(NotSolid(format!("a box of type {index}")));
            };
            out.extend(own.to_le_bytes());
            for f in fields {
                let n = shapes.shapes[f.shape as usize].words() as usize;
                // SAFETY: the field's words are at its offset.
                unsafe {
                    let at = ptr.add(f.offset as usize).cast::<u64>();
                    encode(
                        std::slice::from_raw_parts(at, n),
                        shapes,
                        f.shape,
                        types,
                        out,
                    )?;
                }
            }
        }
        &Shape::List(element) => {
            let list = word as *mut u8;
            let n = shapes.shapes[element as usize].words() as usize;
            // SAFETY: a live list of the element's shape.
            let len = unsafe { list::length(list) };
            out.extend((len as u64).to_le_bytes());
            for i in 0..len {
                // SAFETY: as above; the index is inside the list.
                unsafe {
                    let at = list::get(types, list, i);
                    encode(
                        std::slice::from_raw_parts(at, n),
                        shapes,
                        element,
                        types,
                        out,
                    )?;
                }
            }
        }
        &Shape::Set(key) => {
            // SAFETY: a live set of the key's shape.
            unsafe { entries(word, shapes, key, None, types, out)? }
        }
        &Shape::Map(key, value) => {
            // SAFETY: a live map of the shapes.
            unsafe { entries(word, shapes, key, Some(value), types, out)? }
        }
        Shape::Function => return Err(NotSolid("a function value".into())),
        Shape::Opaque { name, .. } => return Err(NotSolid(format!("a value of type {name}"))),
    }
    Ok(())
}

/// The entries of a map, or of a set without values, in the order of
/// their keys' bytes.
unsafe fn entries(
    word: u64,
    shapes: &Shapes,
    key: u32,
    value: Option<u32>,
    types: &Types,
    out: &mut Vec<u8>,
) -> Result<(), NotSolid> {
    let kw = shapes.shapes[key as usize].words() as usize;
    let vw = value.map_or(0, |v| shapes.shapes[v as usize].words() as usize);
    let mut encoded = Vec::new();
    // SAFETY: as the caller promises; each entry is its key's words, then
    // its value's.
    unsafe {
        for at in map::iter(types, word as *mut u8) {
            let e = std::slice::from_raw_parts(at, kw + vw);
            let mut k = Vec::new();
            encode(&e[..kw], shapes, key, types, &mut k)?;
            let mut v = Vec::new();
            if let Some(value) = value {
                encode(&e[kw..], shapes, value, types, &mut v)?;
            }
            encoded.push((k, v));
        }
    }
    encoded.sort();
    out.extend((encoded.len() as u64).to_le_bytes());
    for (k, v) in encoded {
        out.extend(k);
        out.extend(v);
    }
    Ok(())
}
