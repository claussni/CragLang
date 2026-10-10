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

//! The Solid value codec (Implementation Plan §11.6.7 and §11.6.8): a
//! value as bytes, walked through the shape of its type as printing walks
//! it, and back. The bytes are canonical, so equal values give equal bytes
//! and equal hashes:
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
//! - A string or bytes: its length, eight bytes, then its bytes. A string
//!   decodes only from valid UTF-8.
//!
//! A function value or what the shape cannot show is not encoded: it holds
//! code addresses, or words whose meaning the shape does not know.
//!
//! Decoding first checks the bytes against the shapes, allocating nothing,
//! and then builds the value, so bytes that do not fit leave no boxes
//! behind. The boxes get the type indices and sizes the shapes give them.

use crag_abi::{Shape, ShapeField, Shapes, TYPE_INDEX_OFFSET};

use crate::heap::{Heap, alloc_box};
use crate::rc::Types;
use crate::text::{bytes_of, make_text};
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
        Shape::Str | Shape::Bytes => {
            // SAFETY: the words are a live string or bytes value.
            let bytes = unsafe { bytes_of(words) };
            out.extend((bytes.len() as u64).to_le_bytes());
            out.extend(bytes);
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

/// Why bytes are not a value of a shape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecodeError(pub String);

/// The words of the value the bytes encode, of the shape `shape` of
/// `shapes`, built on the heap. The caller owns the value.
///
/// # Safety
///
/// `types` describes the collections the shapes name, and the shapes give
/// each box its type index and size as code generation lays them out.
pub unsafe fn decode_value(
    bytes: &[u8],
    shapes: &Shapes,
    shape: u32,
    heap: &mut Heap,
    types: &Types,
) -> Result<Vec<u64>, DecodeError> {
    let mut d = Decoder { bytes, at: 0 };
    d.check(shapes, shape)?;
    if d.at != bytes.len() {
        return Err(DecodeError(format!(
            "{} bytes after the value",
            bytes.len() - d.at
        )));
    }
    let mut d = Decoder { bytes, at: 0 };
    // SAFETY: the bytes fit the shapes, as checked, and the caller vouches
    // for the shapes.
    Ok(unsafe { d.build(shapes, shape, heap, types) })
}

struct Decoder<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl Decoder<'_> {
    fn take<const N: usize>(&mut self) -> Result<[u8; N], DecodeError> {
        let end = self.at.checked_add(N).filter(|&e| e <= self.bytes.len());
        let Some(end) = end else {
            return Err(DecodeError("the bytes end inside the value".into()));
        };
        let taken = self.bytes[self.at..end].try_into().expect("N bytes");
        self.at = end;
        Ok(taken)
    }

    fn u32(&mut self) -> Result<u32, DecodeError> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    fn u64(&mut self) -> Result<u64, DecodeError> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    /// A length. An element takes a byte at least, unless it is a tag or
    /// `()`, so a longer collection than the bytes left is refused only
    /// when it would not fit memory either; `check` refuses the rest.
    fn len(&mut self) -> Result<usize, DecodeError> {
        let len = self.u64()?;
        match usize::try_from(len) {
            Ok(len) if len < 1 << 32 => Ok(len),
            _ => Err(DecodeError(format!("a collection of {len} elements"))),
        }
    }

    /// The next `n` bytes.
    fn bytes(&mut self, n: usize) -> Result<&[u8], DecodeError> {
        let end = self.at.checked_add(n).filter(|&e| e <= self.bytes.len());
        let Some(end) = end else {
            return Err(DecodeError("the bytes end inside the value".into()));
        };
        let taken = &self.bytes[self.at..end];
        self.at = end;
        Ok(taken)
    }

    /// Reads past a value of the shape, checking it fits.
    fn check(&mut self, shapes: &Shapes, shape: u32) -> Result<(), DecodeError> {
        let shape_of = |s: u32| {
            shapes
                .shapes
                .get(s as usize)
                .ok_or_else(|| DecodeError(format!("no shape {s}")))
        };
        let boxed = |s: u32| {
            shapes
                .boxed(s)
                .ok_or_else(|| DecodeError(format!("shape {s} has no box")))
        };
        match shape_of(shape)? {
            Shape::Unit | Shape::Tag(_) => {}
            Shape::Number(_) => {
                self.u64()?;
            }
            Shape::Union { members, words } => {
                let at = self.u32()? as usize;
                let Some(&(_, member)) = members.get(at) else {
                    return Err(DecodeError(format!("no member {at}")));
                };
                if shape_of(member)?.words() + 1 > (*words).max(1) {
                    return Err(DecodeError(format!("member {at} does not fit")));
                }
                self.check(shapes, member)?;
            }
            Shape::Record { .. } => {
                let own = self.u32()?;
                let Shape::Record { fields, .. } = shape_of(own)? else {
                    return Err(DecodeError(format!("shape {own} is no record")));
                };
                // Code reads the box as the static type, so the box's own
                // type must keep each of its fields, by name, where it is:
                // a subtype.
                if let Shape::Record {
                    fields: expected, ..
                } = shape_of(shape)?
                {
                    let kept = |e: &ShapeField| {
                        fields
                            .iter()
                            .any(|f| f.name == e.name && f.offset == e.offset && f.shape == e.shape)
                    };
                    if !expected.iter().all(kept) {
                        return Err(DecodeError(format!("shape {own} is no subtype of {shape}")));
                    }
                }
                let (_, size) = boxed(own)?;
                for f in fields {
                    let end = f.offset as u64 + 8 * u64::from(shape_of(f.shape)?.words());
                    if f.offset < crag_abi::HEADER_SIZE || f.offset % 8 != 0 || end > size.into() {
                        return Err(DecodeError(format!("field {} is outside its box", f.name)));
                    }
                    self.check(shapes, f.shape)?;
                }
            }
            &Shape::List(element) | &Shape::Set(element) => {
                boxed(shape)?;
                for _ in 0..self.len()? {
                    self.check(shapes, element)?;
                }
            }
            &Shape::Map(key, value) => {
                boxed(shape)?;
                for _ in 0..self.len()? {
                    self.check(shapes, key)?;
                    self.check(shapes, value)?;
                }
            }
            Shape::Str => {
                let n = self.len()?;
                if std::str::from_utf8(self.bytes(n)?).is_err() {
                    return Err(DecodeError("a string that is not UTF-8".into()));
                }
            }
            Shape::Bytes => {
                let n = self.len()?;
                self.bytes(n)?;
            }
            Shape::Function => return Err(DecodeError("a function value".into())),
            Shape::Opaque { name, .. } => {
                return Err(DecodeError(format!("a value of type {name}")));
            }
        }
        Ok(())
    }

    /// Builds a value of the shape from bytes `check` accepted.
    unsafe fn build(
        &mut self,
        shapes: &Shapes,
        shape: u32,
        heap: &mut Heap,
        types: &Types,
    ) -> Vec<u64> {
        let ok = "checked";
        let words = |s: u32| shapes.shapes[s as usize].words() as usize;
        match &shapes.shapes[shape as usize] {
            Shape::Unit | Shape::Tag(_) => Vec::new(),
            Shape::Number(_) => vec![self.u64().expect(ok)],
            Shape::Union { members, words: n } => {
                let (index, member) = members[self.u32().expect(ok) as usize];
                let mut out = vec![u64::from(index)];
                // SAFETY: as the caller promises.
                out.extend(unsafe { self.build(shapes, member, heap, types) });
                out.resize(*n as usize, 0);
                out
            }
            Shape::Record { .. } => {
                let own = self.u32().expect(ok);
                let Shape::Record { fields, .. } = &shapes.shapes[own as usize] else {
                    unreachable!("checked");
                };
                let (index, size) = shapes.boxed(own).expect(ok);
                let ptr = alloc_box(heap, size as usize, u64::from(index));
                for f in fields {
                    // SAFETY: as the caller promises; the field lies inside
                    // the box, as checked.
                    unsafe {
                        let value = self.build(shapes, f.shape, heap, types);
                        let at = ptr.add(f.offset as usize).cast::<u64>();
                        std::ptr::copy_nonoverlapping(value.as_ptr(), at, value.len());
                    }
                }
                vec![ptr as u64]
            }
            &Shape::List(element) => {
                let (index, _) = shapes.boxed(shape).expect(ok);
                let mut list = list::empty(heap, index);
                for _ in 0..self.len().expect(ok) {
                    // SAFETY: as the caller promises; the list is ours, and
                    // the push takes the element.
                    unsafe {
                        let mut value = self.build(shapes, element, heap, types);
                        value.resize(words(element).max(1), 0);
                        list = list::push(heap, types, list, &value);
                    }
                }
                vec![list as u64]
            }
            &Shape::Set(key) => {
                // SAFETY: as the caller promises.
                vec![unsafe { self.map(shapes, shape, key, None, heap, types) }]
            }
            &Shape::Map(key, value) => {
                // SAFETY: as the caller promises.
                vec![unsafe { self.map(shapes, shape, key, Some(value), heap, types) }]
            }
            Shape::Str | Shape::Bytes => {
                let n = self.len().expect(ok);
                let bytes = self.bytes(n).expect(ok);
                make_text(heap, &[bytes]).to_vec()
            }
            Shape::Function | Shape::Opaque { .. } => unreachable!("checked"),
        }
    }

    unsafe fn map(
        &mut self,
        shapes: &Shapes,
        shape: u32,
        key: u32,
        value: Option<u32>,
        heap: &mut Heap,
        types: &Types,
    ) -> u64 {
        let ok = "checked";
        let (index, _) = shapes.boxed(shape).expect(ok);
        let mut map = map::empty(heap, index);
        for _ in 0..self.len().expect(ok) {
            // SAFETY: as the caller promises; the map is ours, and the
            // insert takes the key and the value.
            unsafe {
                let mut k = self.build(shapes, key, heap, types);
                k.resize(2, 0);
                let mut v = match value {
                    Some(value) => self.build(shapes, value, heap, types),
                    None => Vec::new(),
                };
                v.resize(2, 0);
                map = map::insert(heap, types, map, &k, &v);
            }
        }
        map as u64
    }
}
