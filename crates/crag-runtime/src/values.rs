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

//! Equality, order, hashing and showing of any value by the shape of its
//! type (Specification §19.11): what the prelude's generic `equals`,
//! `compare`, `hash` and `show` call for a type without its own.
//!
//! Generated code keeps a type's shapes as bytes and turns them into a
//! handle once per call site run; the tables are decoded once for each
//! distinct table and kept for the process.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::sync::Mutex;

use crag_abi::value_op::{COMPARE, EQUALS, UNORDERED};
use crag_abi::{Number, Shape, Shapes, TYPE_INDEX_OFFSET};

use crate::fiber::TaskContext;
use crate::print::{PrintLimits, member_words, print_value};
use crate::rc::Types;
use crate::system::worker_of;
use crate::text::{TextWords, bytes_of, make_text};
use crate::{die, list, map};

/// A decoded table and its root shape.
struct Table {
    shapes: Shapes,
    root: u32,
}

/// The tables by their bytes, and by handle.
struct Tables {
    by_bytes: HashMap<Vec<u8>, u32>,
    tables: Vec<&'static Table>,
}

static TABLES: Mutex<Option<Tables>> = Mutex::new(None);

fn table(handle: u64) -> &'static Table {
    let tables = TABLES.lock().unwrap_or_else(|e| e.into_inner());
    match tables.as_ref().and_then(|t| t.tables.get(handle as usize)) {
        Some(table) => table,
        None => die("a value operation without its shapes"),
    }
}

system_stack_fn! {
    /// `rt_value_shapes(ctx, w0, w1)`: see `crag_abi::RuntimeFn::ValueShapes`.
    fn rt_value_shapes(ctx: *const TaskContext, w0: u64, w1: u64) -> u64 => shapes_entry
}

system_stack_fn! {
    /// `rt_value_op(ctx, packed, a0, a1, b0, b1)`: see
    /// `crag_abi::RuntimeFn::ValueOp`.
    fn rt_value_op(ctx: *const TaskContext, packed: u64, a0: u64, a1: u64, b0: u64, b1: u64) -> u64
        => op_entry
}

system_stack_fn! {
    /// `rt_value_show(ctx, handle, w0, w1)`: see
    /// `crag_abi::RuntimeFn::ValueShow`.
    fn rt_value_show(ctx: *const TaskContext, handle: u64, w0: u64, w1: u64) -> TextWords
        => show_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with live values of the table's root
/// shape that the caller holds.
unsafe extern "C" fn shapes_entry(_ctx: *const TaskContext, w0: u64, w1: u64) -> u64 {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    let mut tables = TABLES.lock().unwrap_or_else(|e| e.into_inner());
    let tables = tables.get_or_insert_with(|| Tables {
        by_bytes: HashMap::new(),
        tables: Vec::new(),
    });
    if let Some(&handle) = tables.by_bytes.get(bytes) {
        return u64::from(handle);
    }
    let Some((root, rest)) = bytes.split_first_chunk::<4>() else {
        die("value shapes without a root");
    };
    let shapes = Shapes::decode(rest).unwrap_or_else(|e| die(&format!("value shapes: {e}")));
    let table: &'static Table = Box::leak(Box::new(Table {
        shapes,
        root: u32::from_le_bytes(*root),
    }));
    let handle = tables.tables.len() as u32;
    tables.tables.push(table);
    tables.by_bytes.insert(bytes.to_vec(), handle);
    u64::from(handle)
}

/// See `shapes_entry`.
unsafe extern "C" fn op_entry(
    ctx: *const TaskContext,
    packed: u64,
    a0: u64,
    a1: u64,
    b0: u64,
    b1: u64,
) -> u64 {
    let table = table(packed >> 8);
    // SAFETY: as the caller promises.
    let (_, types) = unsafe { worker_of(ctx) };
    let walk = Walk {
        shapes: &table.shapes,
        types,
    };
    let (a, b) = ([a0, a1], [b0, b1]);
    // SAFETY: as the caller promises.
    unsafe {
        match packed as u8 {
            EQUALS => u64::from(walk.equals(&a, &b, table.root)),
            COMPARE => walk
                .compare(&a, &b, table.root)
                .map_or(UNORDERED, |o| (o as i64 + 1) as u64),
            _ => {
                let mut h = Hash(0xcbf2_9ce4_8422_2325);
                walk.hash(&a, table.root, &mut h);
                h.0
            }
        }
    }
}

/// See `shapes_entry`.
unsafe extern "C" fn show_entry(
    ctx: *const TaskContext,
    handle: u64,
    w0: u64,
    w1: u64,
) -> TextWords {
    let table = table(handle);
    // SAFETY: as the caller promises.
    let (heap, types) = unsafe { worker_of(ctx) };
    let limits = PrintLimits {
        depth: usize::MAX,
        items: usize::MAX,
        chars: usize::MAX,
    };
    // SAFETY: as the caller promises.
    let text = unsafe { print_value(&[w0, w1], &table.shapes, table.root, types, limits) };
    let [w0, w1] = make_text(heap, &[text.as_bytes()]);
    TextWords(w0, w1)
}

/// FNV-1a over words.
struct Hash(u64);

impl Hash {
    fn word(&mut self, w: u64) {
        for b in w.to_le_bytes() {
            self.0 = (self.0 ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    }

    fn bytes(&mut self, bytes: &[u8]) {
        self.word(bytes.len() as u64);
        for &b in bytes {
            self.0 = (self.0 ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3);
        }
    }
}

struct Walk<'a> {
    shapes: &'a Shapes,
    types: &'a Types,
}

/// The words of a record's field.
///
/// # Safety
///
/// `ptr` is a live box with the field at its offset.
unsafe fn field<'a>(ptr: *const u8, offset: u32, words: u32) -> &'a [u64] {
    // SAFETY: as the caller promises.
    unsafe { std::slice::from_raw_parts(ptr.add(offset as usize).cast::<u64>(), words as usize) }
}

/// The type index in a box's header.
///
/// # Safety
///
/// `ptr` is a live box.
unsafe fn box_index(ptr: *const u8) -> u32 {
    // SAFETY: as the caller promises.
    unsafe { ptr.offset(TYPE_INDEX_OFFSET as isize).cast::<u32>().read() }
}

impl Walk<'_> {
    fn shape(&self, shape: u32) -> &Shape {
        &self.shapes.shapes[shape as usize]
    }

    /// The fields of a record box, by its own type where the table knows
    /// it.
    fn record_fields(&self, index: u32, shape: u32) -> &[crag_abi::ShapeField] {
        let own = self.shapes.record(index).unwrap_or(shape);
        match self.shape(own) {
            Shape::Record { fields, .. } => fields,
            _ => &[],
        }
    }

    /// The entries of a map or set, each its key's words then its value's.
    unsafe fn entries(&self, word: u64, kw: usize, vw: usize) -> Vec<&[u64]> {
        // SAFETY: as the caller promises.
        unsafe { map::iter(self.types, word as *mut u8) }
            // SAFETY: each entry is its key's words, then its value's.
            .map(|at| unsafe { std::slice::from_raw_parts(at, kw + vw) })
            .collect()
    }

    /// Whether two values of the shape are equal.
    ///
    /// # Safety
    ///
    /// Both are live values of the shape.
    unsafe fn equals(&self, a: &[u64], b: &[u64], shape: u32) -> bool {
        // SAFETY: as the caller promises, for every part walked.
        unsafe {
            match self.shape(shape) {
                Shape::Unit | Shape::Tag(_) => true,
                Shape::Number(Number::Float) => f64::from_bits(a[0]) == f64::from_bits(b[0]),
                Shape::Number(_) => a[0] == b[0],
                Shape::Str | Shape::Bytes => bytes_of(a) == bytes_of(b),
                Shape::Union { members, words } => {
                    if a[0] != b[0] {
                        return false;
                    }
                    let Some(&(_, m)) = members.iter().find(|m| u64::from(m.0) == a[0]) else {
                        return a[..*words as usize] == b[..*words as usize];
                    };
                    let n = *words as usize;
                    let (pa, pb) = (
                        member_words(&a[1..n], self.shape(m)),
                        member_words(&b[1..n], self.shape(m)),
                    );
                    self.equals(pa, pb, m)
                }
                Shape::Record { .. } => {
                    let (pa, pb) = (a[0] as *const u8, b[0] as *const u8);
                    if pa == pb {
                        return true;
                    }
                    let index = box_index(pa);
                    if index != box_index(pb) {
                        return false;
                    }
                    self.record_fields(index, shape).iter().all(|f| {
                        let n = self.shape(f.shape).words();
                        self.equals(field(pa, f.offset, n), field(pb, f.offset, n), f.shape)
                    })
                }
                Shape::List(element) => {
                    let (la, lb) = (a[0] as *mut u8, b[0] as *mut u8);
                    let len = list::length(la);
                    if len != list::length(lb) {
                        return false;
                    }
                    let n = self.shape(*element).words() as usize;
                    (0..len).all(|i| {
                        let ea = std::slice::from_raw_parts(list::get(self.types, la, i), n);
                        let eb = std::slice::from_raw_parts(list::get(self.types, lb, i), n);
                        self.equals(ea, eb, *element)
                    })
                }
                Shape::Set(key) | Shape::Map(key, _) => {
                    let value = match self.shape(shape) {
                        Shape::Map(_, v) => Some(*v),
                        _ => None,
                    };
                    let kw = self.shape(*key).words() as usize;
                    let vw = value.map_or(0, |v| self.shape(v).words() as usize);
                    let (ma, mb) = (a[0] as *mut u8, b[0] as *mut u8);
                    if map::length(ma) != map::length(mb) {
                        return false;
                    }
                    self.entries(a[0], kw, vw).iter().all(|e| {
                        let found = map::get(self.types, mb, &e[..kw]);
                        if found.is_null() {
                            return false;
                        }
                        match value {
                            Some(v) => {
                                let other = std::slice::from_raw_parts(found, vw);
                                self.equals(&e[kw..], other, v)
                            }
                            None => true,
                        }
                    })
                }
                Shape::Function | Shape::Opaque { .. } => {
                    let n = self.shape(shape).words() as usize;
                    a[..n] == b[..n]
                }
            }
        }
    }

    /// The order of two values of the shape, if the shape has one.
    ///
    /// # Safety
    ///
    /// As for `equals`.
    unsafe fn compare(&self, a: &[u64], b: &[u64], shape: u32) -> Option<Ordering> {
        // SAFETY: as the caller promises, for every part walked.
        unsafe {
            Some(match self.shape(shape) {
                Shape::Unit | Shape::Tag(_) => Ordering::Equal,
                Shape::Number(n) => match n {
                    Number::Unsigned | Number::CodePoint => a[0].cmp(&b[0]),
                    Number::Float => f64::from_bits(a[0])
                        .partial_cmp(&f64::from_bits(b[0]))
                        .unwrap_or(Ordering::Equal),
                    Number::Signed | Number::Fixed(_) => (a[0] as i64).cmp(&(b[0] as i64)),
                },
                Shape::Str | Shape::Bytes => bytes_of(a).cmp(bytes_of(b)),
                Shape::Union { members, words } => {
                    // Members order as the union is written.
                    let position = |w: u64| members.iter().position(|m| u64::from(m.0) == w);
                    let (ia, ib) = (position(a[0]), position(b[0]));
                    if ia != ib {
                        return Some(ia.cmp(&ib));
                    }
                    let (_, m) = members[ia?];
                    let n = *words as usize;
                    let (pa, pb) = (
                        member_words(&a[1..n], self.shape(m)),
                        member_words(&b[1..n], self.shape(m)),
                    );
                    self.compare(pa, pb, m)?
                }
                Shape::Record { .. } => {
                    let (pa, pb) = (a[0] as *const u8, b[0] as *const u8);
                    let (ia, ib) = (box_index(pa), box_index(pb));
                    if ia != ib {
                        return Some(ia.cmp(&ib));
                    }
                    for f in self.record_fields(ia, shape) {
                        let n = self.shape(f.shape).words();
                        let o =
                            self.compare(field(pa, f.offset, n), field(pb, f.offset, n), f.shape)?;
                        if o != Ordering::Equal {
                            return Some(o);
                        }
                    }
                    Ordering::Equal
                }
                Shape::List(element) => {
                    let (la, lb) = (a[0] as *mut u8, b[0] as *mut u8);
                    let (na, nb) = (list::length(la), list::length(lb));
                    let n = self.shape(*element).words() as usize;
                    for i in 0..na.min(nb) {
                        let ea = std::slice::from_raw_parts(list::get(self.types, la, i), n);
                        let eb = std::slice::from_raw_parts(list::get(self.types, lb, i), n);
                        let o = self.compare(ea, eb, *element)?;
                        if o != Ordering::Equal {
                            return Some(o);
                        }
                    }
                    na.cmp(&nb)
                }
                Shape::Set(_) | Shape::Map(..) | Shape::Function | Shape::Opaque { .. } => {
                    return None;
                }
            })
        }
    }

    /// Hashes a value of the shape; equal values hash alike.
    ///
    /// # Safety
    ///
    /// As for `equals`.
    unsafe fn hash(&self, a: &[u64], shape: u32, h: &mut Hash) {
        // SAFETY: as the caller promises, for every part walked.
        unsafe {
            match self.shape(shape) {
                Shape::Unit | Shape::Tag(_) => h.word(0),
                // -0.0 and 0.0 are equal, so they hash alike.
                Shape::Number(Number::Float) => h.word((f64::from_bits(a[0]) + 0.0).to_bits()),
                Shape::Number(_) => h.word(a[0]),
                Shape::Str | Shape::Bytes => h.bytes(bytes_of(a)),
                Shape::Union { members, words } => {
                    h.word(a[0]);
                    if let Some(&(_, m)) = members.iter().find(|m| u64::from(m.0) == a[0]) {
                        let payload = member_words(&a[1..*words as usize], self.shape(m));
                        self.hash(payload, m, h);
                    }
                }
                Shape::Record { .. } => {
                    let ptr = a[0] as *const u8;
                    let index = box_index(ptr);
                    h.word(u64::from(index));
                    for f in self.record_fields(index, shape) {
                        let n = self.shape(f.shape).words();
                        self.hash(field(ptr, f.offset, n), f.shape, h);
                    }
                }
                Shape::List(element) => {
                    let l = a[0] as *mut u8;
                    let len = list::length(l);
                    h.word(len as u64);
                    let n = self.shape(*element).words() as usize;
                    for i in 0..len {
                        let e = std::slice::from_raw_parts(list::get(self.types, l, i), n);
                        self.hash(e, *element, h);
                    }
                }
                Shape::Set(key) | Shape::Map(key, _) => {
                    let value = match self.shape(shape) {
                        Shape::Map(_, v) => Some(*v),
                        _ => None,
                    };
                    let kw = self.shape(*key).words() as usize;
                    let vw = value.map_or(0, |v| self.shape(v).words() as usize);
                    // The entries in any order hash alike.
                    let mut sum = 0u64;
                    for e in self.entries(a[0], kw, vw) {
                        let mut eh = Hash(0xcbf2_9ce4_8422_2325);
                        self.hash(&e[..kw], *key, &mut eh);
                        if let Some(v) = value {
                            self.hash(&e[kw..], v, &mut eh);
                        }
                        sum = sum.wrapping_add(eh.0);
                    }
                    h.word(sum);
                }
                Shape::Function | Shape::Opaque { .. } => {
                    for &w in &a[..self.shape(shape).words() as usize] {
                        h.word(w);
                    }
                }
            }
        }
    }
}
