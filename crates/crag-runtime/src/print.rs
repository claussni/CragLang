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

//! Value printing (Implementation Plan §11.6.5): a value shown as source
//! writes it, walked through the shape of its type, without generated
//! code. A box of a record type is shown by the type in its header, which
//! may be a subtype of the static one. Entries of maps and sets are shown
//! in the order of their keys' words, which for numbers is their order.
//! Limits cut deep, long and large values short with `…`.

use crag_abi::{Number, Shape, Shapes, TYPE_INDEX_OFFSET};

use crate::heap::Heap;
use crate::rc::{Types, drop_box};
use crate::{list, map};

/// How much of a value is shown.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PrintLimits {
    /// Values inside values, from the outermost.
    pub depth: usize,
    /// Elements of a collection.
    pub items: usize,
    /// Characters of the text, after which it ends.
    pub chars: usize,
}

impl Default for PrintLimits {
    fn default() -> PrintLimits {
        PrintLimits {
            depth: 16,
            items: 100,
            chars: 10_000,
        }
    }
}

/// The text of a value: its words, of the shape `shape` of `shapes`.
///
/// # Safety
///
/// The words are a live value of the shape, and `types` describes its
/// collections.
pub unsafe fn print_value(
    words: &[u64],
    shapes: &Shapes,
    shape: u32,
    types: &Types,
    limits: PrintLimits,
) -> String {
    let mut p = Printer {
        shapes,
        types,
        limits,
        out: String::new(),
        full: false,
    };
    // SAFETY: as the caller promises.
    unsafe { p.value(words, shape, 0) };
    p.out
}

struct Printer<'a> {
    shapes: &'a Shapes,
    types: &'a Types,
    limits: PrintLimits,
    out: String,
    /// The text reached its limit.
    full: bool,
}

impl Printer<'_> {
    fn shape(&self, shape: u32) -> &Shape {
        &self.shapes.shapes[shape as usize]
    }

    /// Whether the text is full; the first time, it ends with `…`.
    fn stop(&mut self) -> bool {
        if !self.full && self.out.len() >= self.limits.chars {
            self.out.push('…');
            self.full = true;
        }
        self.full
    }

    unsafe fn value(&mut self, words: &[u64], shape: u32, depth: usize) {
        if self.stop() {
            return;
        }
        if depth > self.limits.depth {
            self.out.push('…');
            return;
        }
        let word = words.first().copied().unwrap_or(0);
        match self.shape(shape).clone() {
            Shape::Unit => self.out.push_str("()"),
            Shape::Tag(name) => self.out.push_str(&name),
            Shape::Number(n) => self.out.push_str(&number(n, word)),
            Shape::Union { members, words: n } => {
                let member = members.iter().find(|m| u64::from(m.0) == word);
                match member {
                    // SAFETY: the payload is the member's.
                    Some(&(_, m)) => unsafe { self.value(&words[1..n as usize], m, depth) },
                    None => self.out.push_str(&format!("<a member of type {word}>")),
                }
            }
            Shape::Record { name, fields } => {
                let ptr = word as *const u8;
                // SAFETY: the word points at a live box of a record type.
                let index = unsafe { ptr.offset(TYPE_INDEX_OFFSET as isize).cast::<u32>().read() };
                // A subtype's box is shown as its own type.
                let (name, fields) = match self.shapes.record(index).map(|s| self.shape(s)) {
                    Some(Shape::Record { name, fields }) => (name.clone(), fields.clone()),
                    _ => (name, fields),
                };
                self.out.push_str(name.as_deref().unwrap_or(""));
                self.out.push('(');
                for (i, f) in fields.iter().enumerate() {
                    if i > 0 {
                        self.out.push_str(", ");
                    }
                    self.out.push_str(&f.name);
                    self.out.push_str(": ");
                    let n = self.shape(f.shape).words() as usize;
                    // SAFETY: the field's words are at its offset.
                    unsafe {
                        let at = ptr.add(f.offset as usize).cast::<u64>();
                        let words = std::slice::from_raw_parts(at, n);
                        self.value(words, f.shape, depth + 1);
                    }
                    if self.full {
                        return;
                    }
                }
                self.out.push(')');
            }
            Shape::List(element) => {
                let list = word as *mut u8;
                let n = self.shape(element).words() as usize;
                // SAFETY: a live list of the element's shape.
                let len = unsafe { list::length(list) };
                self.out.push('[');
                for i in 0..len {
                    if !self.separate(i, len) {
                        break;
                    }
                    // SAFETY: as above; the index is inside the list.
                    unsafe {
                        let at = list::get(self.types, list, i);
                        self.value(std::slice::from_raw_parts(at, n), element, depth + 1);
                    }
                }
                self.out.push(']');
            }
            Shape::Set(element) => {
                // SAFETY: a live set of the element's shape.
                unsafe { self.entries(word, element, None, depth) }
            }
            Shape::Map(key, value) => {
                // SAFETY: a live map of the shapes.
                unsafe { self.entries(word, key, Some(value), depth) }
            }
            Shape::Function => self.out.push_str("<function>"),
            Shape::Opaque { name, .. } => self.out.push_str(&format!("<a value of type {name}>")),
        }
    }

    /// Before the element `i` of `len`: the separator, or the end of what
    /// is shown. Whether to show it.
    fn separate(&mut self, i: usize, len: usize) -> bool {
        if i > 0 {
            self.out.push_str(", ");
        }
        if i == self.limits.items {
            self.out.push_str(&format!("… {} more", len - i));
            return false;
        }
        !self.stop()
    }

    /// The entries of a map, or of a set without values, by their keys.
    unsafe fn entries(&mut self, word: u64, key: u32, value: Option<u32>, depth: usize) {
        let map = word as *mut u8;
        let kw = self.shape(key).words() as usize;
        let vw = value.map_or(0, |v| self.shape(v).words() as usize);
        // SAFETY: as the caller promises.
        let mut entries: Vec<&[u64]> = unsafe { map::iter(self.types, map) }
            // SAFETY: each entry is its key's words, then its value's.
            .map(|at| unsafe { std::slice::from_raw_parts(at, kw + vw) })
            .collect();
        entries.sort_by_key(|e| e[..kw].iter().map(|&w| w as i64).collect::<Vec<_>>());
        if entries.is_empty() {
            self.out
                .push_str(if value.is_some() { "[:]" } else { "[]" });
            return;
        }
        self.out.push('[');
        let len = entries.len();
        for (i, e) in entries.into_iter().enumerate() {
            if !self.separate(i, len) {
                break;
            }
            // SAFETY: the entry's words are a key and a value of the shapes.
            unsafe {
                self.value(&e[..kw], key, depth + 1);
                if let Some(value) = value {
                    self.out.push_str(": ");
                    self.value(&e[kw..], value, depth + 1);
                }
            }
        }
        self.out.push(']');
    }
}

/// A number as source writes it.
fn number(n: Number, word: u64) -> String {
    match n {
        Number::Signed => (word as i64).to_string(),
        Number::Unsigned => word.to_string(),
        Number::Float => format!("{:?}", f64::from_bits(word)),
        Number::Fixed(digits) => {
            let scaled = word as i64;
            let scale = 10u64.pow(digits);
            let sign = if scaled < 0 { "-" } else { "" };
            let n = scaled.unsigned_abs();
            match digits {
                0 => format!("{sign}{n}"),
                _ => format!(
                    "{sign}{}.{:0width$}",
                    n / scale,
                    n % scale,
                    width = digits as usize
                ),
            }
        }
        Number::CodePoint => match char::from_u32(word as u32) {
            Some(c) => format!("{c:?}"),
            None => format!("<code point {word:#x}>"),
        },
    }
}

/// Gives up the references a value's words hold, freeing what only they
/// held.
///
/// # Safety
///
/// The caller owns the value, of the shape, and gives it up.
pub unsafe fn release_value(
    heap: &mut Heap,
    types: &Types,
    words: &[u64],
    shapes: &Shapes,
    shape: u32,
) {
    let boxed = |s: u32| {
        matches!(
            shapes.shapes[s as usize],
            Shape::Record { .. } | Shape::List(_) | Shape::Set(_) | Shape::Map(..)
        )
    };
    let ptr = match &shapes.shapes[shape as usize] {
        _ if boxed(shape) => words[0],
        Shape::Union { members, words: 2 } => {
            match members.iter().find(|m| u64::from(m.0) == words[0]) {
                Some(&(_, m)) if boxed(m) => words[1],
                _ => 0,
            }
        }
        // The environment, or null.
        Shape::Function => words[1],
        _ => 0,
    };
    if ptr != 0 {
        // SAFETY: as the caller promises.
        unsafe { drop_box(heap, types, ptr as *mut u8) };
    }
}
