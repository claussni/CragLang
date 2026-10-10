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

//! Strings and bytes (Implementation Plan §11.6.9): two words, the bytes
//! inline or in a buffer (see `crag_abi`). The runtime joins them, compares
//! them and writes numbers as text; generated code counts their buffers.

use crag_abi::{
    BUFFER_HEADER, COUNT_OFFSET, HEADER_SIZE, INLINE_TEXT_MAX, Number, TEXT_LEN_MAX,
    TYPE_INDEX_OFFSET, inline_text,
};

use crate::die;
use crate::fiber::TaskContext;
use crate::heap::Heap;
use crate::system::worker_of;

/// The two words of a string or bytes value, as the runtime functions
/// return them: in the first two result registers.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TextWords(pub u64, pub u64);

/// Whether the first word of a value points at a buffer.
pub fn in_buffer(w0: u64) -> bool {
    w0 & 1 == 0
}

/// The bytes of a string or bytes value, borrowed from its words or from
/// its buffer.
///
/// # Safety
///
/// The words are a live value, and its buffer outlives the borrow.
pub unsafe fn bytes_of(words: &[u64]) -> &[u8] {
    let (w0, w1) = (words[0], words[1]);
    // SAFETY: as the caller promises. An inline value's bytes follow its
    // first byte in the two words, which are adjacent and little-endian.
    unsafe {
        if in_buffer(w0) {
            let start = HEADER_SIZE as usize + (w1 >> 32) as usize;
            let ptr = (w0 as *const u8).add(start);
            std::slice::from_raw_parts(ptr, (w1 & 0xffff_ffff) as usize)
        } else {
            let ptr = words.as_ptr().cast::<u8>().add(1);
            std::slice::from_raw_parts(ptr, (w0 as u8 >> 1) as usize)
        }
    }
}

/// A new value holding the bytes of `parts`, one after another: inline
/// when they fit, otherwise in a buffer from the heap, with a reference of
/// its own.
pub fn make_text(heap: &mut Heap, parts: &[&[u8]]) -> [u64; 2] {
    let len: usize = parts.iter().map(|p| p.len()).sum();
    if len <= INLINE_TEXT_MAX {
        return inline_text(&parts.concat());
    }
    if len as u64 > TEXT_LEN_MAX {
        die("a string or bytes of 4 GiB or more");
    }
    let ptr = heap.alloc(HEADER_SIZE as usize + len);
    // SAFETY: the block holds the header and `len` bytes.
    unsafe {
        ptr.offset(COUNT_OFFSET as isize).cast::<u64>().write(1);
        ptr.offset(TYPE_INDEX_OFFSET as isize)
            .cast::<u64>()
            .write(BUFFER_HEADER);
        let mut at = ptr.add(HEADER_SIZE as usize);
        for part in parts {
            std::ptr::copy_nonoverlapping(part.as_ptr(), at, part.len());
            at = at.add(part.len());
        }
    }
    [ptr as u64, len as u64]
}

/// A number as interpolation writes it: as the value printer does, but a
/// code point as its character.
pub fn show_number(number: Number, word: u64) -> String {
    match number {
        Number::CodePoint => match char::from_u32(word as u32) {
            Some(c) => c.to_string(),
            None => format!("<code point {word:#x}>"),
        },
        n => crate::print::number(n, word),
    }
}

system_stack_fn! {
    /// `rt_text_concat(ctx, a0, a1, b0, b1)`: see
    /// `crag_abi::RuntimeFn::TextConcat`.
    fn rt_text_concat(ctx: *const TaskContext, a0: u64, a1: u64, b0: u64, b1: u64) -> TextWords
        => concat_entry
}

system_stack_fn! {
    /// `rt_text_equals(ctx, a0, a1, b0, b1)`: see
    /// `crag_abi::RuntimeFn::TextEquals`.
    fn rt_text_equals(ctx: *const TaskContext, a0: u64, a1: u64, b0: u64, b1: u64) -> u64
        => equals_entry
}

system_stack_fn! {
    /// `rt_text_show(ctx, word, number)`: see `crag_abi::RuntimeFn::TextShow`.
    fn rt_text_show(ctx: *const TaskContext, word: u64, number: u64) -> TextWords
        => show_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with what generated code passed them.
unsafe extern "C" fn concat_entry(
    ctx: *const TaskContext,
    a0: u64,
    a1: u64,
    b0: u64,
    b1: u64,
) -> TextWords {
    // SAFETY: as the caller promises; both values are borrowed live ones.
    unsafe {
        let (heap, _) = worker_of(ctx);
        let (a, b) = ([a0, a1], [b0, b1]);
        let [w0, w1] = make_text(heap, &[bytes_of(&a), bytes_of(&b)]);
        TextWords(w0, w1)
    }
}

/// See `concat_entry`.
unsafe extern "C" fn equals_entry(
    _ctx: *const TaskContext,
    a0: u64,
    a1: u64,
    b0: u64,
    b1: u64,
) -> u64 {
    // SAFETY: as the caller promises.
    unsafe { u64::from(bytes_of(&[a0, a1]) == bytes_of(&[b0, b1])) }
}

/// See `concat_entry`.
unsafe extern "C" fn show_entry(ctx: *const TaskContext, word: u64, number: u64) -> TextWords {
    let Some(number) = Number::from_code(number) else {
        die(&format!("no number has the code {number}"));
    };
    let text = show_number(number, word);
    // SAFETY: as the caller promises.
    let (heap, _) = unsafe { worker_of(ctx) };
    let [w0, w1] = make_text(heap, &[text.as_bytes()]);
    TextWords(w0, w1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rc::{Types, drop_box};

    #[test]
    fn short_values_are_inline_and_long_ones_in_buffers() {
        let mut heap = Heap::new();
        let short = make_text(&mut heap, &[b"Gr\xc3\xbc", b"\xc3\x9fe"]);
        assert!(!in_buffer(short[0]));
        assert_eq!(short, inline_text("Grüße".as_bytes()));
        // SAFETY: the values are live.
        unsafe {
            assert_eq!(bytes_of(&short), "Grüße".as_bytes());
            let fifteen = make_text(&mut heap, &[b"abcdefghijklmno"]);
            assert!(!in_buffer(fifteen[0]));
            assert_eq!(bytes_of(&fifteen), b"abcdefghijklmno");
            let long = make_text(&mut heap, &[b"abcdefgh", b"ijklmnop"]);
            assert!(in_buffer(long[0]));
            assert_eq!(long[1], 16);
            assert_eq!(bytes_of(&long), b"abcdefghijklmnop");
            assert_eq!(heap.live_blocks(), 1);
            // A buffer needs no descriptor.
            drop_box(&mut heap, &Types::default(), long[0] as *mut u8);
            assert_eq!(heap.live_blocks(), 0);
            assert_eq!(bytes_of(&make_text(&mut heap, &[])), b"");
        }
    }

    #[test]
    fn numbers_are_written_as_interpolation_writes_them() {
        assert_eq!(show_number(Number::Signed, -5i64 as u64), "-5");
        assert_eq!(
            show_number(Number::Unsigned, u64::MAX),
            "18446744073709551615"
        );
        assert_eq!(show_number(Number::Float, 0.5f64.to_bits()), "0.5");
        assert_eq!(show_number(Number::Fixed(2), 1205), "12.05");
        assert_eq!(show_number(Number::CodePoint, 'q' as u64), "q");
    }
}
