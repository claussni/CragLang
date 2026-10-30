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

//! The text functions of the prelude (Specification §19.10) that need the
//! runtime: counting, stepping by code points, searching, case mapping,
//! the Unicode classes, parsing numbers, and reading and writing numbers
//! in bytes. The rest of them are written in Crag over these.
//!
//! A string's bytes are valid UTF-8, which the compiler and `text`
//! guarantee; the same functions serve bytes values, where only the byte
//! operations are used.

use crag_abi::text_op::*;

use crate::fiber::TaskContext;
use crate::io::Words;
use crate::system::worker_of;
use crate::text::{TextWords, bytes_of, make_text};

/// No offset, position or code point.
const NONE: u64 = u64::MAX;

/// Whether a byte starts a code point.
fn starts(b: u8) -> bool {
    b & 0xC0 != 0x80
}

/// The string of bytes that are UTF-8.
fn as_str(bytes: &[u8]) -> &str {
    std::str::from_utf8(bytes).unwrap_or_else(|e| {
        // SAFETY: the bytes before the error are valid UTF-8.
        unsafe { std::str::from_utf8_unchecked(&bytes[..e.valid_up_to()]) }
    })
}

fn text(ctx: *const TaskContext, bytes: &[u8]) -> TextWords {
    // SAFETY: called on the system stack by a runtime function.
    let (heap, _) = unsafe { worker_of(ctx) };
    let [w0, w1] = make_text(heap, &[bytes]);
    TextWords(w0, w1)
}

system_stack_fn! {
    /// `rt_text_measure(ctx, op, w0, w1)`: see
    /// `crag_abi::RuntimeFn::TextMeasure`.
    fn rt_text_measure(ctx: *const TaskContext, op: u64, w0: u64, w1: u64) -> u64 => measure_entry
}

system_stack_fn! {
    /// `rt_text_at(ctx, op, w0, w1, at)`: see `crag_abi::RuntimeFn::TextAt`.
    fn rt_text_at(ctx: *const TaskContext, op: u64, w0: u64, w1: u64, at: u64) -> u64 => at_entry
}

system_stack_fn! {
    /// `rt_text_find(ctx, a0, a1, b0, b1, packed)`: see
    /// `crag_abi::RuntimeFn::TextFind`.
    fn rt_text_find(ctx: *const TaskContext, a0: u64, a1: u64, b0: u64, b1: u64, packed: u64) -> u64
        => find_entry
}

system_stack_fn! {
    /// `rt_text_map(ctx, op, w0, w1)`: see `crag_abi::RuntimeFn::TextMap`.
    fn rt_text_map(ctx: *const TaskContext, op: u64, w0: u64, w1: u64) -> TextWords => map_entry
}

system_stack_fn! {
    /// `rt_text_slice(ctx, w0, w1, from, to)`: see
    /// `crag_abi::RuntimeFn::TextSlice`.
    fn rt_text_slice(ctx: *const TaskContext, w0: u64, w1: u64, from: u64, to: u64) -> TextWords
        => slice_entry
}

system_stack_fn! {
    /// `rt_code_point(ctx, op, value)`: see
    /// `crag_abi::RuntimeFn::CodePointOp`.
    fn rt_code_point(ctx: *const TaskContext, op: u64, value: u64) -> u64 => code_point_entry
}

system_stack_fn! {
    /// `rt_text_parse(ctx, op, w0, w1, base)`: see
    /// `crag_abi::RuntimeFn::TextParse`.
    fn rt_text_parse(ctx: *const TaskContext, op: u64, w0: u64, w1: u64, base: u64) -> Words
        => parse_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with values the caller holds.
unsafe extern "C" fn measure_entry(_ctx: *const TaskContext, op: u64, w0: u64, w1: u64) -> u64 {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    match op as u8 {
        CODE_POINT_COUNT => bytes.iter().filter(|&&b| starts(b)).count() as u64,
        _ => bytes.len() as u64,
    }
}

/// See `measure_entry`.
unsafe extern "C" fn at_entry(_ctx: *const TaskContext, op: u64, w0: u64, w1: u64, at: u64) -> u64 {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    let len = bytes.len();
    let Ok(at) = usize::try_from(at as i64) else {
        return match op as u8 {
            IS_BOUNDARY => 0,
            _ => NONE,
        };
    };
    match op as u8 {
        IS_BOUNDARY => u64::from(at == len || (at < len && starts(bytes[at]))),
        NEXT if at < len => {
            let mut next = at + 1;
            while next < len && !starts(bytes[next]) {
                next += 1;
            }
            next as u64
        }
        PREVIOUS if at > 0 && at <= len => {
            let mut previous = at - 1;
            while previous > 0 && !starts(bytes[previous]) {
                previous -= 1;
            }
            previous as u64
        }
        CODE_POINT_AT if at < len => as_str(&bytes[at..])
            .chars()
            .next()
            .map_or(NONE, |c| u64::from(u32::from(c))),
        BYTE_AT if at < len => u64::from(bytes[at]),
        _ => NONE,
    }
}

/// The first offset at or after `from` where `part` is in `bytes`.
fn index_of(bytes: &[u8], part: &[u8], from: usize) -> Option<usize> {
    if from > bytes.len() {
        return None;
    }
    if part.is_empty() {
        return Some(from);
    }
    bytes[from..]
        .windows(part.len())
        .position(|w| w == part)
        .map(|i| i + from)
}

/// See `measure_entry`.
unsafe extern "C" fn find_entry(
    _ctx: *const TaskContext,
    a0: u64,
    a1: u64,
    b0: u64,
    b1: u64,
    packed: u64,
) -> u64 {
    let (a, b) = ([a0, a1], [b0, b1]);
    // SAFETY: as the caller promises.
    let (bytes, part) = unsafe { (bytes_of(&a), bytes_of(&b)) };
    let from = (packed >> 3) as usize;
    match (packed & 7) as u8 {
        INDEX_OF => index_of(bytes, part, from).map_or(NONE, |i| i as u64),
        LAST_INDEX_OF => match part.len() {
            0 => bytes.len() as u64,
            n if n > bytes.len() => NONE,
            n => bytes
                .windows(n)
                .rposition(|w| w == part)
                .map_or(NONE, |i| i as u64),
        },
        STARTS_WITH => u64::from(bytes.starts_with(part)),
        ENDS_WITH => u64::from(bytes.ends_with(part)),
        _ => (bytes.cmp(part) as i64 + 1) as u64,
    }
}

/// See `measure_entry`.
unsafe extern "C" fn map_entry(ctx: *const TaskContext, op: u64, w0: u64, w1: u64) -> TextWords {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    if op as u8 == HEX {
        let hex: String = bytes.iter().map(|b| format!("{b:02x}")).collect();
        return text(ctx, hex.as_bytes());
    }
    let s = as_str(bytes);
    match op as u8 {
        TRIM => text(ctx, s.trim().as_bytes()),
        TRIM_START => text(ctx, s.trim_start().as_bytes()),
        TRIM_END => text(ctx, s.trim_end().as_bytes()),
        TO_UPPER => text(ctx, s.to_uppercase().as_bytes()),
        _ => text(ctx, s.to_lowercase().as_bytes()),
    }
}

/// See `measure_entry`.
unsafe extern "C" fn slice_entry(
    ctx: *const TaskContext,
    w0: u64,
    w1: u64,
    from: u64,
    to: u64,
) -> TextWords {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    let clamp = |n: u64| usize::try_from(n as i64).unwrap_or(0).min(bytes.len());
    let (from, to) = (clamp(from), clamp(to));
    text(ctx, &bytes[from..to.max(from)])
}

/// See `measure_entry`.
unsafe extern "C" fn code_point_entry(_ctx: *const TaskContext, op: u64, value: u64) -> u64 {
    let valid = u32::try_from(value).ok().and_then(char::from_u32);
    if op as u8 == CP_IS_VALID {
        return u64::from(valid.is_some());
    }
    let Some(c) = valid else {
        return 0;
    };
    let single = |mut mapped: Box<dyn Iterator<Item = char>>| match (mapped.next(), mapped.next()) {
        (Some(m), None) => u64::from(u32::from(m)),
        _ => value,
    };
    match op as u8 {
        CP_IS_LETTER => u64::from(c.is_alphabetic()),
        CP_IS_DIGIT => u64::from(c.is_ascii_digit()),
        CP_IS_WHITESPACE => u64::from(c.is_whitespace()),
        CP_IS_UPPER => u64::from(c.is_uppercase()),
        CP_IS_LOWER => u64::from(c.is_lowercase()),
        CP_TO_UPPER => single(Box::new(c.to_uppercase())),
        CP_TO_LOWER => single(Box::new(c.to_lowercase())),
        _ => u64::from(c.is_numeric()),
    }
}

/// See `measure_entry`.
unsafe extern "C" fn parse_entry(
    _ctx: *const TaskContext,
    op: u64,
    w0: u64,
    w1: u64,
    base: u64,
) -> Words {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let s = as_str(unsafe { bytes_of(&words) });
    match op as u8 {
        PARSE_INT => match base {
            2..=36 => {
                i64::from_str_radix(s, base as u32).map_or(Words(0, 0), |n| Words(n as u64, 1))
            }
            _ => Words(0, 0),
        },
        PARSE_UINT => match base {
            2..=36 if !s.starts_with('+') => {
                u64::from_str_radix(s, base as u32).map_or(Words(0, 0), |n| Words(n, 1))
            }
            _ => Words(0, 0),
        },
        // Rust also reads "inf" and "NaN", which Crag does not (§3.1.4).
        _ => match s.parse::<f64>() {
            Ok(f)
                if f.is_finite()
                    && s.bytes()
                        .all(|b| b.is_ascii_digit() || b".+-eE".contains(&b)) =>
            {
                Words(f.to_bits(), 1)
            }
            _ => Words(0, 0),
        },
    }
}

system_stack_fn! {
    /// `rt_bytes_read(ctx, packed, w0, w1, at)`: see
    /// `crag_abi::RuntimeFn::BytesRead`.
    fn rt_bytes_read(ctx: *const TaskContext, packed: u64, w0: u64, w1: u64, at: u64) -> Words
        => read_entry
}

system_stack_fn! {
    /// `rt_bytes_write(ctx, packed, w0, w1, at, value)`: see
    /// `crag_abi::RuntimeFn::BytesWrite`.
    fn rt_bytes_write(ctx: *const TaskContext, packed: u64, w0: u64, w1: u64, at: u64, value: u64)
        -> TextWords => write_entry
}

system_stack_fn! {
    /// `rt_bytes_of_list(ctx, list)`: see `crag_abi::RuntimeFn::BytesOfList`.
    fn rt_bytes_of_list(ctx: *const TaskContext, list: *mut u8) -> TextWords => of_list_entry
}

/// The width in bytes of a kind of `crag_abi::bytes_kind`.
fn width(kind: u8) -> usize {
    use crag_abi::bytes_kind::*;
    match kind {
        INT8 | UINT8 => 1,
        INT16 | UINT16 => 2,
        INT32 | UINT32 | FLOAT32 => 4,
        _ => 8,
    }
}

/// See `measure_entry`.
unsafe extern "C" fn read_entry(
    _ctx: *const TaskContext,
    packed: u64,
    w0: u64,
    w1: u64,
    at: u64,
) -> Words {
    use crag_abi::bytes_kind::*;
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    let kind = packed as u8;
    let n = width(kind);
    let Some(field) = usize::try_from(at as i64)
        .ok()
        .and_then(|at| bytes.get(at..at.checked_add(n)?))
    else {
        return Words(0, 0);
    };
    let mut raw = [0u8; 8];
    match packed & BIG {
        0 => raw[..n].copy_from_slice(field),
        _ => {
            for (i, &b) in field.iter().rev().enumerate() {
                raw[i] = b;
            }
        }
    }
    let unsigned = u64::from_le_bytes(raw);
    let value = match kind {
        INT8 => unsigned as u8 as i8 as i64 as u64,
        INT16 => unsigned as u16 as i16 as i64 as u64,
        INT32 => unsigned as u32 as i32 as i64 as u64,
        FLOAT32 => {
            let f = f64::from(f32::from_bits(unsigned as u32));
            if !f.is_finite() {
                return Words(0, 0);
            }
            f.to_bits()
        }
        FLOAT64 if !f64::from_bits(unsigned).is_finite() => return Words(0, 0),
        _ => unsigned,
    };
    Words(value, 1)
}

/// See `measure_entry`.
unsafe extern "C" fn write_entry(
    ctx: *const TaskContext,
    packed: u64,
    w0: u64,
    w1: u64,
    at: u64,
    value: u64,
) -> TextWords {
    use crag_abi::bytes_kind::*;
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let mut bytes = unsafe { bytes_of(&words) }.to_vec();
    let kind = packed as u8;
    let n = width(kind);
    let raw = match kind {
        FLOAT32 => u64::from((f64::from_bits(value) as f32).to_bits()),
        _ => value,
    }
    .to_le_bytes();
    let at = at as usize;
    if let Some(field) = bytes.get_mut(at..at + n) {
        match packed & BIG {
            0 => field.copy_from_slice(&raw[..n]),
            _ => {
                for (i, b) in field.iter_mut().rev().enumerate() {
                    *b = raw[i];
                }
            }
        }
    }
    text(ctx, &bytes)
}

/// See `measure_entry`.
unsafe extern "C" fn of_list_entry(ctx: *const TaskContext, list: *mut u8) -> TextWords {
    // SAFETY: as the caller promises: a live list of `UInt8`, whose
    // elements are a byte, or a word without flat layouts, the byte first.
    let bytes: Vec<u8> = unsafe {
        let (_, types) = worker_of(ctx);
        (0..crate::list::length(list))
            .map(|i| crate::list::get(types, list, i).cast::<u8>().read())
            .collect()
    };
    text(ctx, &bytes)
}
