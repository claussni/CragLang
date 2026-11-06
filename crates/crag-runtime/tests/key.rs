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

//! The memcomparable key encoding (Implementation Plan §11.11.6): the
//! unsigned byte order of `encode_key` equals the order of `compare`,
//! checked over every pair of a value set per shape — numbers, strings
//! with embedded zero bytes, a union, a record and a list — and over
//! random integers and strings.

mod common;

use std::cmp::Ordering;

use crag_abi::{ElementLayout, LIST_SIZE, Number, Shape, ShapeField, Shapes, TypeDescriptor};
use crag_runtime::{Heap, Types, compare_values, decode_value, encode_key, release_value};

const EMPTY_TAG: u32 = 50;
const INT_TAG: u32 = 51;
const LIST_IDX: u32 = 60;

const SIGNED: u32 = 0;
const UNSIGNED: u32 = 1;
const FLOAT: u32 = 2;
const STR: u32 = 3;
const VARIANT: u32 = 5;
const PAIR: u32 = 6;
const LIST: u32 = 7;

fn field(name: &str, offset: u32, shape: u32) -> ShapeField {
    ShapeField {
        name: name.into(),
        offset,
        shape,
    }
}

fn shapes() -> Shapes {
    Shapes {
        shapes: vec![
            Shape::Number(Number::Signed),
            Shape::Number(Number::Unsigned),
            Shape::Number(Number::Float),
            Shape::Str,
            Shape::Tag("Empty".into()),
            Shape::Variant {
                members: vec![(EMPTY_TAG, 4), (INT_TAG, 0)],
                words: 2,
            },
            Shape::Inline {
                name: Some("Pair".into()),
                fields: vec![field("x", 0, SIGNED), field("y", 1, SIGNED)],
                words: 2,
            },
            Shape::List(SIGNED),
        ],
        records: Vec::new(),
        boxes: vec![(LIST, LIST_IDX, LIST_SIZE)],
        plain: Vec::new(),
        identities: Vec::new(),
    }
}

fn types() -> Types {
    let word = ElementLayout::of_words(1, Vec::new());
    Types::new([(
        LIST_IDX,
        TypeDescriptor::List {
            element: word.clone(),
            cell: word.clone(),
            ref_cell: word,
        },
    )])
}

/// Every pair of the values must order by its key bytes exactly as
/// `compare` orders the values; equal values must encode alike.
fn ordered(values: &[Vec<u64>], shapes: &Shapes, types: &Types, shape: u32) {
    let keys: Vec<Vec<u8>> = values
        .iter()
        .map(|words| {
            let mut out = Vec::new();
            // SAFETY: the values are live and of the shape.
            unsafe { encode_key(words, shapes, types, shape, &mut out) }.expect("orderable");
            out
        })
        .collect();
    for (i, a) in values.iter().enumerate() {
        for (j, b) in values.iter().enumerate() {
            // SAFETY: the values are live and of the shape.
            let order = unsafe { compare_values(shapes, types, a, b, shape) }
                .expect("the shape has an order");
            assert_eq!(
                keys[i].cmp(&keys[j]),
                order,
                "value {i} vs {j} of shape {shape}: {:?} vs {:?}",
                keys[i],
                keys[j]
            );
            if order == Ordering::Equal {
                assert_eq!(keys[i], keys[j], "equal values must encode alike");
            }
        }
    }
}

/// A string value on the heap, from its codec bytes.
fn text(heap: &mut Heap, shapes: &Shapes, types: &Types, s: &str) -> Vec<u64> {
    let mut bytes = (s.len() as u64).to_le_bytes().to_vec();
    bytes.extend(s.as_bytes());
    // SAFETY: the bytes are a value of the Str shape.
    unsafe { decode_value(&bytes, shapes, STR, heap, types) }.expect("a string decodes")
}

/// A list of signed integers on the heap, from its codec bytes.
fn list(heap: &mut Heap, shapes: &Shapes, types: &Types, elements: &[i64]) -> Vec<u64> {
    let mut bytes = (elements.len() as u64).to_le_bytes().to_vec();
    for e in elements {
        bytes.extend((*e as u64).to_le_bytes());
    }
    // SAFETY: the bytes are a value of the list shape.
    unsafe { decode_value(&bytes, shapes, LIST, heap, types) }.expect("a list decodes")
}

#[test]
fn key_bytes_order_as_compare_does() {
    let _watchdog = common::watchdog("the key encoding test");
    let shapes = shapes();
    let types = types();
    let mut heap = Heap::new();

    let signed: Vec<Vec<u64>> = [i64::MIN, -70_000, -5, -1, 0, 1, 7, 70_000, i64::MAX]
        .iter()
        .map(|&v| vec![v as u64])
        .collect();
    ordered(&signed, &shapes, &types, SIGNED);

    let unsigned: Vec<Vec<u64>> = [0, 1, 5, 1 << 40, u64::MAX]
        .iter()
        .map(|&v| vec![v])
        .collect();
    ordered(&unsigned, &shapes, &types, UNSIGNED);

    // `-0.0` and `0.0` compare `Equal`, so they must encode alike.
    let floats: Vec<Vec<u64>> = [
        f64::NEG_INFINITY,
        -1e300,
        -2.5,
        -f64::MIN_POSITIVE,
        -0.0,
        0.0,
        f64::MIN_POSITIVE,
        1.0,
        2.5,
        1e300,
        f64::INFINITY,
    ]
    .iter()
    .map(|&v| vec![v.to_bits()])
    .collect();
    ordered(&floats, &shapes, &types, FLOAT);

    let texts = [
        "",
        "a",
        "a\0",
        "a\0b",
        "aa",
        "ab",
        "b",
        "a longer text than fifteen bytes",
    ];
    let texts: Vec<Vec<u64>> = texts
        .iter()
        .map(|s| text(&mut heap, &shapes, &types, s))
        .collect();
    ordered(&texts, &shapes, &types, STR);

    // `compare` orders union members by their place among the shape's
    // members, then by the payload.
    let variants: Vec<Vec<u64>> = vec![
        vec![u64::from(EMPTY_TAG), 0],
        vec![u64::from(INT_TAG), -3i64 as u64],
        vec![u64::from(INT_TAG), 9],
    ];
    ordered(&variants, &shapes, &types, VARIANT);

    let pairs: Vec<Vec<u64>> = [(0i64, 1i64), (1, 0), (1, 2), (-1, 5), (1, 2), (1, -2)]
        .iter()
        .map(|&(x, y)| vec![x as u64, y as u64])
        .collect();
    ordered(&pairs, &shapes, &types, PAIR);

    // A list orders by its elements first and its length last.
    let lists: Vec<&[i64]> = vec![&[], &[-1], &[1], &[1, 2], &[1, 2, 3], &[2], &[1, 2]];
    let lists: Vec<Vec<u64>> = lists
        .iter()
        .map(|e| list(&mut heap, &shapes, &types, e))
        .collect();
    ordered(&lists, &shapes, &types, LIST);

    for words in texts.iter().chain(&lists) {
        // SAFETY: the values are live and of their shapes.
        unsafe {
            release_value(
                &mut heap,
                &types,
                words,
                &shapes,
                if words.len() == 2 { STR } else { LIST },
            );
        }
    }
    assert_eq!(heap.live_blocks(), 0);
}

#[test]
fn random_keys_order_as_compare_does() {
    let _watchdog = common::watchdog("the random key test");
    let shapes = shapes();
    let types = types();
    let mut heap = Heap::new();
    // A fixed-seed xorshift keeps the run reproducible.
    let mut state = 0x9e3779b97f4a7c15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };

    let signed: Vec<Vec<u64>> = (0..64)
        .map(|_| {
            let v = next();
            // Small and large magnitudes alike.
            vec![if v & 1 == 0 { v >> (v % 60) } else { v }]
        })
        .collect();
    ordered(&signed, &shapes, &types, SIGNED);

    let texts: Vec<Vec<u64>> = (0..48)
        .map(|_| {
            let n = (next() % 12) as usize;
            let s: String = (0..n)
                .map(|_| char::from(b'a' + (next() % 3) as u8))
                .collect();
            // Embedded zero bytes exercise the escape.
            let s = if next() % 4 == 0 {
                format!("{s}\0{s}")
            } else {
                s
            };
            text(&mut heap, &shapes, &types, &s)
        })
        .collect();
    ordered(&texts, &shapes, &types, STR);

    for words in &texts {
        // SAFETY: the values are live strings.
        unsafe { release_value(&mut heap, &types, words, &shapes, STR) };
    }
    assert_eq!(heap.live_blocks(), 0);
}
