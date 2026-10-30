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

//! Fields stored flat in a box (Compiler Architecture §A11.4): decoded,
//! printed, encoded again and released through their shapes and the
//! box's descriptor.

use crag_abi::{
    CountedField, FieldGuard, Number, Shape, ShapeField, Shapes, StoredKind, StoredSlot, StoredTag,
    TypeDescriptor,
};
use crag_runtime::{
    Heap, PrintLimits, Types, decode_value, encode_value, print_value, release_box,
};

const LABEL: u32 = 40;
const STR: u32 = 41;
const EMPTY: u32 = 42;

fn slot(at: u32, offset: u32, size: u32, kind: StoredKind) -> StoredSlot {
    StoredSlot {
        at,
        offset,
        size,
        bits: None,
        kind,
    }
}

fn field(name: &str, offset: u32, shape: u32) -> ShapeField {
    ShapeField {
        name: name.into(),
        offset,
        shape,
    }
}

/// `type Label(at: Point, name: Str | Empty)` with
/// `type Point(x: Int16, y: Int16)`: `at` in four bytes after the
/// header, `name` as a tag byte and the string's two words after it.
fn shapes() -> Shapes {
    let int16 = StoredKind::Int { signed: true };
    Shapes {
        shapes: vec![
            Shape::Number(Number::Signed),
            Shape::Inline {
                name: Some("Point".into()),
                fields: vec![field("x", 0, 0), field("y", 1, 0)],
                words: 2,
            },
            Shape::Stored {
                form: 1,
                size: 4,
                slots: vec![slot(0, 0, 2, int16.clone()), slot(1, 2, 2, int16)],
                words: 2,
            },
            Shape::Str,
            Shape::Variant {
                members: vec![(STR, 3), (EMPTY, 5)],
                words: 3,
            },
            Shape::Tag("Empty".into()),
            Shape::Stored {
                form: 4,
                size: 24,
                slots: vec![slot(
                    0,
                    0,
                    24,
                    StoredKind::Union {
                        tag: StoredTag::Bytes { offset: 0, size: 1 },
                        members: vec![
                            (STR, vec![slot(1, 8, 16, StoredKind::Words)]),
                            (EMPTY, Vec::new()),
                        ],
                    },
                )],
                words: 3,
            },
            Shape::Record {
                name: Some("Label".into()),
                fields: vec![field("at", 16, 2), field("name", 24, 6)],
            },
        ],
        records: vec![(LABEL, 7)],
        boxes: vec![(7, LABEL, 48)],
    }
}

#[test]
fn stored_fields_go_through_their_shapes() {
    let shapes = Shapes::decode(&shapes().encode()).expect("the shapes encode");
    // The string's buffer is there only when the tag says it is a string.
    let types = Types::new([(
        LABEL,
        TypeDescriptor::Record {
            counted: vec![CountedField::Guarded {
                offset: 32,
                guards: vec![FieldGuard::Tag {
                    offset: 24,
                    tags: vec![0],
                }],
            }],
            dispose: None,
        },
    )]);
    let text = "a name longer than fifteen bytes";
    let mut bytes = 7u32.to_le_bytes().to_vec();
    bytes.extend(3u64.to_le_bytes());
    bytes.extend((-4i64 as u64).to_le_bytes());
    bytes.extend(0u32.to_le_bytes());
    bytes.extend((text.len() as u64).to_le_bytes());
    bytes.extend(text.as_bytes());
    let mut heap = Heap::new();
    // SAFETY: the shapes lay the box out as the descriptor has it.
    unsafe {
        let words = decode_value(&bytes, &shapes, 7, &mut heap, &types).expect("the bytes fit");
        let ptr = words[0] as *mut u8;
        let at = std::slice::from_raw_parts(ptr.add(16), 4);
        assert_eq!(at, [3, 0, 0xfc, 0xff]);
        assert_eq!(*ptr.add(24), 0);
        assert_eq!(
            print_value(&words, &shapes, 7, &types, PrintLimits::default()),
            format!("Label(at: Point(x: 3, y: -4), name: \"{text}\")")
        );
        let again = encode_value(&words, &shapes, 7, &types).expect("it encodes");
        assert_eq!(again, bytes);
        release_box(&mut heap, &types, ptr);
    }
    assert_eq!(heap.live_blocks(), 0);
}
