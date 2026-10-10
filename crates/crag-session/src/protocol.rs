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

//! The messages between the host and an image (Implementation Plan
//! §11.6.1, §11.6.3).
//!
//! A frame is the length of its body as four little-endian bytes, then the
//! body: a tag byte and the message's fields. Integers are little-endian, a
//! sequence is its length as a `u32` and then its items, and an enum is a
//! tag byte and then its fields. The image's first message is `Hello` with
//! the version of the protocol it speaks, which the host checks before it
//! sends anything. Messages that evaluate input and print values come with
//! the components that use them (§11.6.2, §11.6.5).

use std::io::{self, Read, Write};

use crag_abi::{
    CodeObject, CountedField, ElementLayout, FuncId, Reloc, RelocKind, RelocTarget, RuntimeFn,
    SlotKey, StackCheck, StackMap, TrapKind, TypeDescriptor,
};

/// The version of the protocol, raised whenever a message changes.
pub const PROTOCOL_VERSION: u32 = 4;

/// The longest body a frame may have; a longer length means the stream is
/// corrupt.
pub const MAX_FRAME: u32 = 1 << 30;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Message {
    /// From the image, first: the protocol it speaks and its process id.
    Hello { version: u32, pid: u32 },
    /// From the host: asks for a `Pong` with the same number.
    Ping(u64),
    /// From the image: the answer to a `Ping`.
    Pong(u64),
    /// From the host: the image ends with status 0.
    Shutdown,
    /// From the host: code to load, with the descriptors of the types it
    /// uses and the entry stubs to run it with. The functions are loaded
    /// together, and may call each other and what is already loaded. Then
    /// the cells of the values in `reset` are emptied, so the values are
    /// computed again (§11.6.2).
    Load {
        types: Vec<(u32, TypeDescriptor)>,
        stubs: Vec<Stub>,
        functions: Vec<ShippedFunction>,
        reset: Vec<SlotKey>,
    },
    /// From the image: everything in the `Load` is loaded.
    Loaded,
    /// From the host: runs a loaded function without parameters on a fiber
    /// of its own.
    Run(FuncId),
    /// From the image: the run finished with these result words.
    Finished(Vec<u64>),
    /// From the image: the run trapped.
    Trapped {
        kind: TrapKind,
        position: Option<u32>,
        stack: Vec<FuncId>,
    },
    /// From the image: it could not do what the host asked, and why; it
    /// is as it was before.
    Failed(String),
}

/// A function's code, shipped to an image.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShippedFunction {
    pub id: FuncId,
    /// The signature of the slot it fills (§11.6.4).
    pub signature: u32,
    /// Words of parameters and results.
    pub params: u32,
    pub returns: u32,
    pub object: CodeObject,
}

/// An entry stub: code that calls a function with `params` parameter words
/// and `returns` result words from a fiber's start.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stub {
    pub params: u32,
    pub returns: u32,
    pub object: CodeObject,
}

const HELLO: u8 = 0;
const PING: u8 = 1;
const PONG: u8 = 2;
const SHUTDOWN: u8 = 3;
const LOAD: u8 = 4;
const LOADED: u8 = 5;
const RUN: u8 = 6;
const FINISHED: u8 = 7;
const TRAPPED: u8 = 8;
const FAILED: u8 = 9;

impl Message {
    /// The body of the message's frame.
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer(Vec::new());
        match self {
            Message::Hello { version, pid } => {
                w.u8(HELLO);
                w.u32(*version);
                w.u32(*pid);
            }
            Message::Ping(n) => {
                w.u8(PING);
                w.u64(*n);
            }
            Message::Pong(n) => {
                w.u8(PONG);
                w.u64(*n);
            }
            Message::Shutdown => w.u8(SHUTDOWN),
            Message::Load {
                types,
                stubs,
                functions,
                reset,
            } => {
                w.u8(LOAD);
                w.seq(types, |w, (index, d)| {
                    w.u32(*index);
                    w.descriptor(d);
                });
                w.seq(stubs, |w, s| {
                    w.u32(s.params);
                    w.u32(s.returns);
                    w.object(&s.object);
                });
                w.seq(functions, |w, f| w.function(f));
                w.seq(reset, |w, key| w.slot_key(key));
            }
            Message::Loaded => w.u8(LOADED),
            Message::Run(id) => {
                w.u8(RUN);
                w.u32(id.0);
            }
            Message::Finished(words) => {
                w.u8(FINISHED);
                w.seq(words, |w, x| w.u64(*x));
            }
            Message::Trapped {
                kind,
                position,
                stack,
            } => {
                w.u8(TRAPPED);
                w.u32(*kind as u32);
                match position {
                    None => w.u8(0),
                    Some(p) => {
                        w.u8(1);
                        w.u32(*p);
                    }
                }
                w.seq(stack, |w, f| w.u32(f.0));
            }
            Message::Failed(why) => {
                w.u8(FAILED);
                w.seq(why.as_bytes(), |w, b| w.u8(*b));
            }
        }
        w.0
    }

    /// The message a frame's body holds.
    pub fn decode(body: &[u8]) -> io::Result<Message> {
        let mut r = Reader(body);
        let message = match r.u8()? {
            HELLO => Message::Hello {
                version: r.u32()?,
                pid: r.u32()?,
            },
            PING => Message::Ping(r.u64()?),
            PONG => Message::Pong(r.u64()?),
            SHUTDOWN => Message::Shutdown,
            LOAD => Message::Load {
                types: r.seq(|r| Ok((r.u32()?, r.descriptor()?)))?,
                stubs: r.seq(|r| {
                    Ok(Stub {
                        params: r.u32()?,
                        returns: r.u32()?,
                        object: r.object()?,
                    })
                })?,
                functions: r.seq(Reader::function)?,
                reset: r.seq(Reader::slot_key)?,
            },
            LOADED => Message::Loaded,
            RUN => Message::Run(FuncId(r.u32()?)),
            FINISHED => Message::Finished(r.seq(Reader::u64)?),
            TRAPPED => Message::Trapped {
                kind: {
                    let kind = r.u32()?;
                    TrapKind::from_index(u64::from(kind))
                        .ok_or_else(|| invalid(format!("the unknown trap kind {kind}")))?
                },
                position: match r.u8()? {
                    0 => None,
                    1 => Some(r.u32()?),
                    tag => return Err(invalid(format!("an option with the tag {tag}"))),
                },
                stack: r.seq(|r| Ok(FuncId(r.u32()?)))?,
            },
            FAILED => {
                let bytes = r.seq(Reader::u8)?;
                Message::Failed(
                    String::from_utf8(bytes)
                        .map_err(|_| invalid("a reason that is not UTF-8".into()))?,
                )
            }
            tag => return Err(invalid(format!("a message with the unknown tag {tag}"))),
        };
        match r.0.len() {
            0 => Ok(message),
            n => Err(invalid(format!("{n} bytes after a message"))),
        }
    }
}

impl ShippedFunction {
    /// The function as the protocol writes it, which its content hash is
    /// taken of.
    pub fn encode(&self) -> Vec<u8> {
        let mut w = Writer(Vec::new());
        w.function(self);
        w.0
    }
}

/// Writes a message as one frame.
pub fn write_message(w: &mut impl Write, message: &Message) -> io::Result<()> {
    let body = message.encode();
    let len = u32::try_from(body.len())
        .ok()
        .filter(|&len| len <= MAX_FRAME)
        .ok_or_else(|| invalid("a message too long for a frame".into()))?;
    let mut frame = Vec::with_capacity(4 + body.len());
    frame.extend(len.to_le_bytes());
    frame.extend(body);
    w.write_all(&frame)?;
    w.flush()
}

/// Reads one frame and its message. The end of the stream before a frame
/// starts is `UnexpectedEof`, as is one inside a frame.
pub fn read_message(r: &mut impl Read) -> io::Result<Message> {
    let mut len = [0; 4];
    r.read_exact(&mut len)?;
    let len = u32::from_le_bytes(len);
    if len > MAX_FRAME {
        return Err(invalid(format!("a frame of {len} bytes")));
    }
    let mut body = vec![0; len as usize];
    r.read_exact(&mut body)?;
    Message::decode(&body)
}

fn invalid(message: String) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

/// A body, written from the front.
struct Writer(Vec<u8>);

impl Writer {
    fn u8(&mut self, x: u8) {
        self.0.push(x);
    }

    fn u32(&mut self, x: u32) {
        self.0.extend(x.to_le_bytes());
    }

    fn u64(&mut self, x: u64) {
        self.0.extend(x.to_le_bytes());
    }

    fn seq<T>(&mut self, items: &[T], mut item: impl FnMut(&mut Writer, &T)) {
        // A frame cannot hold more items than this anyway.
        self.u32(items.len() as u32);
        for x in items {
            item(self, x);
        }
    }

    fn slot_key(&mut self, key: &SlotKey) {
        self.u32(key.func.0);
        self.u32(key.signature);
    }

    fn function(&mut self, f: &ShippedFunction) {
        self.u32(f.id.0);
        self.u32(f.signature);
        self.u32(f.params);
        self.u32(f.returns);
        self.object(&f.object);
    }

    fn object(&mut self, o: &CodeObject) {
        self.seq(&o.code, |w, b| w.u8(*b));
        self.u32(o.align);
        self.u32(o.entry);
        self.seq(&o.relocs, |w, r| {
            w.u32(r.offset);
            let RelocKind::Abs64 = r.kind;
            w.u8(0);
            match r.target {
                RelocTarget::Function(id) => {
                    w.u8(0);
                    w.u32(id.0);
                }
                RelocTarget::Runtime(func) => {
                    w.u8(1);
                    w.u32(func as u32);
                }
                RelocTarget::Local(offset) => {
                    w.u8(2);
                    w.u32(offset);
                }
                RelocTarget::Slot(key) => {
                    w.u8(3);
                    w.slot_key(&key);
                }
                RelocTarget::Cell(key) => {
                    w.u8(4);
                    w.slot_key(&key);
                }
            }
            w.u64(r.addend as u64);
        });
        self.u32(o.footprint);
        match o.stack_check {
            StackCheck::None => self.u8(0),
            StackCheck::Margin => self.u8(1),
            StackCheck::Sized { needed } => {
                self.u8(2);
                self.u32(needed);
            }
        }
        self.seq(&o.stack_maps, |w, m| {
            w.u32(m.return_offset);
            w.seq(&m.slots, |w, s| w.u32(*s));
        });
    }

    fn descriptor(&mut self, d: &TypeDescriptor) {
        match d {
            TypeDescriptor::Record { counted } => {
                self.u8(0);
                self.counted(counted);
            }
            TypeDescriptor::List { element } => {
                self.u8(1);
                self.element(element);
            }
            TypeDescriptor::Map { key, value } => {
                self.u8(2);
                self.element(key);
                self.element(value);
            }
        }
    }

    fn element(&mut self, e: &ElementLayout) {
        self.u32(e.words);
        self.counted(&e.counted);
    }

    fn counted(&mut self, fields: &[CountedField]) {
        self.seq(fields, |w, f| match f {
            CountedField::Box(offset) => {
                w.u8(0);
                w.u32(*offset);
            }
            CountedField::Union { offset, boxed } => {
                w.u8(1);
                w.u32(*offset);
                w.seq(boxed, |w, b| w.u32(*b));
            }
        });
    }
}

/// The fields of a body, read from the front.
struct Reader<'a>(&'a [u8]);

impl Reader<'_> {
    fn take<const N: usize>(&mut self) -> io::Result<[u8; N]> {
        let Some((bytes, rest)) = self.0.split_first_chunk::<N>() else {
            return Err(invalid("a message cut short".into()));
        };
        self.0 = rest;
        Ok(*bytes)
    }

    fn u8(&mut self) -> io::Result<u8> {
        Ok(self.take::<1>()?[0])
    }

    fn u32(&mut self) -> io::Result<u32> {
        Ok(u32::from_le_bytes(self.take()?))
    }

    fn u64(&mut self) -> io::Result<u64> {
        Ok(u64::from_le_bytes(self.take()?))
    }

    /// A sequence. Its length is checked against the bytes left, which
    /// every item takes at least one of, so a corrupt length cannot make
    /// the reader allocate more than the frame holds.
    fn seq<T>(&mut self, mut item: impl FnMut(&mut Self) -> io::Result<T>) -> io::Result<Vec<T>> {
        let len = self.u32()? as usize;
        if len > self.0.len() {
            return Err(invalid("a message cut short".into()));
        }
        let mut items = Vec::with_capacity(len);
        for _ in 0..len {
            items.push(item(self)?);
        }
        Ok(items)
    }

    fn slot_key(&mut self) -> io::Result<SlotKey> {
        Ok(SlotKey {
            func: FuncId(self.u32()?),
            signature: self.u32()?,
        })
    }

    fn function(&mut self) -> io::Result<ShippedFunction> {
        Ok(ShippedFunction {
            id: FuncId(self.u32()?),
            signature: self.u32()?,
            params: self.u32()?,
            returns: self.u32()?,
            object: self.object()?,
        })
    }

    fn object(&mut self) -> io::Result<CodeObject> {
        Ok(CodeObject {
            code: self.seq(Reader::u8)?,
            align: self.u32()?,
            entry: self.u32()?,
            relocs: self.seq(|r| {
                let offset = r.u32()?;
                let kind = match r.u8()? {
                    0 => RelocKind::Abs64,
                    tag => return Err(invalid(format!("a relocation kind with the tag {tag}"))),
                };
                let target = match r.u8()? {
                    0 => RelocTarget::Function(FuncId(r.u32()?)),
                    1 => {
                        let index = r.u32()?;
                        RelocTarget::Runtime(RuntimeFn::from_index(index).ok_or_else(|| {
                            invalid(format!("the unknown runtime function {index}"))
                        })?)
                    }
                    2 => RelocTarget::Local(r.u32()?),
                    3 => RelocTarget::Slot(r.slot_key()?),
                    4 => RelocTarget::Cell(r.slot_key()?),
                    tag => return Err(invalid(format!("a relocation target with the tag {tag}"))),
                };
                Ok(Reloc {
                    offset,
                    kind,
                    target,
                    addend: r.u64()? as i64,
                })
            })?,
            footprint: self.u32()?,
            stack_check: match self.u8()? {
                0 => StackCheck::None,
                1 => StackCheck::Margin,
                2 => StackCheck::Sized {
                    needed: self.u32()?,
                },
                tag => return Err(invalid(format!("a stack check with the tag {tag}"))),
            },
            stack_maps: self.seq(|r| {
                Ok(StackMap {
                    return_offset: r.u32()?,
                    slots: r.seq(Reader::u32)?,
                })
            })?,
        })
    }

    fn descriptor(&mut self) -> io::Result<TypeDescriptor> {
        Ok(match self.u8()? {
            0 => TypeDescriptor::Record {
                counted: self.counted()?,
            },
            1 => TypeDescriptor::List {
                element: self.element()?,
            },
            2 => TypeDescriptor::Map {
                key: self.element()?,
                value: self.element()?,
            },
            tag => return Err(invalid(format!("a type descriptor with the tag {tag}"))),
        })
    }

    fn element(&mut self) -> io::Result<ElementLayout> {
        Ok(ElementLayout {
            words: self.u32()?,
            counted: self.counted()?,
        })
    }

    fn counted(&mut self) -> io::Result<Vec<CountedField>> {
        self.seq(|r| {
            Ok(match r.u8()? {
                0 => CountedField::Box(r.u32()?),
                1 => CountedField::Union {
                    offset: r.u32()?,
                    boxed: r.seq(Reader::u32)?,
                },
                tag => return Err(invalid(format!("a counted field with the tag {tag}"))),
            })
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn all() -> Vec<Message> {
        vec![
            Message::Hello {
                version: PROTOCOL_VERSION,
                pid: 4711,
            },
            Message::Ping(u64::MAX),
            Message::Pong(7),
            Message::Shutdown,
            Message::Load {
                types: vec![
                    (
                        3,
                        TypeDescriptor::Record {
                            counted: vec![
                                CountedField::Box(16),
                                CountedField::Union {
                                    offset: 24,
                                    boxed: vec![3, 5],
                                },
                            ],
                        },
                    ),
                    (
                        5,
                        TypeDescriptor::List {
                            element: ElementLayout {
                                words: 2,
                                counted: vec![CountedField::Box(8)],
                            },
                        },
                    ),
                    (
                        6,
                        TypeDescriptor::Map {
                            key: ElementLayout::default(),
                            value: ElementLayout {
                                words: 1,
                                counted: Vec::new(),
                            },
                        },
                    ),
                ],
                stubs: vec![Stub {
                    params: 0,
                    returns: 2,
                    object: object(StackCheck::None),
                }],
                functions: vec![
                    ShippedFunction {
                        id: FuncId(9),
                        signature: 7,
                        params: 1,
                        returns: 1,
                        object: object(StackCheck::Margin),
                    },
                    ShippedFunction {
                        id: FuncId(10),
                        signature: 7,
                        params: 0,
                        returns: 0,
                        object: object(StackCheck::Sized { needed: 4096 }),
                    },
                ],
                reset: vec![SlotKey {
                    func: FuncId(10),
                    signature: 2,
                }],
            },
            Message::Loaded,
            Message::Run(FuncId(9)),
            Message::Finished(vec![0, u64::MAX]),
            Message::Trapped {
                kind: TrapKind::Overflow,
                position: Some(17),
                stack: vec![FuncId(9), FuncId(10)],
            },
            Message::Trapped {
                kind: TrapKind::Unsupported,
                position: None,
                stack: Vec::new(),
            },
            Message::Failed("function 3 is not loaded".into()),
        ]
    }

    fn object(stack_check: StackCheck) -> CodeObject {
        CodeObject {
            code: vec![0x90, 0xc3, 0, 0, 0, 0, 0, 0, 0, 0],
            align: 16,
            entry: 1,
            relocs: vec![
                Reloc {
                    offset: 2,
                    kind: RelocKind::Abs64,
                    target: RelocTarget::Function(FuncId(10)),
                    addend: -8,
                },
                Reloc {
                    offset: 2,
                    kind: RelocKind::Abs64,
                    target: RelocTarget::Runtime(RuntimeFn::Trap),
                    addend: 0,
                },
                Reloc {
                    offset: 2,
                    kind: RelocKind::Abs64,
                    target: RelocTarget::Local(1),
                    addend: i64::MAX,
                },
                Reloc {
                    offset: 2,
                    kind: RelocKind::Abs64,
                    target: RelocTarget::Slot(SlotKey {
                        func: FuncId(9),
                        signature: u32::MAX,
                    }),
                    addend: 0,
                },
                Reloc {
                    offset: 2,
                    kind: RelocKind::Abs64,
                    target: RelocTarget::Cell(SlotKey {
                        func: FuncId(10),
                        signature: 2,
                    }),
                    addend: 0,
                },
            ],
            footprint: 48,
            stack_check,
            stack_maps: vec![StackMap {
                return_offset: 1,
                slots: vec![0, 8],
            }],
        }
    }

    #[test]
    fn messages_survive_a_stream() {
        let mut stream = Vec::new();
        for m in all() {
            write_message(&mut stream, &m).unwrap();
        }
        let mut r = stream.as_slice();
        for m in all() {
            assert_eq!(read_message(&mut r).unwrap(), m);
        }
        let end = read_message(&mut r).unwrap_err();
        assert_eq!(end.kind(), io::ErrorKind::UnexpectedEof);
    }

    #[test]
    fn frames_are_length_prefixed() {
        let mut stream = Vec::new();
        write_message(&mut stream, &Message::Pong(0x0102)).unwrap();
        assert_eq!(stream, [9, 0, 0, 0, PONG, 2, 1, 0, 0, 0, 0, 0, 0]);
    }

    #[test]
    fn broken_frames_are_rejected() {
        let invalid = |bytes: &[u8]| {
            let mut r = bytes;
            read_message(&mut r).unwrap_err().kind()
        };
        // Cut short inside the frame, then inside the body.
        assert_eq!(
            invalid(&[9, 0, 0, 0, PONG, 2]),
            io::ErrorKind::UnexpectedEof
        );
        assert_eq!(invalid(&[2, 0, 0, 0, PONG, 2]), io::ErrorKind::InvalidData);
        assert_eq!(invalid(&[1, 0, 0, 0, 99]), io::ErrorKind::InvalidData);
        assert_eq!(
            invalid(&[2, 0, 0, 0, SHUTDOWN, 0]),
            io::ErrorKind::InvalidData
        );
        assert_eq!(invalid(&[0, 0, 0, 0x41]), io::ErrorKind::InvalidData);
        assert_eq!(invalid(&[0, 0, 0, 0]), io::ErrorKind::InvalidData);
        // A sequence longer than the frame, a trap kind, a runtime function
        // and an option tag that do not exist.
        assert_eq!(
            invalid(&[5, 0, 0, 0, FINISHED, 0xff, 0xff, 0xff, 0xff]),
            io::ErrorKind::InvalidData
        );
        assert_eq!(
            invalid(&[10, 0, 0, 0, TRAPPED, 99, 0, 0, 0, 0, 0, 0, 0, 0]),
            io::ErrorKind::InvalidData
        );
        assert_eq!(
            invalid(&[10, 0, 0, 0, TRAPPED, 0, 0, 0, 0, 2, 0, 0, 0, 0]),
            io::ErrorKind::InvalidData
        );
        let mut load = vec![LOAD, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0];
        load.extend(
            ShippedFunction {
                id: FuncId(1),
                signature: 7,
                params: 0,
                returns: 0,
                object: CodeObject {
                    relocs: vec![Reloc {
                        offset: 0,
                        kind: RelocKind::Abs64,
                        target: RelocTarget::Runtime(RuntimeFn::Trap),
                        addend: 0,
                    }],
                    ..object(StackCheck::Margin)
                },
            }
            .encode(),
        );
        // No cells to empty.
        load.extend([0, 0, 0, 0]);
        // The runtime function's index, after the function's id, signature,
        // words, code, alignment, entry, relocation count, offset and kinds.
        let at = 13 + 16 + 4 + 10 + 8 + 4 + 4 + 2;
        assert_eq!(load[at - 1], 1);
        assert_eq!(load[at], RuntimeFn::Trap as u8);
        let broken = |at: usize, byte: u8| {
            let mut load = load.clone();
            load[at] = byte;
            let mut frame = (load.len() as u32).to_le_bytes().to_vec();
            frame.extend(load);
            invalid(&frame)
        };
        let mut frame = (load.len() as u32).to_le_bytes().to_vec();
        frame.extend(&load);
        assert!(read_message(&mut frame.as_slice()).is_ok());
        assert_eq!(broken(at, 200), io::ErrorKind::InvalidData);
        // A relocation target after the cell's tag.
        assert_eq!(broken(at - 1, 5), io::ErrorKind::InvalidData);
    }
}
