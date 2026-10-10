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
//! §11.6.1).
//!
//! A frame is the length of its body as four little-endian bytes, then the
//! body: a tag byte and the message's fields, integers little-endian. The
//! image's first message is `Hello` with the version of the protocol it
//! speaks, which the host checks before it sends anything. Messages that
//! load code, evaluate input and print values come with the components
//! that use them (§11.6.2, §11.6.3, §11.6.5).

use std::io::{self, Read, Write};

/// The version of the protocol, raised whenever a message changes.
pub const PROTOCOL_VERSION: u32 = 1;

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
}

const HELLO: u8 = 0;
const PING: u8 = 1;
const PONG: u8 = 2;
const SHUTDOWN: u8 = 3;

impl Message {
    /// The body of the message's frame.
    pub fn encode(&self) -> Vec<u8> {
        let mut body = Vec::new();
        match self {
            Message::Hello { version, pid } => {
                body.push(HELLO);
                body.extend(version.to_le_bytes());
                body.extend(pid.to_le_bytes());
            }
            Message::Ping(n) => {
                body.push(PING);
                body.extend(n.to_le_bytes());
            }
            Message::Pong(n) => {
                body.push(PONG);
                body.extend(n.to_le_bytes());
            }
            Message::Shutdown => body.push(SHUTDOWN),
        }
        body
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
            tag => return Err(invalid(format!("a message with the unknown tag {tag}"))),
        };
        match r.0.len() {
            0 => Ok(message),
            n => Err(invalid(format!("{n} bytes after a message"))),
        }
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
        ]
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
    }
}
