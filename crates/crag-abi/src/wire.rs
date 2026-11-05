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

//! Bytes as the toolchain's formats write and read them: integers
//! little-endian, a sequence as its length in a `u32` and then its items,
//! bytes and text as a sequence of bytes. [`Writer`] writes them, and
//! [`Reader`] reads them from bytes that may be anything: a read past the
//! end, or a sequence longer than the bytes left could hold, is an error,
//! so that no length in the bytes makes the reader allocate more than it
//! was given.
//!
//! A format reads with the error type of its own, which [`Malformed`]
//! converts into, and adds what it reads and writes of its own as a trait
//! on the two.

use std::fmt;
use std::io;
use std::marker::PhantomData;

/// Why bytes are not what was read of them.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Malformed {
    /// The bytes end before what was read of them.
    Short,
    /// Text that is not UTF-8.
    NotUtf8,
}

impl fmt::Display for Malformed {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self {
            Malformed::Short => "the bytes end early",
            Malformed::NotUtf8 => "text that is not UTF-8",
        })
    }
}

impl std::error::Error for Malformed {}

impl From<Malformed> for String {
    fn from(error: Malformed) -> String {
        error.to_string()
    }
}

impl From<Malformed> for io::Error {
    fn from(error: Malformed) -> io::Error {
        io::Error::new(io::ErrorKind::InvalidData, error.to_string())
    }
}

/// Bytes being written, in the field.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Writer(pub Vec<u8>);

impl Writer {
    pub fn u8(&mut self, x: u8) {
        self.0.push(x);
    }

    pub fn u32(&mut self, x: u32) {
        self.0.extend(x.to_le_bytes());
    }

    pub fn u64(&mut self, x: u64) {
        self.0.extend(x.to_le_bytes());
    }

    /// The bytes as they are, without their length.
    pub fn raw(&mut self, bytes: &[u8]) {
        self.0.extend_from_slice(bytes);
    }

    /// The bytes as a sequence: their length, then the bytes.
    pub fn bytes(&mut self, bytes: &[u8]) {
        self.u32(bytes.len() as u32);
        self.raw(bytes);
    }

    /// The text as the sequence of its UTF-8 bytes.
    pub fn text(&mut self, text: &str) {
        self.bytes(text.as_bytes());
    }

    /// The items as a sequence: their count, then each as `item` writes it.
    pub fn seq<T>(&mut self, items: &[T], mut item: impl FnMut(&mut Writer, &T)) {
        self.u32(items.len() as u32);
        for x in items {
            item(self, x);
        }
    }
}

/// Bytes being read from the front, with `E` as the error of the format
/// read, which a malformed read converts into.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reader<'a, E = Malformed> {
    left: &'a [u8],
    error: PhantomData<E>,
}

impl<'a, E: From<Malformed>> Reader<'a, E> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Reader {
            left: bytes,
            error: PhantomData,
        }
    }

    /// How many bytes are left.
    pub fn len(&self) -> usize {
        self.left.len()
    }

    /// Whether every byte was read.
    pub fn is_empty(&self) -> bool {
        self.left.is_empty()
    }

    /// The next `n` bytes.
    pub fn take(&mut self, n: usize) -> Result<&'a [u8], E> {
        let (head, rest) = self.left.split_at_checked(n).ok_or(Malformed::Short)?;
        self.left = rest;
        Ok(head)
    }

    /// The next `N` bytes.
    pub fn array<const N: usize>(&mut self) -> Result<[u8; N], E> {
        let (head, rest) = self.left.split_first_chunk().ok_or(Malformed::Short)?;
        self.left = rest;
        Ok(*head)
    }

    pub fn u8(&mut self) -> Result<u8, E> {
        Ok(self.array::<1>()?[0])
    }

    pub fn u32(&mut self) -> Result<u32, E> {
        Ok(u32::from_le_bytes(self.array()?))
    }

    pub fn u64(&mut self) -> Result<u64, E> {
        Ok(u64::from_le_bytes(self.array()?))
    }

    /// The count of a sequence, which no more bytes than are left can
    /// hold, as each item takes a byte at least.
    fn sequence_len(&mut self) -> Result<usize, E> {
        let n = self.u32()? as usize;
        match n <= self.len() {
            true => Ok(n),
            false => Err(Malformed::Short.into()),
        }
    }

    /// A sequence of bytes.
    pub fn bytes(&mut self) -> Result<&'a [u8], E> {
        let n = self.sequence_len()?;
        self.take(n)
    }

    /// A sequence of bytes as text.
    pub fn text(&mut self) -> Result<String, E> {
        let bytes = self.bytes()?.to_vec();
        Ok(String::from_utf8(bytes).map_err(|_| Malformed::NotUtf8)?)
    }

    /// A sequence of items, each as `item` reads it.
    pub fn seq<T>(&mut self, mut item: impl FnMut(&mut Self) -> Result<T, E>) -> Result<Vec<T>, E> {
        let n = self.sequence_len()?;
        let mut items = Vec::with_capacity(n);
        for _ in 0..n {
            items.push(item(self)?);
        }
        Ok(items)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn what_is_written_reads_back() {
        let mut w = Writer::default();
        w.u8(7);
        w.u32(70_000);
        w.u64(1 << 40);
        w.bytes(b"ab");
        w.text("c\u{e9}");
        w.seq(&[1u32, 2], |w, &x| w.u32(x));
        w.raw(&[9]);
        let mut r: Reader = Reader::new(&w.0);
        assert_eq!(r.u8(), Ok(7));
        assert_eq!(r.u32(), Ok(70_000));
        assert_eq!(r.u64(), Ok(1 << 40));
        assert_eq!(r.bytes(), Ok(&b"ab"[..]));
        assert_eq!(r.text(), Ok("c\u{e9}".to_string()));
        assert_eq!(r.seq(Reader::u32), Ok(vec![1, 2]));
        assert_eq!(r.array(), Ok([9]));
        assert!(r.is_empty());
    }

    #[test]
    fn short_or_forged_bytes_are_refused() {
        assert_eq!(
            Reader::<Malformed>::new(&[1, 2, 3]).u32(),
            Err(Malformed::Short)
        );
        assert_eq!(Reader::<Malformed>::new(&[]).u8(), Err(Malformed::Short));
        // A count past the end, before any item is allocated for.
        let forged = u32::MAX.to_le_bytes();
        let mut r: Reader = Reader::new(&forged);
        assert_eq!(r.seq(Reader::u8), Err(Malformed::Short));
        assert_eq!(
            Reader::<Malformed>::new(&forged).bytes(),
            Err(Malformed::Short)
        );
        // Bytes that are no text, and the error as a format has it.
        let mut w = Writer::default();
        w.bytes(&[0xff]);
        assert_eq!(
            Reader::<String>::new(&w.0).text(),
            Err("text that is not UTF-8".into())
        );
        assert_eq!(String::from(Malformed::Short), "the bytes end early");
    }
}
