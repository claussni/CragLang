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

//! The bytes of code on the wire: what `send` writes and `decode` reads.
//!
//! - The magic `CRAGX` and the format's version, one byte.
//! - A stamp, or a zero byte for none: a one byte, the document's name
//!   and the budget's name, each a four-byte length and its UTF-8 bytes,
//!   the sequence number, eight bytes, and the MAC, 32 bytes.
//! - The tree: an eight-byte length and its bytes.
//! - The environment of its closure, in the Solid value codec: an
//!   eight-byte length and its bytes.
//!
//! Numbers are little-endian. The MAC is BLAKE3 keyed by the budget's
//! token over the tree's hash, the environment's hash and the sequence
//! number, so a stamp holds for this code with these captures only, and
//! the token never travels.

use crate::document::KEY;

const MAGIC: &[u8] = b"CRAGX";
const VERSION: u8 = 1;

/// What a sender stamps code with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Stamp {
    pub document: String,
    pub budget: String,
    pub sequence: u64,
    pub mac: [u8; KEY],
}

/// Code on the wire.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Message {
    pub stamp: Option<Stamp>,
    pub tree: Vec<u8>,
    pub env: Vec<u8>,
}

/// The MAC of a stamp.
pub fn mac(token: &[u8; KEY], tree: &[u8], env: &[u8], sequence: u64) -> [u8; KEY] {
    let mut hasher = blake3::Hasher::new_keyed(token);
    hasher.update(blake3::hash(tree).as_bytes());
    hasher.update(blake3::hash(env).as_bytes());
    hasher.update(&sequence.to_le_bytes());
    *hasher.finalize().as_bytes()
}

/// Whether two MACs are equal, compared in constant time.
pub fn same_mac(a: &[u8; KEY], b: &[u8; KEY]) -> bool {
    blake3::Hash::from(*a) == blake3::Hash::from(*b)
}

impl Message {
    pub fn encode(&self) -> Vec<u8> {
        let mut out = MAGIC.to_vec();
        out.push(VERSION);
        match &self.stamp {
            None => out.push(0),
            Some(stamp) => {
                out.push(1);
                for name in [&stamp.document, &stamp.budget] {
                    out.extend((name.len() as u32).to_le_bytes());
                    out.extend(name.as_bytes());
                }
                out.extend(stamp.sequence.to_le_bytes());
                out.extend(stamp.mac);
            }
        }
        for part in [&self.tree, &self.env] {
            out.extend((part.len() as u64).to_le_bytes());
            out.extend(part);
        }
        out
    }

    pub fn decode(bytes: &[u8]) -> Result<Message, String> {
        let mut r = Reader { bytes, at: 0 };
        if r.take(MAGIC.len())? != MAGIC {
            return Err("the bytes lack the magic of code".into());
        }
        let version = r.take(1)?[0];
        if version != VERSION {
            return Err(format!("code of format version {version}, not {VERSION}"));
        }
        let stamp = match r.take(1)?[0] {
            0 => None,
            1 => {
                let document = r.name()?;
                let budget = r.name()?;
                let sequence = u64::from_le_bytes(r.take(8)?.try_into().unwrap());
                let mac = r.take(KEY)?.try_into().unwrap();
                Some(Stamp {
                    document,
                    budget,
                    sequence,
                    mac,
                })
            }
            _ => return Err("a malformed stamp".into()),
        };
        let tree = r.part()?.to_vec();
        let env = r.part()?.to_vec();
        if r.at != bytes.len() {
            return Err("bytes after the code".into());
        }
        Ok(Message { stamp, tree, env })
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> Result<&'a [u8], String> {
        let end = self.at.checked_add(n).filter(|&e| e <= self.bytes.len());
        let end = end.ok_or("the code ends early")?;
        let part = &self.bytes[self.at..end];
        self.at = end;
        Ok(part)
    }

    fn name(&mut self) -> Result<String, String> {
        let n = u32::from_le_bytes(self.take(4)?.try_into().unwrap());
        let bytes = self.take(n as usize)?;
        String::from_utf8(bytes.to_vec()).map_err(|_| "a name that is not UTF-8".into())
    }

    fn part(&mut self) -> Result<&'a [u8], String> {
        let n = u64::from_le_bytes(self.take(8)?.try_into().unwrap());
        let n = usize::try_from(n).map_err(|_| "a part too long")?;
        self.take(n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_message_round_trips_and_malformed_bytes_are_refused() {
        let stamp = Stamp {
            document: "d".into(),
            budget: "acme".into(),
            sequence: 9,
            mac: mac(&[1; KEY], b"tree", b"env", 9),
        };
        for message in [
            Message {
                stamp: Some(stamp),
                tree: b"tree".to_vec(),
                env: b"env".to_vec(),
            },
            Message {
                stamp: None,
                tree: Vec::new(),
                env: b"e".to_vec(),
            },
        ] {
            let bytes = message.encode();
            assert_eq!(Message::decode(&bytes).unwrap(), message);
            for cut in 0..bytes.len() {
                assert!(Message::decode(&bytes[..cut]).is_err(), "{cut}");
            }
            let mut longer = bytes.clone();
            longer.push(0);
            assert!(Message::decode(&longer).is_err());
        }
        assert!(
            Message::decode(b"CRAGX\x02\x00")
                .unwrap_err()
                .contains("version")
        );
    }

    #[test]
    fn the_mac_covers_tree_captures_and_number() {
        let m = mac(&[1; KEY], b"t", b"e", 1);
        assert!(same_mac(&m, &mac(&[1; KEY], b"t", b"e", 1)));
        assert!(!same_mac(&m, &mac(&[1; KEY], b"u", b"e", 1)));
        assert!(!same_mac(&m, &mac(&[1; KEY], b"t", b"f", 1)));
        assert!(!same_mac(&m, &mac(&[1; KEY], b"t", b"e", 2)));
        assert!(!same_mac(&m, &mac(&[2; KEY], b"t", b"e", 1)));
    }
}
