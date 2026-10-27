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

//! JSON-RPC messages as the Language Server Protocol frames them: a
//! `Content-Length` header, an empty line, and the JSON body.

use std::io::{self, BufRead, Write};

use serde_json::Value;

/// The largest message accepted, so a broken client cannot make the
/// server allocate without bound.
const MAX_MESSAGE: usize = 64 << 20;

/// Reads the next message; `None` at the end of the input.
pub fn read(input: &mut impl BufRead) -> io::Result<Option<Value>> {
    let mut length = None;
    let mut line = String::new();
    loop {
        line.clear();
        if input.read_line(&mut line)? == 0 {
            return Ok(None);
        }
        if line.len() > 1024 {
            return Err(invalid("a header line is too long"));
        }
        let header = line.trim_end_matches(['\r', '\n']);
        if header.is_empty() {
            if length.is_some() {
                break;
            }
            // Blank lines before a header are tolerated.
            continue;
        }
        let Some((name, value)) = header.split_once(':') else {
            return Err(invalid("a header without `:`"));
        };
        if name.eq_ignore_ascii_case("content-length") {
            let n: usize = value
                .trim()
                .parse()
                .map_err(|_| invalid("a bad Content-Length"))?;
            if n > MAX_MESSAGE {
                return Err(invalid("a message is too long"));
            }
            length = Some(n);
        }
    }
    let mut body = vec![0; length.unwrap_or(0)];
    input.read_exact(&mut body)?;
    serde_json::from_slice(&body)
        .map(Some)
        .map_err(|e| invalid(&format!("bad JSON: {e}")))
}

/// Writes one message.
pub fn write(output: &mut dyn Write, message: &Value) -> io::Result<()> {
    let body = serde_json::to_vec(message)?;
    write!(output, "Content-Length: {}\r\n\r\n", body.len())?;
    output.write_all(&body)?;
    output.flush()
}

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.to_string())
}

/// Error codes of JSON-RPC and the protocol.
pub mod code {
    pub const INVALID_PARAMS: i64 = -32602;
    pub const METHOD_NOT_FOUND: i64 = -32601;
    pub const SERVER_NOT_INITIALIZED: i64 = -32002;
    pub const REQUEST_FAILED: i64 = -32803;
    pub const CONTENT_MODIFIED: i64 = -32801;
    pub const REQUEST_CANCELLED: i64 = -32800;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_message_reads_back() {
        let mut out = Vec::new();
        write(
            &mut out,
            &serde_json::json!({"jsonrpc": "2.0", "method": "x"}),
        )
        .unwrap();
        let mut input = io::Cursor::new(out);
        let message = read(&mut input).unwrap().unwrap();
        assert_eq!(message["method"], "x");
        assert!(read(&mut input).unwrap().is_none());
    }

    #[test]
    fn a_huge_length_is_refused() {
        let mut input = io::Cursor::new(b"Content-Length: 999999999999\r\n\r\n".to_vec());
        assert!(read(&mut input).is_err());
    }
}
