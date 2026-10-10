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

//! The image's side: the loop that answers the host (Implementation Plan
//! §11.6.1).

use std::io;
use std::os::unix::net::UnixStream;
use std::path::Path;

use crate::host::ImageKind;
use crate::protocol::{Message, PROTOCOL_VERSION, read_message, write_message};

/// Connects to the host at `socket`, says `Hello` and answers messages
/// until the host says `Shutdown` or goes away.
pub fn serve(kind: ImageKind, socket: &Path) -> io::Result<()> {
    let ImageKind::Scratch = kind;
    let mut stream = UnixStream::connect(socket)?;
    write_message(
        &mut stream,
        &Message::Hello {
            version: PROTOCOL_VERSION,
            pid: std::process::id(),
        },
    )?;
    loop {
        match read_message(&mut stream) {
            Ok(Message::Ping(n)) => write_message(&mut stream, &Message::Pong(n))?,
            Ok(Message::Shutdown) => return Ok(()),
            Ok(other) => {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("the host sent {other:?}"),
                ));
            }
            // The host is gone, so nothing is left to answer.
            Err(e) if e.kind() == io::ErrorKind::UnexpectedEof => return Ok(()),
            Err(e) => return Err(e),
        }
    }
}
