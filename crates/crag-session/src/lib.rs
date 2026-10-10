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

//! The session manager (Implementation Plan §11.6.1): user code runs in
//! image processes apart from the host, so a crash or a runaway loop in it
//! never takes the compiler down (Specification §20.1). The host starts
//! the images, talks to them over a local socket in length-prefixed,
//! versioned messages, and starts a fresh image when one dies. The host
//! compiles; an image loads the code it is shipped and runs it (§11.6.3).

pub mod host;
pub mod image;
pub mod protocol;

pub use host::{
    ImageCommand, ImageExit, ImageHandle, ImageKind, ImageState, RunResult, Session, SessionError,
    describe, receive, send, spawn_image,
};
pub use image::{Image, serve};
pub use protocol::{
    Fill, Message, PROTOCOL_VERSION, ShippedFunction, Stub, read_message, write_message,
};
