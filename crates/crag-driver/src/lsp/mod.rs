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

//! The language server (Implementation Plan §11.8.1, Specification §20.8):
//! `crag lsp` speaks the Language Server Protocol on standard input and
//! output.
//!
//! The main thread owns the database. It applies edits as they arrive and
//! hands every request, with a snapshot of the database, to a thread of
//! its own, which answers it directly. An edit cancels the queries still
//! running on older snapshots: their requests are answered with
//! `ContentModified`. After each edit a thread publishes the diagnostics of
//! the project's modules, unless a newer edit came first.
//!
//! The server ends when the client sends `exit` or closes its end of the
//! input.

mod analysis;
pub(crate) mod rpc;
mod server;
mod text;

pub use server::serve;
