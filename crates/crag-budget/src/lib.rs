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

//! Budgets of code transport (Specification §18.7, Implementation Plan
//! §11.10.9): what all the code one sender sends may take from a
//! receiver.
//!
//! - [`document`]: budget documents, salts, tokens and token files, which
//!   `crag lmt new` writes.
//! - [`message`]: the bytes `send` writes and `decode` reads: a stamp, a
//!   tree and the environment of its closure.
//! - [`registry`]: the budgets a process enforces as a receiver and the
//!   stamps it sends under, read from its budget directory at startup,
//!   with what each has taken.

pub mod document;
pub mod message;
pub mod registry;

pub use document::{Document, KEY, Limits, Origin};
pub use message::{Message, Stamp};
pub use registry::{Grant, Refusal, Registry, Usage};
