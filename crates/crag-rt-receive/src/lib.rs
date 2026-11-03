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

//! The runtime archive with the receiver of code (Implementation Plan
//! §11.10.4 and §11.10.9): `crag-rt` with the feature `receive`, built as
//! a static library of its own, `libcrag_rt_receive.a`. A release
//! executable that runs received code links with it in place of
//! `libcrag_rt.a`; it carries the compiler's front end and code generator,
//! which check and compile the code the program receives.

pub use crag_rt::MAIN;
