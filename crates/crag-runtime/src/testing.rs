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

//! What the unit tests of the collections share.

use crate::heap::{Heap, alloc_box};

/// The type index of a record with one word, which tests put in
/// collections to see that they count what they hold.
pub(crate) const REC: u32 = 9;

/// A record of type `REC` holding `v`.
pub(crate) fn boxed(heap: &mut Heap, v: u64) -> *mut u8 {
    let ptr = alloc_box(heap, 24, REC.into());
    // SAFETY: the box has the field.
    unsafe { ptr.add(16).cast::<u64>().write(v) };
    ptr
}

/// The word in a record of type `REC`.
///
/// # Safety
///
/// `ptr` points at a live record of type `REC`.
pub(crate) unsafe fn unboxed(ptr: *mut u8) -> u64 {
    // SAFETY: as the caller promises.
    unsafe { ptr.add(16).cast::<u64>().read() }
}

/// A xorshift generator, so a test runs the same way every time.
pub(crate) struct Rng(pub u64);

impl Rng {
    pub(crate) fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    /// A number in `0..n`, for `n > 0`.
    pub(crate) fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}
