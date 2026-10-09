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

//! Reference counting (Plan §11.4.12).
//!
//! Generated code retains and releases inline (see `crag_abi`). When a
//! release takes a count to zero it calls `rt_release`, which frees the box
//! and releases its fields, using the descriptor of its type.
//!
//! Freeing does not recurse: a box whose count reaches zero while another
//! is freed goes on a list of boxes to free, linked through their count
//! words, which no one reads once the count is zero. A long chain of boxes
//! is therefore freed in a loop, with no stack to overflow and no memory to
//! allocate.

use std::mem::offset_of;
use std::ptr::null_mut;
use std::sync::atomic::{AtomicU64, Ordering, fence};

use crag_abi::{COUNT_OFFSET, CountedField, STATIC_COUNT, TYPE_INDEX_OFFSET, TypeDescriptor};

use crate::die;
use crate::fiber::{TaskContext, Worker};
use crate::heap::Heap;

/// The descriptors of an image's types, indexed by type index.
#[derive(Debug, Default)]
pub struct Types {
    descriptors: Vec<Option<TypeDescriptor>>,
}

impl Types {
    pub fn new(descriptors: impl IntoIterator<Item = (u32, TypeDescriptor)>) -> Types {
        let mut types = Types::default();
        for (index, descriptor) in descriptors {
            let index = index as usize;
            if types.descriptors.len() <= index {
                types.descriptors.resize(index + 1, None);
            }
            types.descriptors[index] = Some(descriptor);
        }
        types
    }

    pub fn get(&self, index: u32) -> Option<&TypeDescriptor> {
        self.descriptors.get(index as usize)?.as_ref()
    }
}

/// The count of the box at `ptr`.
///
/// # Safety
///
/// `ptr` points at a live box.
unsafe fn count<'a>(ptr: *mut u8) -> &'a AtomicU64 {
    // SAFETY: as the caller promises; the count is an aligned word.
    unsafe { &*ptr.offset(COUNT_OFFSET as isize).cast::<AtomicU64>() }
}

/// Gives up a reference to a box; whether it was the last. A static box is
/// not counted.
///
/// # Safety
///
/// The caller owns a reference to the box at `ptr`.
unsafe fn release(ptr: *mut u8) -> bool {
    // SAFETY: as the caller promises.
    let count = unsafe { count(ptr) };
    if count.load(Ordering::Relaxed) & STATIC_COUNT != 0 {
        return false;
    }
    if count.fetch_sub(1, Ordering::Release) != 1 {
        return false;
    }
    // What other threads did with the box before they released it happens
    // before it is freed.
    fence(Ordering::Acquire);
    true
}

/// Frees a box whose count has reached zero, and releases its fields,
/// freeing those whose counts reach zero in turn.
///
/// # Safety
///
/// The count of the box at `ptr` has just reached zero, so nothing else
/// refers to it. Every box it reaches was allocated with a type index that
/// `types` describes, and its fields hold what the descriptor says.
pub unsafe fn release_box(heap: &mut Heap, types: &Types, ptr: *mut u8) {
    let link = |ptr: *mut u8| ptr.cast::<*mut u8>();
    // SAFETY: as the caller promises. A box on the list is dead, so its
    // count word is free to hold the link to the next.
    unsafe {
        link(ptr).write(null_mut());
        let mut pending = ptr;
        while !pending.is_null() {
            let ptr = pending;
            pending = link(ptr).read();
            let index = ptr.offset(TYPE_INDEX_OFFSET as isize).cast::<u64>().read() as u32;
            let Some(descriptor) = types.get(index) else {
                die(&format!(
                    "freed a box of type {index}, which has no descriptor"
                ));
            };
            for field in &descriptor.counted {
                let child = match field {
                    CountedField::Box(offset) => ptr.add(*offset as usize).cast::<*mut u8>().read(),
                    CountedField::Union { offset, boxed } => {
                        let at = ptr.add(*offset as usize).cast::<u64>();
                        if boxed.binary_search(&(at.read() as u32)).is_err() {
                            continue;
                        }
                        at.add(1).cast::<*mut u8>().read()
                    }
                };
                if release(child) {
                    link(child).write(pending);
                    pending = child;
                }
            }
            heap.free(ptr);
        }
    }
}

/// `rt_release(ctx, ptr)`: see `crag_abi::RuntimeFn::Release`.
///
/// Switches to the system stack, keeping the fiber's stack pointer in a
/// callee-saved register, and frees there.
///
/// # Safety
///
/// Only generated code may call this, on a fiber stack, with the fiber's
/// task context, for a box whose count it has just taken to zero.
#[unsafe(naked)]
pub(crate) unsafe extern "C" fn rt_release(ctx: *const TaskContext, ptr: *mut u8) {
    std::arch::naked_asm!(
        "push rbx",
        "mov rbx, rsp",
        "mov rax, [rdi + {worker}]",
        "mov rsp, [rax]",
        "and rsp, -16",
        "call {entry}",
        "mov rsp, rbx",
        "pop rbx",
        "ret",
        worker = const offset_of!(TaskContext, worker),
        entry = sym release_entry,
    )
}

/// The Rust half of `rt_release`, on the system stack.
///
/// # Safety
///
/// Called only by `rt_release`, while a worker runs the fiber of `ctx`.
unsafe extern "C" fn release_entry(ctx: *const TaskContext, ptr: *mut u8) {
    // SAFETY: `Worker::resume` stored the worker in the context, and nothing
    // else uses its heap while the fiber runs.
    unsafe {
        let worker: *mut Worker = (*ctx).worker.load(Ordering::Relaxed);
        let (heap, types) = Worker::heap_and_types(worker);
        release_box(heap, types, ptr);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::heap::alloc_box;

    const NODE: u32 = 7;
    const PAIR: u32 = 9;

    fn types() -> Types {
        Types::new([
            (
                NODE,
                TypeDescriptor {
                    counted: vec![CountedField::Box(16)],
                },
            ),
            (
                PAIR,
                TypeDescriptor {
                    counted: vec![CountedField::Union {
                        offset: 16,
                        boxed: vec![NODE],
                    }],
                },
            ),
        ])
    }

    /// A node holding `next`, or a static box when `next` is null.
    fn node(heap: &mut Heap, next: *mut u8) -> *mut u8 {
        let ptr = alloc_box(heap, 24, NODE.into());
        // SAFETY: the box has a field.
        unsafe { ptr.add(16).cast::<*mut u8>().write(next) };
        ptr
    }

    #[test]
    fn a_long_chain_is_freed_without_recursion() {
        let mut heap = Heap::new();
        let types = types();
        let mut end = [STATIC_COUNT, u64::from(NODE), 0];
        let mut head = end.as_mut_ptr().cast::<u8>();
        for _ in 0..1_000_000 {
            head = node(&mut heap, head);
        }
        assert!(heap.pages_in_use() > 100);
        // SAFETY: the head's only reference is ours.
        unsafe {
            assert!(release(head));
            release_box(&mut heap, &types, head);
        }
        assert_eq!(heap.pages_in_use(), 1);
        assert_eq!(heap.segments(), 1);
        assert_eq!(end[0], STATIC_COUNT);
    }

    #[test]
    fn shared_fields_stay_until_their_last_reference() {
        let mut heap = Heap::new();
        let types = types();
        let mut end = [STATIC_COUNT, u64::from(NODE), 0];
        let shared = node(&mut heap, end.as_mut_ptr().cast());
        let a = node(&mut heap, shared);
        let b = alloc_box(&mut heap, 32, PAIR.into());
        // A union holding something other than a box.
        let c = alloc_box(&mut heap, 32, PAIR.into());
        // SAFETY: the boxes are live while they are counted.
        unsafe {
            count(shared).store(2, Ordering::Relaxed);
            b.add(16).cast::<u64>().write(NODE.into());
            b.add(24).cast::<*mut u8>().write(shared);
            c.add(16).cast::<u64>().write(1);
            c.add(24).cast::<u64>().write(12345);
            assert!(release(a));
            release_box(&mut heap, &types, a);
            assert_eq!(count(shared).load(Ordering::Relaxed), 1);
            assert!(release(b));
            release_box(&mut heap, &types, b);
            assert!(release(c));
            release_box(&mut heap, &types, c);
        }
        // Each box went back to its page's free list, the last freed first.
        assert_eq!([heap.alloc(24), heap.alloc(24)], [shared, a]);
        assert_eq!([heap.alloc(32), heap.alloc(32)], [c, b]);
    }
}
