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

//! The functions on lists, maps and sets of the prelude (Specification
//! §19.11) that need the runtime beyond growing and reading a collection:
//! replacing an element, joining two lists, removing a key, and the keys
//! or values of a map as a list.

use crag_abi::TypeDescriptor;

use crate::fiber::TaskContext;
use crate::rc::retain_value;
use crate::system::worker_of;
use crate::{die, list, map};

system_stack_fn! {
    /// `rt_list_set(ctx, list, at, w0, w1)`: see `crag_abi::RuntimeFn::ListSet`.
    fn rt_list_set(ctx: *const TaskContext, list: *mut u8, at: u64, w0: u64, w1: u64) -> *mut u8
        => set_entry
}

system_stack_fn! {
    /// `rt_list_concat(ctx, a, b)`: see `crag_abi::RuntimeFn::ListConcat`.
    fn rt_list_concat(ctx: *const TaskContext, a: *mut u8, b: *mut u8) -> *mut u8 => concat_entry
}

system_stack_fn! {
    /// `rt_map_remove(ctx, map, k0, k1)`: see `crag_abi::RuntimeFn::MapRemove`.
    fn rt_map_remove(ctx: *const TaskContext, map: *mut u8, k0: u64, k1: u64) -> *mut u8
        => remove_entry
}

system_stack_fn! {
    /// `rt_map_list(ctx, map, list, values)`: see `crag_abi::RuntimeFn::MapList`.
    fn rt_map_list(ctx: *const TaskContext, map: *mut u8, list: *mut u8, values: u64) -> *mut u8
        => list_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with live collections whose types the
/// image describes, and the references their documentation names.
unsafe extern "C" fn set_entry(
    ctx: *const TaskContext,
    list: *mut u8,
    at: u64,
    w0: u64,
    w1: u64,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        if at as usize >= list::length(list) {
            die("a list element set outside the list");
        }
        let words = list::passed(list::element(types, list), w0, w1);
        list::set(heap, types, list, at as usize, &words)
    }
}

/// See `set_entry`.
unsafe extern "C" fn concat_entry(ctx: *const TaskContext, a: *mut u8, b: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        list::concat(heap, types, a, b)
    }
}

/// See `set_entry`.
unsafe extern "C" fn remove_entry(
    ctx: *const TaskContext,
    map: *mut u8,
    k0: u64,
    k1: u64,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        map::remove(heap, types, map, &[k0, k1])
    }
}

/// See `set_entry`.
unsafe extern "C" fn list_entry(
    ctx: *const TaskContext,
    map: *mut u8,
    mut list: *mut u8,
    values: u64,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        let (key, value) = match types.of(map) {
            TypeDescriptor::Map { key, value, .. } => (key, value),
            _ => die("keys of a box that is not a map"),
        };
        let entries: Vec<(*const u8, *const u8)> = map::iter(types, map).collect();
        for (k, v) in entries {
            let (at, layout) = match values {
                1 => (v, value),
                _ => (k, key),
            };
            retain_value(at.cast_mut(), layout);
            let mut element = [0u64; 4];
            at.copy_to_nonoverlapping(element.as_mut_ptr().cast(), layout.size as usize);
            list = list::push(heap, types, list, &element);
        }
        list
    }
}
