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

//! Persistent maps and sets as hash array mapped tries (Plan §11.4.13), in
//! the compressed form of Steindorfer and Vinju, "Optimizing Hash-Array
//! Mapped Tries for Fast and Lean Immutable JVM Collections" (CHAMP).
//!
//! A map is a box holding its length and its root node. A node of the trie
//! is a box with two bitmaps over the 32 values of five bits of the hash:
//! one marks the entries the node holds inline, the other its children.
//! Entries come first, then children, each in the order of their bits. A
//! child always holds at least two entries, so a map has one shape for its
//! entries whatever the order they came in. Below the depth where the hash
//! runs out, collision nodes hold entries with equal hashes in a list.
//!
//! Keys are equal when their words are (see `crag_abi::TypeDescriptor`).
//! Like a list, a map taken by value is updated in place where only its
//! reference reaches, and a set is a map whose values have no words.

use crag_abi::{ElementLayout, LEN_OFFSET, MAP_SIZE, TypeDescriptor};

use crate::die;
use crate::fiber::TaskContext;
use crate::heap::{Heap, alloc_box};
use crate::rc::{
    Types, boxes_in, drop_box, header, is_unique, release_value, retain, retain_value,
};
use crate::system::worker_of;

const BITS: u32 = 5;

/// Offset of the root node in the map's box.
const ROOT: usize = 24;

/// The kinds of nodes.
pub(crate) const BITMAP: u32 = 1;
pub(crate) const COLLISION: u32 = 2;

/// Offsets in a node: the bitmaps, the entry bitmap in the lower half, or
/// a collision node's number of entries; then the entries and children.
const MAPS: usize = 16;
const ENTRIES: usize = 24;

/// The word at `offset` in a box.
///
/// # Safety
///
/// The box at `ptr` has a word there.
unsafe fn at(ptr: *mut u8, offset: usize) -> *mut u64 {
    // SAFETY: as the caller promises.
    unsafe { ptr.add(offset).cast() }
}

/// The hash of a key's words.
fn hash(key: &[u64]) -> u64 {
    #[cfg(test)]
    if tests::WEAK_HASH.get() {
        // Few bits, so that keys collide all the way down.
        return key.first().map_or(0, |w| w % 3) << 62;
    }
    // The finalizer of SplitMix64 over each word in turn.
    let mut h = 0x9e37_79b9_7f4a_7c15u64;
    for &w in key {
        h = (h ^ w).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        h = (h ^ (h >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        h ^= h >> 31;
    }
    h
}

/// The bit of a hash at a depth's shift.
fn bit(hash: u64, shift: u32) -> u32 {
    1 << ((hash >> shift) & 31)
}

/// The entries or children before `bit` in a bitmap.
fn rank(map: u32, bit: u32) -> usize {
    (map & (bit - 1)).count_ones() as usize
}

/// What a node holds, taken out of it to build another.
struct Contents {
    entries: u32,
    children: u32,
    /// The entries' words.
    words: Vec<u64>,
    nodes: Vec<*mut u8>,
}

/// A map's type and its layouts, with the heap to allocate from.
struct Maps<'a> {
    heap: &'a mut Heap,
    types: &'a Types,
    key: &'a ElementLayout,
    value: &'a ElementLayout,
    /// Words of a key, and of an entry.
    kw: usize,
    ew: usize,
    index: u64,
}

impl<'a> Maps<'a> {
    /// # Safety
    ///
    /// `map` points at a live map whose type `types` describes.
    unsafe fn new(heap: &'a mut Heap, types: &'a Types, map: *mut u8) -> Maps<'a> {
        // SAFETY: as the caller promises.
        let (key, value, index) = unsafe { layouts(types, map) };
        Maps {
            heap,
            types,
            key,
            value,
            kw: key.words as usize,
            ew: (key.words + value.words) as usize,
            index,
        }
    }

    // The safety contract of every method below: the nodes passed are live
    // nodes of this map's type, the keys and values of its layouts.

    unsafe fn entry(&self, node: *mut u8, i: usize) -> *mut u64 {
        // SAFETY: see above.
        unsafe { at(node, ENTRIES + 8 * self.ew * i) }
    }

    /// The slot of child `j` of a bitmap node.
    unsafe fn slot(&self, node: *mut u8, j: usize) -> *mut *mut u8 {
        // SAFETY: see above.
        unsafe {
            let (entries, _) = bitmaps(node);
            at(
                node,
                ENTRIES + 8 * (self.ew * entries.count_ones() as usize + j),
            )
            .cast()
        }
    }

    unsafe fn retain_entry(&self, entry: *mut u64) {
        // SAFETY: see above.
        unsafe {
            retain_value(entry.cast(), self.key);
            retain_value(entry.add(self.kw).cast(), self.value);
        }
    }

    unsafe fn release_entry(&mut self, entry: *mut u64) {
        // SAFETY: see above.
        unsafe {
            release_value(self.heap, self.types, entry.cast(), self.key);
            release_value(self.heap, self.types, entry.add(self.kw).cast(), self.value);
        }
    }

    unsafe fn same_key(&self, entry: *mut u64, key: &[u64]) -> bool {
        // SAFETY: see above.
        unsafe { std::slice::from_raw_parts(entry, self.kw) == &key[..self.kw] }
    }

    /// The number of entries and children of a node; a collision node has
    /// no children.
    unsafe fn counts(&self, node: *mut u8) -> (usize, usize) {
        // SAFETY: see above.
        unsafe {
            if kind(node) == COLLISION {
                return (at(node, MAPS).read() as usize, 0);
            }
            let (entries, children) = bitmaps(node);
            (
                entries.count_ones() as usize,
                children.count_ones() as usize,
            )
        }
    }

    /// The node's contents, with the caller's reference to it: moved out of
    /// it if the reference is its only one, which frees it, else copied
    /// with references of their own.
    unsafe fn take(&mut self, node: *mut u8) -> Contents {
        // SAFETY: see above.
        unsafe {
            let (n, c) = self.counts(node);
            let (entries, children) = match kind(node) {
                COLLISION => (0, 0),
                _ => bitmaps(node),
            };
            let words = std::slice::from_raw_parts(self.entry(node, 0), n * self.ew).to_vec();
            let nodes: Vec<*mut u8> = (0..c).map(|j| self.slot(node, j).read()).collect();
            if is_unique(node) {
                self.heap.free(node);
            } else {
                for i in 0..n {
                    self.retain_entry(self.entry(node, i));
                }
                nodes.iter().for_each(|&child| retain(child));
                drop_box(self.heap, self.types, node);
            }
            Contents {
                entries,
                children,
                words,
                nodes,
            }
        }
    }

    /// A bitmap node of the contents, whose references it takes.
    fn bitmap(&mut self, c: &Contents) -> *mut u8 {
        let size = ENTRIES + 8 * (c.words.len() + c.nodes.len());
        let node = alloc_box(self.heap, size, self.index | u64::from(BITMAP) << 32);
        // SAFETY: the node has room for the contents.
        unsafe {
            at(node, MAPS).write(u64::from(c.entries) | u64::from(c.children) << 32);
            let words = at(node, ENTRIES);
            words.copy_from_nonoverlapping(c.words.as_ptr(), c.words.len());
            let nodes = words.add(c.words.len()).cast::<*mut u8>();
            nodes.copy_from_nonoverlapping(c.nodes.as_ptr(), c.nodes.len());
        }
        node
    }

    /// A collision node of these entries' words, whose references it takes.
    fn collision(&mut self, words: &[u64]) -> *mut u8 {
        let node = alloc_box(
            self.heap,
            ENTRIES + 8 * words.len(),
            self.index | u64::from(COLLISION) << 32,
        );
        // SAFETY: the node has room for the entries.
        unsafe {
            at(node, MAPS).write((words.len() / self.ew) as u64);
            at(node, ENTRIES).copy_from_nonoverlapping(words.as_ptr(), words.len());
        }
        node
    }

    /// The node itself if the caller's reference is its only one, else a
    /// copy of the same shape with references to what it holds.
    unsafe fn unique(&mut self, node: *mut u8) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if is_unique(node) {
                return node;
            }
            let kind = kind(node);
            let c = self.take(node);
            match kind {
                COLLISION => self.collision(&c.words),
                _ => self.bitmap(&c),
            }
        }
    }

    /// A node holding two entries whose hashes agree below `shift`.
    fn pair(&mut self, shift: u32, a: &[u64], b: &[u64]) -> *mut u8 {
        if shift >= 64 {
            return self.collision(&[a, b].concat());
        }
        let (ha, hb) = (hash(&a[..self.kw]), hash(&b[..self.kw]));
        let (ba, bb) = (bit(ha, shift), bit(hb, shift));
        let c = if ba == bb {
            Contents {
                entries: 0,
                children: ba,
                words: Vec::new(),
                nodes: vec![self.pair(shift + BITS, a, b)],
            }
        } else {
            let words = if ba < bb { [a, b] } else { [b, a] }.concat();
            Contents {
                entries: ba | bb,
                children: 0,
                words,
                nodes: Vec::new(),
            }
        };
        self.bitmap(&c)
    }

    /// Binds the key in a subtree, whose reference the caller gives; the
    /// new subtree, and whether the key is new to it. The entry is the key's
    /// words and then the value's, and the subtree takes their references.
    unsafe fn insert_node(
        &mut self,
        node: *mut u8,
        h: u64,
        shift: u32,
        entry: &[u64],
    ) -> (*mut u8, bool) {
        let key = &entry[..self.kw];
        // SAFETY: see above.
        unsafe {
            if kind(node) == COLLISION {
                let n = at(node, MAPS).read() as usize;
                if let Some(i) = (0..n).find(|&i| self.same_key(self.entry(node, i), key)) {
                    return (self.replace(node, i, entry), false);
                }
                let mut c = self.take(node);
                c.words.extend_from_slice(entry);
                return (self.collision(&c.words), true);
            }
            let (entries, children) = bitmaps(node);
            let b = bit(h, shift);
            if entries & b != 0 {
                let i = rank(entries, b);
                if self.same_key(self.entry(node, i), key) {
                    return (self.replace(node, i, entry), false);
                }
                // Two keys share the bits: both go down into a new child.
                let mut c = self.take(node);
                let old: Vec<u64> = c.words.drain(i * self.ew..(i + 1) * self.ew).collect();
                c.entries ^= b;
                c.children |= b;
                let child = self.pair(shift + BITS, &old, entry);
                c.nodes.insert(rank(c.children, b), child);
                return (self.bitmap(&c), true);
            }
            if children & b != 0 {
                let node = self.unique(node);
                let slot = self.slot(node, rank(children, b));
                let (child, added) = self.insert_node(slot.read(), h, shift + BITS, entry);
                slot.write(child);
                return (node, added);
            }
            let mut c = self.take(node);
            let i = rank(entries, b) * self.ew;
            c.words.splice(i..i, entry.iter().copied());
            c.entries |= b;
            (self.bitmap(&c), true)
        }
    }

    /// Gives entry `i` of a node the entry's value; the key keeps the one it
    /// has, and the entry's own key is released.
    unsafe fn replace(&mut self, node: *mut u8, i: usize, entry: &[u64]) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            let node = self.unique(node);
            let at = self.entry(node, i).add(self.kw);
            release_value(self.heap, self.types, at.cast(), self.value);
            at.copy_from_nonoverlapping(entry[self.kw..].as_ptr(), self.ew - self.kw);
            let mut key = entry[..self.kw].to_vec();
            release_value(self.heap, self.types, key.as_mut_ptr().cast(), self.key);
            node
        }
    }

    /// Removes the key, which the subtree holds, from it; the new subtree,
    /// or null for an empty one.
    unsafe fn remove_node(&mut self, node: *mut u8, h: u64, shift: u32, key: &[u64]) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if kind(node) == COLLISION {
                let n = at(node, MAPS).read() as usize;
                let i = (0..n)
                    .find(|&i| self.same_key(self.entry(node, i), key))
                    .unwrap();
                let mut c = self.take(node);
                self.release_entry(c.words[i * self.ew..].as_mut_ptr());
                c.words.drain(i * self.ew..(i + 1) * self.ew);
                return self.collision(&c.words);
            }
            let (entries, children) = bitmaps(node);
            let b = bit(h, shift);
            if entries & b != 0 {
                let mut c = self.take(node);
                let i = rank(entries, b) * self.ew;
                self.release_entry(c.words[i..].as_mut_ptr());
                c.words.drain(i..i + self.ew);
                c.entries ^= b;
                if c.entries == 0 && c.children == 0 {
                    return std::ptr::null_mut();
                }
                return self.bitmap(&c);
            }
            let node = self.unique(node);
            let j = rank(children, b);
            let slot = self.slot(node, j);
            let child = self.remove_node(slot.read(), h, shift + BITS, key);
            slot.write(child);
            // A child left with one entry moves up into this node, so every
            // child keeps at least two.
            if self.counts(child) == (1, 0) {
                let moved = self.take(child);
                let mut c = self.take(node);
                c.nodes.remove(j);
                c.children ^= b;
                let i = rank(c.entries, b) * self.ew;
                c.words.splice(i..i, moved.words);
                c.entries |= b;
                return self.bitmap(&c);
            }
            node
        }
    }
}

/// The key and value layouts of a map's type, and its type index.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes.
unsafe fn layouts(types: &Types, map: *mut u8) -> (&ElementLayout, &ElementLayout, u64) {
    // SAFETY: as the caller promises.
    unsafe {
        match types.of(map) {
            TypeDescriptor::Map { key, value } => (key, value, header(map) & 0xffff_ffff),
            _ => die("a map whose type is not a map type"),
        }
    }
}

/// # Safety
///
/// `node` points at a live node.
unsafe fn kind(node: *mut u8) -> u32 {
    // SAFETY: as the caller promises.
    unsafe { (header(node) >> 32) as u32 }
}

/// The entry and child bitmaps of a bitmap node.
///
/// # Safety
///
/// `node` points at a live bitmap node.
unsafe fn bitmaps(node: *mut u8) -> (u32, u32) {
    // SAFETY: as the caller promises.
    let maps = unsafe { at(node, MAPS).read() };
    (maps as u32, (maps >> 32) as u32)
}

/// # Safety
///
/// `map` points at a live map.
unsafe fn root(map: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe { at(map, ROOT).cast::<*mut u8>().read() }
}

/// # Safety
///
/// `map` points at a live map whose box only the caller's reference holds.
unsafe fn set_root(map: *mut u8, node: *mut u8, len: usize) {
    // SAFETY: as the caller promises.
    unsafe {
        at(map, ROOT).cast::<*mut u8>().write(node);
        at(map, LEN_OFFSET as usize).write(len as u64);
    }
}

/// A new empty map of the type with this index, as generated code
/// allocates it.
pub fn empty(heap: &mut Heap, index: u32) -> *mut u8 {
    let map = alloc_box(heap, MAP_SIZE as usize, index.into());
    // SAFETY: the box has the words.
    unsafe { set_root(map, std::ptr::null_mut(), 0) };
    map
}

/// The number of entries of a map.
///
/// # Safety
///
/// `map` points at a live map.
pub unsafe fn length(map: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { at(map, LEN_OFFSET as usize).read() as usize }
}

/// The address of the words of the key's value, or null when the map has
/// none; valid while the map is. The key's words are its first.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes, and `key`
/// holds a key of its type.
pub unsafe fn get(types: &Types, map: *mut u8, key: &[u64]) -> *mut u64 {
    // SAFETY: as the caller promises.
    unsafe {
        let (k, value, _) = layouts(types, map);
        let (kw, ew) = (k.words as usize, (k.words + value.words) as usize);
        let key = &key[..kw];
        let found = |entry: *mut u64| std::slice::from_raw_parts(entry, kw) == key;
        let entry = |node: *mut u8, i: usize| at(node, ENTRIES + 8 * ew * i);
        let h = hash(key);
        let mut node = root(map);
        let mut shift = 0;
        while !node.is_null() {
            if kind(node) == COLLISION {
                let n = at(node, MAPS).read() as usize;
                return match (0..n).map(|i| entry(node, i)).find(|&e| found(e)) {
                    Some(e) => e.add(kw),
                    None => std::ptr::null_mut(),
                };
            }
            let (entries, children) = bitmaps(node);
            let b = bit(h, shift);
            if entries & b != 0 {
                let e = entry(node, rank(entries, b));
                return if found(e) {
                    e.add(kw)
                } else {
                    std::ptr::null_mut()
                };
            }
            if children & b == 0 {
                break;
            }
            let j = entries.count_ones() as usize * ew + rank(children, b);
            node = at(node, ENTRIES + 8 * j).cast::<*mut u8>().read();
            shift += BITS;
        }
        std::ptr::null_mut()
    }
}

/// The map with the key bound to the value, each given by its first words.
/// It takes the references of the map, the key and the value. A key the map
/// has keeps its words, and the one given is released.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes, owned by the
/// caller, and `key` and `value` hold a key and a value of its type.
pub unsafe fn insert(
    heap: &mut Heap,
    types: &Types,
    map: *mut u8,
    key: &[u64],
    value: &[u64],
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let mut m = Maps::new(heap, types, map);
        let entry = [&key[..m.kw], &value[..m.ew - m.kw]].concat();
        let entry = &entry[..];
        let map = unique_map(&mut m, map);
        let node = root(map);
        let len = length(map);
        if node.is_null() {
            let c = Contents {
                entries: bit(hash(&entry[..m.kw]), 0),
                children: 0,
                words: entry.to_vec(),
                nodes: Vec::new(),
            };
            set_root(map, m.bitmap(&c), 1);
        } else {
            let (node, added) = m.insert_node(node, hash(&entry[..m.kw]), 0, entry);
            set_root(map, node, len + usize::from(added));
        }
        map
    }
}

/// The map without the key. It takes the map's reference.
///
/// # Safety
///
/// As for [`insert`], with a key for the entry.
pub unsafe fn remove(heap: &mut Heap, types: &Types, map: *mut u8, key: &[u64]) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        if get(types, map, key).is_null() {
            return map;
        }
        let mut m = Maps::new(heap, types, map);
        let key = &key[..m.kw];
        let map = unique_map(&mut m, map);
        let node = m.remove_node(root(map), hash(key), 0, key);
        set_root(map, node, length(map) - 1);
        map
    }
}

/// The map's box itself if the caller's reference is its only one, else a
/// copy holding a reference to the root node.
///
/// # Safety
///
/// `map` points at a live map of the type of `m`, owned by the caller.
unsafe fn unique_map(m: &mut Maps, map: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        if is_unique(map) {
            return map;
        }
        let copy = empty(m.heap, m.index as u32);
        let node = root(map);
        if !node.is_null() {
            retain(node);
        }
        set_root(copy, node, length(map));
        drop_box(m.heap, m.types, map);
        copy
    }
}

/// The entries of a map, each the address of its key's words, which its
/// value's follow. Valid while the map is.
pub struct MapIter {
    ew: usize,
    /// The nodes left to visit, each with the next of its entries.
    stack: Vec<(*mut u8, usize)>,
}

/// Iterates a map's entries in an unspecified order.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes, which stays
/// live while the iterator is used.
pub unsafe fn iter(types: &Types, map: *mut u8) -> MapIter {
    // SAFETY: as the caller promises.
    unsafe {
        let (key, value, _) = layouts(types, map);
        let node = root(map);
        MapIter {
            ew: (key.words + value.words) as usize,
            stack: if node.is_null() {
                Vec::new()
            } else {
                vec![(node, 0)]
            },
        }
    }
}

impl Iterator for MapIter {
    type Item = *const u64;

    fn next(&mut self) -> Option<*const u64> {
        // SAFETY: the map, and so every node on the stack, is live.
        unsafe {
            while let Some(&mut (node, ref mut i)) = self.stack.last_mut() {
                let (entries, children) = match kind(node) {
                    COLLISION => (at(node, MAPS).read() as usize, 0),
                    _ => {
                        let (e, c) = bitmaps(node);
                        (e.count_ones() as usize, c.count_ones() as usize)
                    }
                };
                let k = *i;
                *i += 1;
                if k < entries {
                    return Some(at(node, ENTRIES + 8 * self.ew * k));
                }
                self.stack.pop();
                // Children follow the entries, pushed so the first comes
                // out first.
                for j in (0..children).rev() {
                    let slot = at(node, ENTRIES + 8 * (self.ew * entries + j));
                    self.stack.push((slot.cast::<*mut u8>().read(), 0));
                }
            }
            None
        }
    }
}

/// Calls `f` with each box a map's box or node holds: the root, the
/// children, or what the entries hold.
///
/// # Safety
///
/// `ptr` points at a live map or node of a map type with these layouts,
/// and `kind` is its kind.
pub(crate) unsafe fn boxes_of(
    ptr: *mut u8,
    kind: u32,
    key: &ElementLayout,
    value: &ElementLayout,
    f: &mut impl FnMut(*mut u8),
) {
    let (kw, ew) = (key.words as usize, (key.words + value.words) as usize);
    // SAFETY: as the caller promises.
    unsafe {
        let (entries, children) = match kind {
            BITMAP => {
                let (e, c) = bitmaps(ptr);
                (e.count_ones() as usize, c.count_ones() as usize)
            }
            COLLISION => (at(ptr, MAPS).read() as usize, 0),
            _ => {
                let node = root(ptr);
                if !node.is_null() {
                    f(node);
                }
                return;
            }
        };
        for i in 0..entries {
            let entry = ptr.add(ENTRIES + 8 * ew * i);
            boxes_in(entry, &key.counted, &mut *f);
            boxes_in(entry.add(8 * kw), &value.counted, &mut *f);
        }
        for j in 0..children {
            f(at(ptr, ENTRIES + 8 * (ew * entries + j))
                .cast::<*mut u8>()
                .read());
        }
    }
}

system_stack_fn! {
    /// `rt_map_insert(ctx, map, k0, k1, v0, v1)`: see
    /// `crag_abi::RuntimeFn::MapInsert`.
    fn rt_map_insert(
        ctx: *const TaskContext,
        map: *mut u8,
        k0: u64,
        k1: u64,
        v0: u64,
        v1: u64
    ) -> *mut u8 => insert_entry
}

system_stack_fn! {
    /// `rt_map_get(ctx, map, k0, k1)`: see `crag_abi::RuntimeFn::MapGet`.
    fn rt_map_get(ctx: *const TaskContext, map: *mut u8, k0: u64, k1: u64) -> *mut u64
        => get_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with what generated code passed them.
unsafe extern "C" fn insert_entry(
    ctx: *const TaskContext,
    map: *mut u8,
    k0: u64,
    k1: u64,
    v0: u64,
    v1: u64,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        insert(heap, types, map, &[k0, k1], &[v0, v1])
    }
}

/// See `insert_entry`.
///
/// # Safety
///
/// See `insert_entry`.
unsafe extern "C" fn get_entry(
    ctx: *const TaskContext,
    map: *mut u8,
    k0: u64,
    k1: u64,
) -> *mut u64 {
    // SAFETY: as the caller promises.
    unsafe {
        let (_, types) = worker_of(ctx);
        get(types, map, &[k0, k1])
    }
}

#[cfg(test)]
mod tests {
    use std::cell::Cell;
    use std::collections::HashMap;

    use super::*;
    use crag_abi::CountedField;

    use crate::testing::{REC, Rng, boxed, unboxed};

    thread_local! {
        /// Whether keys hash to three values only, in this test's thread.
        pub(super) static WEAK_HASH: Cell<bool> = const { Cell::new(false) };
    }

    const INTS: u32 = 30;
    const BOXES: u32 = 31;
    const SET: u32 = 32;

    fn types() -> Types {
        let word = |counted| ElementLayout { words: 1, counted };
        Types::new([
            (REC, TypeDescriptor::Record { counted: vec![] }),
            (
                INTS,
                TypeDescriptor::Map {
                    key: word(vec![]),
                    value: word(vec![]),
                },
            ),
            (
                BOXES,
                TypeDescriptor::Map {
                    key: word(vec![]),
                    value: word(vec![CountedField::Box(0)]),
                },
            ),
            (
                SET,
                TypeDescriptor::Map {
                    key: word(vec![]),
                    value: ElementLayout::default(),
                },
            ),
        ])
    }

    /// The value of a map of type `index` standing for `v`.
    fn value(heap: &mut Heap, index: u32, v: u64) -> Vec<u64> {
        match index {
            INTS => vec![v],
            BOXES => vec![boxed(heap, v) as u64],
            _ => vec![],
        }
    }

    /// What the value at `ptr` stands for.
    unsafe fn read(index: u32, ptr: *mut u64) -> u64 {
        // SAFETY: as the caller promises.
        unsafe {
            match index {
                INTS => ptr.read(),
                BOXES => unboxed(ptr.read() as *mut u8),
                _ => 0,
            }
        }
    }

    /// Checks the shape of a subtree: every child holds two entries or
    /// more, and every entry sits where its hash says; its entries.
    unsafe fn check_node(m: &Maps, node: *mut u8, shift: u32, top: bool) -> usize {
        // SAFETY: the trie is live.
        unsafe {
            let (n, c) = m.counts(node);
            let mut total = n;
            if kind(node) == COLLISION {
                assert!(shift >= 64);
                let h = hash(std::slice::from_raw_parts(m.entry(node, 0), m.kw));
                for i in 0..n {
                    let key = std::slice::from_raw_parts(m.entry(node, i), m.kw);
                    assert_eq!(hash(key), h);
                }
            } else {
                let (entries, children) = bitmaps(node);
                assert_eq!(entries & children, 0);
                let mut bits = (0..32).filter(|b| entries & 1 << b != 0);
                for i in 0..n {
                    let key = std::slice::from_raw_parts(m.entry(node, i), m.kw);
                    assert_eq!(bit(hash(key), shift), 1 << bits.next().unwrap());
                }
                for j in 0..c {
                    total += check_node(m, m.slot(node, j).read(), shift + BITS, false);
                }
            }
            assert!(top || total >= 2, "a child with one entry");
            total
        }
    }

    unsafe fn check(heap: &mut Heap, types: &Types, map: *mut u8, model: &HashMap<u64, u64>) {
        // SAFETY: the map is live.
        unsafe {
            assert_eq!(length(map), model.len());
            let index = header(map) as u32;
            let m = Maps::new(heap, types, map);
            let node = root(map);
            if model.is_empty() {
                assert!(node.is_null());
                return;
            }
            assert_eq!(check_node(&m, node, 0, true), model.len());
            for (k, v) in model {
                let at = get(types, map, &[*k]);
                assert!(!at.is_null(), "key {k}");
                assert_eq!(read(index, at), *v);
            }
            let mut seen: Vec<u64> = iter(types, map).map(|e| e.read()).collect();
            seen.sort_unstable();
            let mut keys: Vec<u64> = model.keys().copied().collect();
            keys.sort_unstable();
            assert_eq!(seen, keys);
        }
    }

    /// Random inserts, removals and lookups over versions that share
    /// structure, against hash maps.
    fn random_operations(index: u32, seed: u64, steps: usize, keys: u64) {
        let mut heap = Heap::new();
        let types = types();
        let mut rng = Rng(seed);
        let mut pool = vec![(empty(&mut heap, index), HashMap::new())];
        let mut next = 0;
        // SAFETY: every map in the pool is live and owned by it.
        unsafe {
            for step in 0..steps {
                let k = rng.below(pool.len());
                let (map, model) = pool[k].clone();
                if rng.below(3) == 0 {
                    retain(map);
                    pool.push((map, model.clone()));
                }
                let mut model = model;
                let key = rng.next() % keys;
                let map = match rng.below(8) {
                    0..=4 => {
                        next += 1;
                        let value = value(&mut heap, index, next);
                        model.insert(key, if index == SET { 0 } else { next });
                        insert(&mut heap, &types, map, &[key], &value)
                    }
                    5 | 6 => {
                        model.remove(&key);
                        remove(&mut heap, &types, map, &[key])
                    }
                    _ => {
                        assert_eq!(
                            get(&types, map, &[key]).is_null(),
                            !model.contains_key(&key)
                        );
                        map
                    }
                };
                pool[k] = (map, model);
                if pool.len() > 12 {
                    let (map, _) = pool.swap_remove(rng.below(pool.len()));
                    drop_box(&mut heap, &types, map);
                }
                if step % 16 == 0 {
                    for (map, model) in &pool {
                        check(&mut heap, &types, *map, model);
                    }
                }
            }
            for (map, model) in pool {
                check(&mut heap, &types, map, &model);
                drop_box(&mut heap, &types, map);
            }
        }
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn maps_of_words_behave_like_hash_maps() {
        random_operations(INTS, 1, 4000, 3000);
    }

    #[test]
    fn maps_of_boxes_count_their_values() {
        random_operations(BOXES, 2, 3000, 500);
    }

    #[test]
    fn sets_are_maps_without_values() {
        random_operations(SET, 3, 2000, 200);
    }

    #[test]
    fn keys_with_equal_hashes_share_a_collision_node() {
        WEAK_HASH.set(true);
        random_operations(BOXES, 4, 2000, 40);
        WEAK_HASH.set(false);
    }

    #[test]
    fn the_shape_does_not_depend_on_the_order_of_insertion() {
        let mut heap = Heap::new();
        let types = types();
        let mut rng = Rng(5);
        let keys: Vec<u64> = (0..2000).map(|_| rng.next()).collect();
        // SAFETY: the maps are live and owned here.
        unsafe {
            let mut a = empty(&mut heap, INTS);
            let mut b = empty(&mut heap, INTS);
            for &k in &keys {
                a = insert(&mut heap, &types, a, &[k], &[1]);
            }
            for &k in keys.iter().rev() {
                b = insert(&mut heap, &types, b, &[k], &[1]);
            }
            // Removing half the keys again leaves the shape of the other half.
            let mut c = empty(&mut heap, INTS);
            for &k in &keys[..1000] {
                c = insert(&mut heap, &types, c, &[k], &[1]);
            }
            for &k in &keys[1000..] {
                a = remove(&mut heap, &types, a, &[k]);
                b = remove(&mut heap, &types, b, &[k]);
            }
            let walk = |m| iter(&types, m).map(|e| e.read()).collect::<Vec<_>>();
            assert_eq!(walk(a), walk(c));
            assert_eq!(walk(b), walk(c));
            for m in [a, b, c] {
                drop_box(&mut heap, &types, m);
            }
        }
        assert_eq!(heap.live_blocks(), 0);
    }
}
