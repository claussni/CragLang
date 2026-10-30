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

//! Persistent maps and sets in insertion order (Plan §11.4.13, Compiler
//! Architecture §A11.4.2).
//!
//! A map is a box holding its length, the root of its hash index and its
//! entries. The entries are slots in the order their keys came in, each a
//! key's words and then its value's, in a tree of leaves of 32 slots under
//! inner nodes of 32 children. Changing the value of a key writes its slot,
//! a new key is pushed at the end, and removing a key clears its slot to a
//! hole, so no other slot moves. A leaf marks its live slots in a bitmap.
//! When holes outnumber the entries, the map is compacted.
//!
//! The index is a hash array mapped trie in the compressed form of
//! Steindorfer and Vinju, "Optimizing Hash-Array Mapped Tries for Fast and
//! Lean Immutable JVM Collections" (CHAMP), of pairs of a key's hash and
//! its slot's position. A node has two bitmaps over the 32 values of five
//! bits of the hash: one marks the pairs the node holds inline, the other
//! its children. Pairs come first, then children, each in the order of
//! their bits, and a child always holds at least two pairs. Below the depth
//! where the hash runs out, collision nodes hold pairs with equal hashes.
//!
//! Keys are equal when their words are, or, for strings and bytes, their
//! bytes (see `crag_abi::TypeDescriptor`).
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
use crate::text;

const BITS: u32 = 5;

/// Offsets in the map's box: the root of the index, the tree of entries,
/// its height, and the number of slots in it, holes among them.
const ROOT: usize = 24;
const TREE: usize = 32;
const HEIGHT: usize = 40;
const SLOTS: usize = 48;

const _: () = assert!(MAP_SIZE as usize == SLOTS + 8);

/// The kinds of nodes: of the index, and of the tree of entries.
pub(crate) const BITMAP: u32 = 1;
pub(crate) const COLLISION: u32 = 2;
pub(crate) const LEAF: u32 = 3;
pub(crate) const INNER: u32 = 4;

/// Offsets in a node. The word at `MAPS` holds an index node's bitmaps,
/// the pairs' in the lower half, or a collision node's number of pairs; a
/// leaf's bitmap of live slots in the lower half and its slots in use in
/// the upper; or an inner node's number of children. The pairs and
/// children, the slots, or the children follow at `BODY`.
const MAPS: usize = 16;
const BODY: usize = 24;

/// A key's hash and the position of its slot.
type Pair = [u64; 2];

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
    key.iter().fold(SEED, |h, &w| mix(h, w))
}

const SEED: u64 = 0x9e37_79b9_7f4a_7c15;

/// The finalizer of SplitMix64 over a hash and a word.
fn mix(h: u64, w: u64) -> u64 {
    let mut h = (h ^ w).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    h = (h ^ (h >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    h ^ (h >> 31)
}

/// The hash of a key, by its bytes when it is a string or bytes.
///
/// # Safety
///
/// `key` holds a live key, of a string or bytes when `text` is set.
unsafe fn hash_key(key: &[u64], text: bool) -> u64 {
    if !text {
        return hash(key);
    }
    // SAFETY: as the caller promises.
    let bytes = unsafe { text::bytes_of(key) };
    #[cfg(test)]
    if tests::WEAK_HASH.get() {
        return bytes.first().map_or(0, |&b| u64::from(b) % 3) << 62;
    }
    bytes
        .chunks(8)
        .fold(mix(SEED, bytes.len() as u64), |h, chunk| {
            let mut word = [0; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            mix(h, u64::from_le_bytes(word))
        })
}

/// Whether two keys are equal: their words, or for strings and bytes their
/// bytes.
///
/// # Safety
///
/// As for [`hash_key`], for both keys.
unsafe fn equal_keys(a: &[u64], b: &[u64], text: bool) -> bool {
    // SAFETY: as the caller promises.
    a == b || text && unsafe { text::bytes_of(a) == text::bytes_of(b) }
}

/// The bit of a hash at a depth's shift.
fn bit(hash: u64, shift: u32) -> u32 {
    1 << ((hash >> shift) & 31)
}

/// The pairs or children before `bit` in a bitmap.
fn rank(map: u32, bit: u32) -> usize {
    (map & (bit - 1)).count_ones() as usize
}

/// The slots a tree of entries of height `h` holds when full.
fn capacity(h: usize) -> usize {
    1 << (BITS as usize * (h + 1))
}

/// The slots or children a node of the tree of entries has room for when
/// it uses `n`: room doubles as a node fills, so small maps stay small.
fn room(n: usize) -> usize {
    n.max(1).next_power_of_two()
}

/// What an index node holds, taken out of it to build another.
struct Contents {
    pairs_map: u32,
    children: u32,
    /// The pairs' words.
    pairs: Vec<u64>,
    nodes: Vec<*mut u8>,
}

/// A map's type and its layouts, with the heap to allocate from.
struct Maps<'a> {
    heap: &'a mut Heap,
    types: &'a Types,
    key: &'a ElementLayout,
    value: &'a ElementLayout,
    /// Words of a key, and of a slot.
    kw: usize,
    ew: usize,
    index: u64,
    /// Keys are strings or bytes.
    text: bool,
}

impl<'a> Maps<'a> {
    /// # Safety
    ///
    /// `map` points at a live map whose type `types` describes.
    unsafe fn new(heap: &'a mut Heap, types: &'a Types, map: *mut u8) -> Maps<'a> {
        // SAFETY: as the caller promises.
        let (key, value, index, text) = unsafe { layouts(types, map) };
        Maps {
            heap,
            types,
            key,
            value,
            kw: key.words as usize,
            ew: (key.words + value.words) as usize,
            index,
            text,
        }
    }

    // The safety contract of every method below: the nodes passed are live
    // nodes of this map's type, the keys and values of its layouts.

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

    // The index.

    /// The index node's contents, with the caller's reference to it: moved
    /// out of it if the reference is its only one, which frees it, else
    /// copied with references of their own.
    unsafe fn take(&mut self, node: *mut u8) -> Contents {
        // SAFETY: see above.
        unsafe {
            let (n, c) = counts(node);
            let (pairs_map, children) = match kind(node) {
                COLLISION => (0, 0),
                _ => bitmaps(node),
            };
            let pairs = std::slice::from_raw_parts(at(node, BODY), 2 * n).to_vec();
            let nodes: Vec<*mut u8> = (0..c).map(|j| index_child(node, j).read()).collect();
            if is_unique(node) {
                self.heap.free(node);
            } else {
                nodes.iter().for_each(|&child| retain(child));
                drop_box(self.heap, self.types, node);
            }
            Contents {
                pairs_map,
                children,
                pairs,
                nodes,
            }
        }
    }

    /// A bitmap node of the contents, whose references it takes.
    fn bitmap(&mut self, c: &Contents) -> *mut u8 {
        let size = BODY + 8 * (c.pairs.len() + c.nodes.len());
        let node = alloc_box(self.heap, size, self.index | u64::from(BITMAP) << 32);
        // SAFETY: the node has room for the contents.
        unsafe {
            at(node, MAPS).write(u64::from(c.pairs_map) | u64::from(c.children) << 32);
            let words = at(node, BODY);
            words.copy_from_nonoverlapping(c.pairs.as_ptr(), c.pairs.len());
            let nodes = words.add(c.pairs.len()).cast::<*mut u8>();
            nodes.copy_from_nonoverlapping(c.nodes.as_ptr(), c.nodes.len());
        }
        node
    }

    /// A collision node of these pairs' words.
    fn collision(&mut self, pairs: &[u64]) -> *mut u8 {
        let node = alloc_box(
            self.heap,
            BODY + 8 * pairs.len(),
            self.index | u64::from(COLLISION) << 32,
        );
        // SAFETY: the node has room for the pairs.
        unsafe {
            at(node, MAPS).write((pairs.len() / 2) as u64);
            at(node, BODY).copy_from_nonoverlapping(pairs.as_ptr(), pairs.len());
        }
        node
    }

    /// The index node itself if the caller's reference is its only one,
    /// else a copy of the same shape with references to its children.
    unsafe fn unique_index(&mut self, node: *mut u8) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if is_unique(node) {
                return node;
            }
            let kind = kind(node);
            let c = self.take(node);
            match kind {
                COLLISION => self.collision(&c.pairs),
                _ => self.bitmap(&c),
            }
        }
    }

    /// A node holding two pairs whose hashes agree below `shift`.
    fn pair(&mut self, shift: u32, a: Pair, b: Pair) -> *mut u8 {
        if shift >= 64 {
            return self.collision(&[a, b].concat());
        }
        let (ba, bb) = (bit(a[0], shift), bit(b[0], shift));
        let c = if ba == bb {
            Contents {
                pairs_map: 0,
                children: ba,
                pairs: Vec::new(),
                nodes: vec![self.pair(shift + BITS, a, b)],
            }
        } else {
            let pairs = if ba < bb { [a, b] } else { [b, a] }.concat();
            Contents {
                pairs_map: ba | bb,
                children: 0,
                pairs,
                nodes: Vec::new(),
            }
        };
        self.bitmap(&c)
    }

    /// Adds the pair of a key the subtree lacks to it, whose reference the
    /// caller gives; the new subtree.
    unsafe fn insert_index(&mut self, node: *mut u8, shift: u32, p: Pair) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if kind(node) == COLLISION {
                let mut c = self.take(node);
                c.pairs.extend_from_slice(&p);
                return self.collision(&c.pairs);
            }
            let (pairs_map, children) = bitmaps(node);
            let b = bit(p[0], shift);
            if pairs_map & b != 0 {
                // Two pairs share the bits: both go down into a new child.
                let mut c = self.take(node);
                let i = 2 * rank(pairs_map, b);
                let old = [c.pairs[i], c.pairs[i + 1]];
                c.pairs.drain(i..i + 2);
                c.pairs_map ^= b;
                c.children |= b;
                let child = self.pair(shift + BITS, old, p);
                c.nodes.insert(rank(c.children, b), child);
                return self.bitmap(&c);
            }
            if children & b != 0 {
                let node = self.unique_index(node);
                let slot = index_child(node, rank(children, b));
                slot.write(self.insert_index(slot.read(), shift + BITS, p));
                return node;
            }
            let mut c = self.take(node);
            let i = 2 * rank(pairs_map, b);
            c.pairs.splice(i..i, p);
            c.pairs_map |= b;
            self.bitmap(&c)
        }
    }

    /// Removes the pair, which the subtree holds, from it; the new subtree,
    /// or null for an empty one.
    unsafe fn remove_index(&mut self, node: *mut u8, shift: u32, p: Pair) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if kind(node) == COLLISION {
                let mut c = self.take(node);
                let i = c.pairs.chunks(2).position(|q| q[1] == p[1]).unwrap();
                c.pairs.drain(2 * i..2 * i + 2);
                return self.collision(&c.pairs);
            }
            let (pairs_map, children) = bitmaps(node);
            let b = bit(p[0], shift);
            if pairs_map & b != 0 {
                let mut c = self.take(node);
                let i = 2 * rank(pairs_map, b);
                c.pairs.drain(i..i + 2);
                c.pairs_map ^= b;
                if c.pairs_map == 0 && c.children == 0 {
                    return std::ptr::null_mut();
                }
                return self.bitmap(&c);
            }
            let node = self.unique_index(node);
            let j = rank(children, b);
            let slot = index_child(node, j);
            let child = self.remove_index(slot.read(), shift + BITS, p);
            slot.write(child);
            // A child left with one pair moves up into this node, so every
            // child keeps at least two.
            if counts(child) == (1, 0) {
                let moved = self.take(child);
                let mut c = self.take(node);
                c.nodes.remove(j);
                c.children ^= b;
                let i = 2 * rank(c.pairs_map, b);
                c.pairs.splice(i..i, moved.pairs);
                c.pairs_map |= b;
                return self.bitmap(&c);
            }
            node
        }
    }

    // The tree of entries.

    /// A node of the tree of entries that the caller's reference alone
    /// reaches, with room for `n` slots or children: the node itself when
    /// it is so, else a copy that takes over the caller's reference.
    unsafe fn own(&mut self, node: *mut u8, n: usize) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            let kind = kind(node);
            let (count, unit) = match kind {
                LEAF => (leaf_used(node), self.ew),
                _ => (at(node, MAPS).read() as usize, 1),
            };
            let unique = is_unique(node);
            if unique && room(count) >= n {
                return node;
            }
            let size = BODY + 8 * unit * room(n.max(count));
            let copy = alloc_box(self.heap, size, self.index | u64::from(kind) << 32);
            at(copy, MAPS).write(at(node, MAPS).read());
            at(copy, BODY).copy_from_nonoverlapping(at(node, BODY), unit * count);
            if unique {
                self.heap.free(node);
                return copy;
            }
            match kind {
                LEAF => {
                    let live = leaf_live(node);
                    for i in (0..count).filter(|i| live & 1 << i != 0) {
                        self.retain_entry(at(node, BODY + 8 * self.ew * i));
                    }
                }
                _ => (0..count).for_each(|j| retain(tree_child(node, j).read())),
            }
            drop_box(self.heap, self.types, node);
            copy
        }
    }

    /// A tree of height `h` holding the entry alone, in its first slot,
    /// whose references it takes.
    fn fresh(&mut self, h: usize, entry: &[u64]) -> *mut u8 {
        let leaf = alloc_box(
            self.heap,
            BODY + 8 * self.ew,
            self.index | u64::from(LEAF) << 32,
        );
        // SAFETY: the leaf has room for the slot, and each inner node for
        // its child.
        unsafe {
            at(leaf, MAPS).write(1 | 1 << 32);
            at(leaf, BODY).copy_from_nonoverlapping(entry.as_ptr(), self.ew);
            let mut node = leaf;
            for _ in 0..h {
                let inner = alloc_box(self.heap, BODY + 8, self.index | u64::from(INNER) << 32);
                at(inner, MAPS).write(1);
                tree_child(inner, 0).write(node);
                node = inner;
            }
            node
        }
    }

    /// Pushes the entry at `pos`, the end of a subtree of height `h` whose
    /// reference the caller gives; the new subtree, which has room for it.
    unsafe fn push_node(&mut self, node: *mut u8, h: usize, pos: usize, entry: &[u64]) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if h == 0 {
                let i = leaf_used(node);
                let leaf = self.own(node, i + 1);
                at(leaf, BODY + 8 * self.ew * i).copy_from_nonoverlapping(entry.as_ptr(), self.ew);
                let live = leaf_live(leaf) | 1 << i;
                at(leaf, MAPS).write(u64::from(live) | ((i + 1) as u64) << 32);
                return leaf;
            }
            let j = (pos >> (BITS as usize * h)) & 31;
            let count = at(node, MAPS).read() as usize;
            if j < count {
                let node = self.own(node, count);
                let slot = tree_child(node, j);
                slot.write(self.push_node(slot.read(), h - 1, pos, entry));
                return node;
            }
            let child = self.fresh(h - 1, entry);
            let node = self.own(node, count + 1);
            tree_child(node, count).write(child);
            at(node, MAPS).write((count + 1) as u64);
            node
        }
    }

    /// The path to slot `pos` of a subtree of height `h`, whose reference
    /// the caller gives, made the caller's alone: the new subtree, the leaf
    /// and the slot's place in it.
    unsafe fn path(&mut self, node: *mut u8, h: usize, pos: usize) -> (*mut u8, *mut u8, usize) {
        // SAFETY: see above.
        unsafe {
            if h == 0 {
                let leaf = self.own(node, leaf_used(node));
                return (leaf, leaf, pos & 31);
            }
            let node = self.own(node, at(node, MAPS).read() as usize);
            let slot = tree_child(node, (pos >> (BITS as usize * h)) & 31);
            let (child, leaf, i) = self.path(slot.read(), h - 1, pos);
            slot.write(child);
            (node, leaf, i)
        }
    }

    /// Binds a key the map lacks: its entry goes at the end, and its pair
    /// into the index. The map is the caller's alone, and takes the
    /// entry's references.
    unsafe fn append(&mut self, map: *mut u8, h: u64, entry: &[u64]) {
        // SAFETY: see above.
        unsafe {
            let slots = map_slots(map);
            let (mut tree, mut height) = (tree(map), height(map));
            if tree.is_null() {
                tree = self.fresh(0, entry);
            } else {
                if slots == capacity(height) {
                    let root = alloc_box(self.heap, BODY + 16, self.index | u64::from(INNER) << 32);
                    at(root, MAPS).write(1);
                    tree_child(root, 0).write(tree);
                    tree = root;
                    height += 1;
                }
                tree = self.push_node(tree, height, slots, entry);
            }
            let p = [h, slots as u64];
            let root = match root(map) {
                node if node.is_null() => self.bitmap(&Contents {
                    pairs_map: bit(h, 0),
                    children: 0,
                    pairs: p.to_vec(),
                    nodes: Vec::new(),
                }),
                node => self.insert_index(node, 0, p),
            };
            at(map, ROOT).cast::<*mut u8>().write(root);
            at(map, TREE).cast::<*mut u8>().write(tree);
            at(map, HEIGHT).write(height as u64);
            at(map, SLOTS).write(slots as u64 + 1);
            at(map, LEN_OFFSET as usize).write(length(map) as u64 + 1);
        }
    }

    /// The map without holes, its entries in their order; it takes the
    /// map's reference.
    unsafe fn compact(&mut self, map: *mut u8) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            let fresh = empty(self.heap, self.index as u32);
            for entry in iter(self.types, map) {
                let entry = entry.cast_mut();
                self.retain_entry(entry);
                let entry = std::slice::from_raw_parts(entry, self.ew);
                self.append(fresh, hash_key(&entry[..self.kw], self.text), entry);
            }
            drop_box(self.heap, self.types, map);
            fresh
        }
    }
}

/// The key and value layouts of a map's type, its type index, and whether
/// its keys are text.
///
/// The layout of a map's values.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes.
pub unsafe fn value_layout(types: &Types, map: *mut u8) -> &ElementLayout {
    // SAFETY: as the caller promises.
    unsafe { layouts(types, map).1 }
}

/// # Safety
///
/// `map` points at a live map whose type `types` describes.
unsafe fn layouts(types: &Types, map: *mut u8) -> (&ElementLayout, &ElementLayout, u64, bool) {
    // SAFETY: as the caller promises.
    unsafe {
        match types.of(map) {
            TypeDescriptor::Map {
                key,
                value,
                text_keys,
            } => (key, value, header(map) & 0xffff_ffff, *text_keys),
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

/// The pair and child bitmaps of a bitmap node.
///
/// # Safety
///
/// `node` points at a live bitmap node.
unsafe fn bitmaps(node: *mut u8) -> (u32, u32) {
    // SAFETY: as the caller promises.
    let maps = unsafe { at(node, MAPS).read() };
    (maps as u32, (maps >> 32) as u32)
}

/// The number of pairs and children of an index node; a collision node has
/// no children.
///
/// # Safety
///
/// `node` points at a live index node.
unsafe fn counts(node: *mut u8) -> (usize, usize) {
    // SAFETY: as the caller promises.
    unsafe {
        if kind(node) == COLLISION {
            return (at(node, MAPS).read() as usize, 0);
        }
        let (pairs, children) = bitmaps(node);
        (pairs.count_ones() as usize, children.count_ones() as usize)
    }
}

/// The place of child `j` of a bitmap node.
///
/// # Safety
///
/// `node` points at a live bitmap node with that child.
unsafe fn index_child(node: *mut u8, j: usize) -> *mut *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (pairs, _) = bitmaps(node);
        at(node, BODY + 8 * (2 * pairs.count_ones() as usize + j)).cast()
    }
}

/// The slots in use of a leaf, and its bitmap of live ones.
///
/// # Safety
///
/// `leaf` points at a live leaf.
unsafe fn leaf_used(leaf: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { (at(leaf, MAPS).read() >> 32) as usize }
}

/// # Safety
///
/// `leaf` points at a live leaf.
unsafe fn leaf_live(leaf: *mut u8) -> u32 {
    // SAFETY: as the caller promises.
    unsafe { at(leaf, MAPS).read() as u32 }
}

/// The place of child `j` of an inner node of the tree of entries.
///
/// # Safety
///
/// `node` points at a live inner node with room for that child.
unsafe fn tree_child(node: *mut u8, j: usize) -> *mut *mut u8 {
    // SAFETY: as the caller promises.
    unsafe { at(node, BODY + 8 * j).cast() }
}

/// The leaf holding slot `pos` of a tree of height `h`.
///
/// # Safety
///
/// `tree` points at a live tree of entries with that slot.
unsafe fn leaf_of(tree: *mut u8, h: usize, pos: usize) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let mut node = tree;
        for level in (1..=h).rev() {
            node = tree_child(node, (pos >> (BITS as usize * level)) & 31).read();
        }
        node
    }
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
/// `map` points at a live map.
unsafe fn tree(map: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe { at(map, TREE).cast::<*mut u8>().read() }
}

/// # Safety
///
/// `map` points at a live map.
unsafe fn height(map: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { at(map, HEIGHT).read() as usize }
}

/// # Safety
///
/// `map` points at a live map.
unsafe fn map_slots(map: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { at(map, SLOTS).read() as usize }
}

/// The position of the key's slot and its hash, if the map has the key.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes, and `key`
/// holds a key of its type.
unsafe fn locate(types: &Types, map: *mut u8, key: &[u64]) -> (u64, Option<usize>) {
    // SAFETY: as the caller promises.
    unsafe {
        let (k, value, _, text) = layouts(types, map);
        let (kw, ew) = (k.words as usize, (k.words + value.words) as usize);
        let key = &key[..kw];
        let h = hash_key(key, text);
        let (tree, height) = (tree(map), height(map));
        let same = |pos: u64| {
            let pos = pos as usize;
            let slot = at(leaf_of(tree, height, pos), BODY + 8 * ew * (pos & 31));
            equal_keys(std::slice::from_raw_parts(slot, kw), key, text)
        };
        let mut node = root(map);
        let mut shift = 0;
        while !node.is_null() {
            if kind(node) == COLLISION {
                let n = at(node, MAPS).read() as usize;
                let pos = (0..n)
                    .map(|i| at(node, BODY + 16 * i + 8).read())
                    .find(|&p| same(p));
                return (h, pos.map(|p| p as usize));
            }
            let (pairs, children) = bitmaps(node);
            let b = bit(h, shift);
            if pairs & b != 0 {
                let i = rank(pairs, b);
                let (ph, pos) = (
                    at(node, BODY + 16 * i).read(),
                    at(node, BODY + 16 * i + 8).read(),
                );
                return (h, (ph == h && same(pos)).then_some(pos as usize));
            }
            if children & b == 0 {
                break;
            }
            node = index_child(node, rank(children, b)).read();
            shift += BITS;
        }
        (h, None)
    }
}

/// A new empty map of the type with this index, as generated code
/// allocates it.
pub fn empty(heap: &mut Heap, index: u32) -> *mut u8 {
    let map = alloc_box(heap, MAP_SIZE as usize, index.into());
    // SAFETY: the box has the words.
    unsafe {
        for offset in (LEN_OFFSET as usize..MAP_SIZE as usize).step_by(8) {
            at(map, offset).write(0);
        }
    }
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
        let Some(pos) = locate(types, map, key).1 else {
            return std::ptr::null_mut();
        };
        let (k, value, ..) = layouts(types, map);
        let ew = (k.words + value.words) as usize;
        let leaf = leaf_of(tree(map), height(map), pos);
        at(leaf, BODY + 8 * (ew * (pos & 31) + k.words as usize))
    }
}

/// The map with the key bound to the value, each given by its first words.
/// It takes the references of the map, the key and the value. A key the map
/// has keeps its words and its place, and the one given is released; a new
/// key goes last.
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
        let (h, found) = locate(types, map, key);
        let mut m = Maps::new(heap, types, map);
        let entry = [&key[..m.kw], &value[..m.ew - m.kw]].concat();
        let map = unique_map(&mut m, map);
        match found {
            Some(pos) => {
                let (tree, leaf, i) = m.path(tree(map), height(map), pos);
                at(map, TREE).cast::<*mut u8>().write(tree);
                let at = at(leaf, BODY + 8 * (m.ew * i + m.kw));
                release_value(m.heap, m.types, at.cast(), m.value);
                at.copy_from_nonoverlapping(entry[m.kw..].as_ptr(), m.ew - m.kw);
                let mut key = entry[..m.kw].to_vec();
                release_value(m.heap, m.types, key.as_mut_ptr().cast(), m.key);
            }
            None => m.append(map, h, &entry),
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
        let (h, Some(pos)) = locate(types, map, key) else {
            return map;
        };
        let mut m = Maps::new(heap, types, map);
        let map = unique_map(&mut m, map);
        let root = m.remove_index(root(map), 0, [h, pos as u64]);
        at(map, ROOT).cast::<*mut u8>().write(root);
        let (tree, leaf, i) = m.path(tree(map), height(map), pos);
        at(map, TREE).cast::<*mut u8>().write(tree);
        m.release_entry(at(leaf, BODY + 8 * m.ew * i));
        at(leaf, MAPS).write(at(leaf, MAPS).read() & !(1 << i));
        let len = length(map) - 1;
        at(map, LEN_OFFSET as usize).write(len as u64);
        if map_slots(map) - len > len {
            return m.compact(map);
        }
        map
    }
}

/// The map's box itself if the caller's reference is its only one, else a
/// copy holding references to the index and the entries.
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
        let copy = alloc_box(m.heap, MAP_SIZE as usize, m.index);
        for offset in (LEN_OFFSET as usize..MAP_SIZE as usize).step_by(8) {
            at(copy, offset).write(at(map, offset).read());
        }
        for node in [root(map), tree(map)] {
            if !node.is_null() {
                retain(node);
            }
        }
        drop_box(m.heap, m.types, map);
        copy
    }
}

/// The entries of a map, each the address of its key's words, which its
/// value's follow. Valid while the map is.
pub struct MapIter {
    ew: usize,
    tree: *mut u8,
    height: usize,
    slots: usize,
    /// The next slot, and the leaf it is in when it is not a leaf's first.
    pos: usize,
    leaf: *mut u8,
}

/// Iterates a map's entries in the order their keys came in.
///
/// # Safety
///
/// `map` points at a live map whose type `types` describes, which stays
/// live while the iterator is used.
pub unsafe fn iter(types: &Types, map: *mut u8) -> MapIter {
    // SAFETY: as the caller promises.
    unsafe {
        let (key, value, ..) = layouts(types, map);
        MapIter {
            ew: (key.words + value.words) as usize,
            tree: tree(map),
            height: height(map),
            slots: map_slots(map),
            pos: 0,
            leaf: std::ptr::null_mut(),
        }
    }
}

impl Iterator for MapIter {
    type Item = *const u64;

    fn next(&mut self) -> Option<*const u64> {
        // SAFETY: the map, and so its tree of entries, is live.
        unsafe {
            while self.pos < self.slots {
                let (pos, i) = (self.pos, self.pos & 31);
                self.pos += 1;
                if i == 0 {
                    self.leaf = leaf_of(self.tree, self.height, pos);
                }
                if leaf_live(self.leaf) & 1 << i != 0 {
                    return Some(at(self.leaf, BODY + 8 * self.ew * i));
                }
            }
            None
        }
    }
}

/// Calls `f` with each box a map's box or node holds: the index and the
/// entries, the children, or what the live slots hold.
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
        match kind {
            BITMAP => {
                let (_, children) = counts(ptr);
                (0..children).for_each(|j| f(index_child(ptr, j).read()));
            }
            COLLISION => {}
            LEAF => {
                let live = leaf_live(ptr);
                for i in (0..leaf_used(ptr)).filter(|i| live & 1 << i != 0) {
                    let entry = ptr.add(BODY + 8 * ew * i);
                    boxes_in(entry, &key.counted, &mut *f);
                    boxes_in(entry.add(8 * kw), &value.counted, &mut *f);
                }
            }
            INNER => {
                (0..at(ptr, MAPS).read() as usize).for_each(|j| f(tree_child(ptr, j).read()));
            }
            _ => {
                for node in [root(ptr), tree(ptr)] {
                    if !node.is_null() {
                        f(node);
                    }
                }
            }
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
        let value = crate::list::passed(value_layout(types, map), v0, v1);
        insert(heap, types, map, &[k0, k1], &value)
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
            (
                REC,
                TypeDescriptor::Record {
                    counted: vec![],
                    dispose: None,
                },
            ),
            (
                INTS,
                TypeDescriptor::Map {
                    key: word(vec![]),
                    value: word(vec![]),
                    text_keys: false,
                },
            ),
            (
                BOXES,
                TypeDescriptor::Map {
                    key: word(vec![]),
                    value: word(vec![CountedField::Box(0)]),
                    text_keys: false,
                },
            ),
            (
                SET,
                TypeDescriptor::Map {
                    key: word(vec![]),
                    value: ElementLayout::default(),
                    text_keys: false,
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

    /// A map as the entries in their order.
    type Model = Vec<(u64, u64)>;

    fn bind(model: &mut Model, key: u64, value: u64) {
        match model.iter_mut().find(|(k, _)| *k == key) {
            Some(entry) => entry.1 = value,
            None => model.push((key, value)),
        }
    }

    /// The key in slot `pos`, which is live.
    unsafe fn key_at(m: &Maps, map: *mut u8, pos: usize) -> Vec<u64> {
        // SAFETY: the map is live and has the slot.
        unsafe {
            let leaf = leaf_of(tree(map), height(map), pos);
            assert!(leaf_live(leaf) & 1 << (pos & 31) != 0, "a pair of a hole");
            let slot = at(leaf, BODY + 8 * m.ew * (pos & 31));
            std::slice::from_raw_parts(slot, m.kw).to_vec()
        }
    }

    /// Checks the shape of a subtree of the index: every child holds two
    /// pairs or more, every pair sits where its hash says, and its hash is
    /// its key's; its pairs.
    unsafe fn check_node(m: &Maps, map: *mut u8, node: *mut u8, shift: u32, top: bool) -> usize {
        // SAFETY: the map is live.
        unsafe {
            let (n, c) = counts(node);
            let mut total = n;
            let pair = |i: usize| {
                (
                    at(node, BODY + 16 * i).read(),
                    at(node, BODY + 16 * i + 8).read(),
                )
            };
            for i in 0..n {
                let (h, pos) = pair(i);
                assert_eq!(hash_key(&key_at(m, map, pos as usize), m.text), h);
            }
            if kind(node) == COLLISION {
                assert!(shift >= 64);
                assert!((0..n).all(|i| pair(i).0 == pair(0).0));
            } else {
                let (pairs, children) = bitmaps(node);
                assert_eq!(pairs & children, 0);
                let mut bits = (0..32).filter(|b| pairs & 1 << b != 0);
                for i in 0..n {
                    assert_eq!(bit(pair(i).0, shift), 1 << bits.next().unwrap());
                }
                for j in 0..c {
                    total += check_node(m, map, index_child(node, j).read(), shift + BITS, false);
                }
            }
            assert!(top || total >= 2, "a child with one pair");
            total
        }
    }

    unsafe fn check(heap: &mut Heap, types: &Types, map: *mut u8, model: &Model) {
        // SAFETY: the map is live.
        unsafe {
            assert_eq!(length(map), model.len());
            assert!(
                map_slots(map) - length(map) <= length(map),
                "more holes than entries"
            );
            let index = header(map) as u32;
            let m = Maps::new(heap, types, map);
            if model.is_empty() {
                assert!(root(map).is_null());
            } else {
                assert_eq!(check_node(&m, map, root(map), 0, true), model.len());
            }
            for (k, v) in model {
                let at = get(types, map, &[*k]);
                assert!(!at.is_null(), "key {k}");
                assert_eq!(read(index, at), *v);
            }
            let seen: Vec<u64> = iter(types, map).map(|e| e.read()).collect();
            let keys: Vec<u64> = model.iter().map(|(k, _)| *k).collect();
            assert_eq!(seen, keys);
        }
    }

    /// Random inserts, removals and lookups over versions that share
    /// structure, against vectors of entries.
    fn random_operations(index: u32, seed: u64, steps: usize, keys: u64) {
        let mut heap = Heap::new();
        let types = types();
        let mut rng = Rng(seed);
        let mut pool: Vec<(*mut u8, Model)> = vec![(empty(&mut heap, index), Vec::new())];
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
                        bind(&mut model, key, if index == SET { 0 } else { next });
                        insert(&mut heap, &types, map, &[key], &value)
                    }
                    5 | 6 => {
                        model.retain(|(k, _)| *k != key);
                        remove(&mut heap, &types, map, &[key])
                    }
                    _ => {
                        assert_eq!(
                            get(&types, map, &[key]).is_null(),
                            !model.iter().any(|(k, _)| *k == key)
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
    fn maps_of_words_behave_like_ordered_maps() {
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

    /// A map from strings to words, the long strings in buffers.
    fn text_keys(weak: bool) {
        const TEXTS: u32 = 33;
        WEAK_HASH.set(weak);
        let mut heap = Heap::new();
        let types = Types::new([(
            TEXTS,
            TypeDescriptor::Map {
                key: ElementLayout {
                    words: 2,
                    counted: vec![CountedField::Box(0)],
                },
                value: ElementLayout {
                    words: 1,
                    counted: vec![],
                },
                text_keys: true,
            },
        )]);
        let name = |heap: &mut Heap, n: u64| {
            let text = match n % 2 {
                0 => format!("k{n}"),
                _ => format!("a longer key, number {n}"),
            };
            text::make_text(heap, &[text.as_bytes()])
        };
        // SAFETY: the map and the keys are live, and the map owns its keys.
        unsafe {
            let mut map = empty(&mut heap, TEXTS);
            for n in 0..300 {
                let key = name(&mut heap, n);
                map = insert(&mut heap, &types, map, &key, &[n]);
            }
            // An equal key in another buffer finds the entry, and binding it
            // again keeps the map's key and releases the one given.
            for n in 0..300 {
                let key = name(&mut heap, n);
                let at = get(&types, map, &key);
                assert!(!at.is_null(), "key {n}");
                assert_eq!(at.read(), n);
                map = insert(&mut heap, &types, map, &key, &[n + 1]);
            }
            assert_eq!(length(map), 300);
            let m = Maps::new(&mut heap, &types, map);
            assert_eq!(check_node(&m, map, root(map), 0, true), 300);
            let missing = text::make_text(&mut heap, &[b"a longer key, number 301"]);
            assert!(get(&types, map, &missing).is_null());
            drop_box(&mut heap, &types, missing[0] as *mut u8);
            for n in (0..300).step_by(3) {
                let key = name(&mut heap, n);
                map = remove(&mut heap, &types, map, &key);
                if text::in_buffer(key[0]) {
                    drop_box(&mut heap, &types, key[0] as *mut u8);
                }
            }
            assert_eq!(length(map), 200);
            let values: Vec<u64> = iter(&types, map).map(|e| e.add(2).read()).collect();
            let kept: Vec<u64> = (0..300).filter(|n| n % 3 != 0).map(|n| n + 1).collect();
            assert_eq!(values, kept);
            drop_box(&mut heap, &types, map);
        }
        assert_eq!(heap.live_blocks(), 0);
        WEAK_HASH.set(false);
    }

    #[test]
    fn string_keys_are_equal_when_their_bytes_are() {
        text_keys(false);
        text_keys(true);
    }

    #[test]
    fn entries_keep_the_order_their_keys_came_in() {
        let mut heap = Heap::new();
        let types = types();
        let walk = |m| {
            unsafe { iter(&types, m) }
                .map(|e| unsafe { e.read() })
                .collect::<Vec<_>>()
        };
        // SAFETY: the maps are live and owned here.
        unsafe {
            let mut a = empty(&mut heap, INTS);
            for k in [5, 3, 9, 1] {
                a = insert(&mut heap, &types, a, &[k], &[k]);
            }
            // A new value keeps the key's place; a key removed and bound
            // again goes last.
            a = insert(&mut heap, &types, a, &[3], &[30]);
            assert_eq!(walk(a), [5, 3, 9, 1]);
            a = remove(&mut heap, &types, a, &[5]);
            a = insert(&mut heap, &types, a, &[5], &[50]);
            assert_eq!(walk(a), [3, 9, 1, 5]);
            // Many removals compact the slots and keep the order.
            let mut b = empty(&mut heap, INTS);
            for k in 0..5000 {
                b = insert(&mut heap, &types, b, &[k], &[k]);
            }
            for k in (0..5000).filter(|k| k % 7 != 0) {
                b = remove(&mut heap, &types, b, &[k]);
            }
            assert!(map_slots(b) <= 2 * length(b));
            assert_eq!(
                walk(b),
                (0..5000).filter(|k| k % 7 == 0).collect::<Vec<_>>()
            );
            for k in (0..5000).filter(|k| k % 7 == 0) {
                b = remove(&mut heap, &types, b, &[k]);
            }
            assert_eq!(length(b), 0);
            assert!(tree(b).is_null() && root(b).is_null());
            for m in [a, b] {
                drop_box(&mut heap, &types, m);
            }
        }
        assert_eq!(heap.live_blocks(), 0);
    }
}
