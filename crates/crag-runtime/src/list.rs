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

//! Persistent lists as RRB trees (Plan §11.4.13, after Bagwell and Rompf,
//! "RRB-Trees: Efficient Immutable Vectors").
//!
//! A list is a box holding its length, the height of its tree and the tree.
//! Leaves hold up to 32 elements and inner nodes up to 32 children, so an
//! index is found in a few steps. A balanced inner node has only complete
//! children but the last, and is indexed by the bits of the index; a
//! relaxed one, made by slicing or joining lists, keeps the cumulative sizes
//! of its children and is searched. Joining rebalances the nodes along the
//! seam, so relaxed trees stay shallow.
//!
//! Every node is a box with the list's type index and its kind in the upper
//! half of the index word. A function that takes a list by value updates in
//! place every node only its reference reaches, and copies the others: a
//! uniquely held list is updated in place, and a shared one shares all but
//! the changed path with its new version. Elements of no words, as in a
//! `List[Unit]`, need no tree: the length is the whole list.

use crag_abi::{ElementLayout, LEN_OFFSET, LIST_SIZE, TypeDescriptor};

use crate::die;
use crate::fiber::TaskContext;
use crate::heap::{Heap, alloc_box};
use crate::rc::{Types, drop_box, header, is_unique, release_value, retain, retain_value};
use crate::system::worker_of;

const BITS: usize = 5;
const WIDTH: usize = 1 << BITS;

/// Offsets in the list's box.
const HEIGHT: usize = 24;
const TREE: usize = 32;

/// The kinds of nodes.
pub(crate) const LEAF: u32 = 1;
pub(crate) const INNER: u32 = 2;

/// Offsets in a node: the slots in use, then a leaf's elements, or an inner
/// node's flag whether it is relaxed, its children and their cumulative
/// sizes, valid when it is.
const SLOTS: usize = 16;
const ELEMS: usize = 24;
const RELAXED: usize = 24;
const CHILDREN: usize = 32;
const SIZES: usize = CHILDREN + 8 * WIDTH;
const INNER_SIZE: usize = SIZES + 8 * WIDTH;

/// The word at `offset` in a box.
///
/// # Safety
///
/// The box at `ptr` has a word there.
unsafe fn at(ptr: *mut u8, offset: usize) -> *mut u64 {
    // SAFETY: as the caller promises.
    unsafe { ptr.add(offset).cast() }
}

/// The elements a complete subtree of height `h` holds.
fn complete(h: usize) -> usize {
    1 << (BITS * (h + 1))
}

/// A list's type and its element layout, with the heap to allocate from.
struct Lists<'a> {
    heap: &'a mut Heap,
    types: &'a Types,
    element: &'a ElementLayout,
    words: usize,
    /// The type index of the list, which its nodes carry too.
    index: u64,
}

impl<'a> Lists<'a> {
    /// # Safety
    ///
    /// `list` points at a live list whose type `types` describes.
    unsafe fn new(heap: &'a mut Heap, types: &'a Types, list: *mut u8) -> Lists<'a> {
        // SAFETY: as the caller promises.
        let (descriptor, index) = unsafe { (types.of(list), header(list) & 0xffff_ffff) };
        let TypeDescriptor::List { element } = descriptor else {
            die(&format!("a list of type {index}, which is not a list type"));
        };
        Lists {
            heap,
            types,
            element,
            words: element.words as usize,
            index,
        }
    }

    // The safety contract of every method below: the nodes passed are live
    // nodes of this list's type at the height given.

    unsafe fn slots(&self, node: *mut u8) -> usize {
        // SAFETY: see above.
        unsafe { at(node, SLOTS).read() as usize }
    }

    unsafe fn set_slots(&self, node: *mut u8, n: usize) {
        // SAFETY: see above.
        unsafe { at(node, SLOTS).write(n as u64) }
    }

    unsafe fn relaxed(&self, node: *mut u8, h: usize) -> bool {
        // SAFETY: see above.
        h > 0 && unsafe { at(node, RELAXED).read() } != 0
    }

    unsafe fn child(&self, node: *mut u8, j: usize) -> *mut u8 {
        // SAFETY: see above.
        unsafe { at(node, CHILDREN + 8 * j).cast::<*mut u8>().read() }
    }

    unsafe fn set_child(&self, node: *mut u8, j: usize, child: *mut u8) {
        // SAFETY: see above.
        unsafe { at(node, CHILDREN + 8 * j).cast::<*mut u8>().write(child) }
    }

    /// The elements of a relaxed node's children `0..=j`.
    unsafe fn cumulative(&self, node: *mut u8, j: usize) -> usize {
        // SAFETY: see above.
        unsafe { at(node, SIZES + 8 * j).read() as usize }
    }

    unsafe fn set_cumulative(&self, node: *mut u8, j: usize, size: usize) {
        // SAFETY: see above.
        unsafe { at(node, SIZES + 8 * j).write(size as u64) }
    }

    unsafe fn elem(&self, leaf: *mut u8, i: usize) -> *mut u8 {
        // SAFETY: see above.
        unsafe { leaf.add(ELEMS + 8 * self.words * i) }
    }

    /// The elements of a subtree, found along its right edge.
    unsafe fn size(&self, mut node: *mut u8, mut h: usize) -> usize {
        let mut total = 0;
        // SAFETY: see above.
        unsafe {
            loop {
                let n = self.slots(node);
                if h == 0 {
                    return total + n;
                }
                if self.relaxed(node, h) {
                    return total + self.cumulative(node, n - 1);
                }
                total += (n - 1) * complete(h - 1);
                node = self.child(node, n - 1);
                h -= 1;
            }
        }
    }

    /// Where child `j` of an inner node starts and ends.
    unsafe fn bounds(&self, node: *mut u8, h: usize, j: usize) -> (usize, usize) {
        // SAFETY: see above.
        unsafe {
            if self.relaxed(node, h) {
                let lo = if j == 0 {
                    0
                } else {
                    self.cumulative(node, j - 1)
                };
                (lo, self.cumulative(node, j))
            } else if j + 1 == self.slots(node) {
                (j * complete(h - 1), self.size(node, h))
            } else {
                (j * complete(h - 1), (j + 1) * complete(h - 1))
            }
        }
    }

    /// The child of an inner node holding index `i`, and the index in it.
    unsafe fn find(&self, node: *mut u8, h: usize, i: usize) -> (usize, usize) {
        // A child holds at most a complete subtree, so the child of a
        // balanced node's index is the first a relaxed one may have.
        let mut j = i / complete(h - 1);
        // SAFETY: see above.
        unsafe {
            if !self.relaxed(node, h) {
                return (j, i - j * complete(h - 1));
            }
            while self.cumulative(node, j) <= i {
                j += 1;
            }
            (j, i - self.bounds(node, h, j).0)
        }
    }

    fn new_leaf(&mut self) -> *mut u8 {
        let size = ELEMS + 8 * self.words * WIDTH;
        let leaf = alloc_box(self.heap, size, self.index | u64::from(LEAF) << 32);
        // SAFETY: the leaf has the word.
        unsafe { self.set_slots(leaf, 0) };
        leaf
    }

    /// An inner node of height `h` holding the children, whose references
    /// it takes. It is balanced when every child is, and every child but
    /// the last is complete.
    unsafe fn new_inner(&mut self, children: &[*mut u8], h: usize) -> *mut u8 {
        let node = alloc_box(self.heap, INNER_SIZE, self.index | u64::from(INNER) << 32);
        let mut balanced = true;
        let mut total = 0;
        // SAFETY: see above; the node has room for the children.
        unsafe {
            for (j, &child) in children.iter().enumerate() {
                let size = self.size(child, h - 1);
                balanced &= !self.relaxed(child, h - 1)
                    && (j + 1 == children.len() || size == complete(h - 1));
                total += size;
                self.set_child(node, j, child);
                self.set_cumulative(node, j, total);
            }
            self.set_slots(node, children.len());
            at(node, RELAXED).write(u64::from(!balanced));
        }
        node
    }

    /// The node itself if the caller's reference is its only one, else a
    /// copy, which holds references to what the node holds; the caller's
    /// reference to the node goes to the result.
    unsafe fn unique(&mut self, node: *mut u8, h: usize) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if is_unique(node) {
                return node;
            }
            let n = self.slots(node);
            let copy = if h == 0 {
                let copy = self.new_leaf();
                for i in 0..n {
                    self.copy_elem(node, i, copy, i);
                }
                copy
            } else {
                let copy = alloc_box(self.heap, INNER_SIZE, header(node));
                let from = node.add(SLOTS);
                from.copy_to_nonoverlapping(copy.add(SLOTS), INNER_SIZE - SLOTS);
                for j in 0..n {
                    retain(self.child(node, j));
                }
                copy
            };
            self.set_slots(copy, n);
            drop_box(self.heap, self.types, node);
            copy
        }
    }

    /// Copies element `i` of a leaf to slot `k` of another, with a
    /// reference to what it holds.
    unsafe fn copy_elem(&self, from: *mut u8, i: usize, to: *mut u8, k: usize) {
        // SAFETY: see above.
        unsafe {
            let src = self.elem(from, i);
            src.copy_to_nonoverlapping(self.elem(to, k), 8 * self.words);
            retain_value(src, self.element);
        }
    }

    /// The list's box itself if the caller's reference is its only one, else
    /// a copy holding a reference to the tree.
    unsafe fn unique_list(&mut self, list: *mut u8) -> *mut u8 {
        // SAFETY: `list` is a live list.
        unsafe {
            if is_unique(list) {
                return list;
            }
            let copy = alloc_box(self.heap, LIST_SIZE as usize, self.index);
            list.add(LEN_OFFSET as usize)
                .copy_to_nonoverlapping(copy.add(LEN_OFFSET as usize), 24);
            let tree = tree(list);
            if !tree.is_null() {
                retain(tree);
            }
            drop_box(self.heap, self.types, list);
            copy
        }
    }

    /// Appends to a node the caller holds the only reference to, unless it
    /// is full; then a new node of the same height holding only the value.
    unsafe fn push_node(&mut self, node: *mut u8, h: usize, value: &[u64]) -> Option<*mut u8> {
        // SAFETY: see above.
        unsafe {
            let n = self.slots(node);
            if h == 0 {
                if n == WIDTH {
                    let leaf = self.new_leaf();
                    self.write(leaf, 0, value);
                    self.set_slots(leaf, 1);
                    return Some(leaf);
                }
                self.write(node, n, value);
                self.set_slots(node, n + 1);
                return None;
            }
            let last = self.unique(self.child(node, n - 1), h - 1);
            self.set_child(node, n - 1, last);
            let relaxed = self.relaxed(node, h);
            let Some(new) = self.push_node(last, h - 1, value) else {
                if relaxed {
                    self.set_cumulative(node, n - 1, self.cumulative(node, n - 1) + 1);
                }
                return None;
            };
            if n == WIDTH {
                return Some(self.new_inner(&[new], h));
            }
            // In a balanced node a full last child was complete, so the node
            // stays balanced.
            self.set_child(node, n, new);
            if relaxed {
                self.set_cumulative(node, n, self.cumulative(node, n - 1) + 1);
            }
            self.set_slots(node, n + 1);
            None
        }
    }

    unsafe fn write(&self, leaf: *mut u8, i: usize, value: &[u64]) {
        // SAFETY: see above.
        unsafe {
            let dst = self.elem(leaf, i).cast::<u64>();
            dst.copy_from_nonoverlapping(value.as_ptr(), self.words);
        }
    }

    /// The elements `start..end` of a subtree, a non-empty range inside it,
    /// as a new reference to a subtree of the same height.
    unsafe fn slice_node(&mut self, node: *mut u8, h: usize, start: usize, end: usize) -> *mut u8 {
        // SAFETY: see above.
        unsafe {
            if start == 0 && end == self.size(node, h) {
                retain(node);
                return node;
            }
            if h == 0 {
                let leaf = self.new_leaf();
                for i in start..end {
                    self.copy_elem(node, i, leaf, i - start);
                }
                self.set_slots(leaf, end - start);
                return leaf;
            }
            let mut children = [std::ptr::null_mut(); WIDTH];
            let mut k = 0;
            for j in 0..self.slots(node) {
                let (lo, hi) = self.bounds(node, h, j);
                if hi <= start {
                    continue;
                }
                if lo >= end {
                    break;
                }
                let child = self.child(node, j);
                children[k] = self.slice_node(child, h - 1, start.max(lo) - lo, end.min(hi) - lo);
                k += 1;
            }
            self.new_inner(&children[..k], h)
        }
    }

    /// Joins two subtrees, which the caller keeps, into one or two new
    /// references to subtrees of the height of the taller.
    unsafe fn merge(&mut self, l: *mut u8, hl: usize, r: *mut u8, hr: usize) -> Vec<*mut u8> {
        // SAFETY: see above.
        unsafe {
            if hl == 0 && hr == 0 {
                let (nl, nr) = (self.slots(l), self.slots(r));
                if nl + nr > WIDTH {
                    retain(l);
                    retain(r);
                    return vec![l, r];
                }
                let leaf = self.new_leaf();
                for i in 0..nl {
                    self.copy_elem(l, i, leaf, i);
                }
                for i in 0..nr {
                    self.copy_elem(r, i, leaf, nl + i);
                }
                self.set_slots(leaf, nl + nr);
                return vec![leaf];
            }
            let h = hl.max(hr);
            let mut children = Vec::with_capacity(2 * WIDTH);
            let (nl, nr) = (self.slots(l), self.slots(r));
            if hl == h {
                for j in 0..nl - 1 {
                    retain(self.child(l, j));
                    children.push(self.child(l, j));
                }
            }
            let middle = match hl.cmp(&hr) {
                std::cmp::Ordering::Greater => self.merge(self.child(l, nl - 1), hl - 1, r, hr),
                std::cmp::Ordering::Less => self.merge(l, hl, self.child(r, 0), hr - 1),
                std::cmp::Ordering::Equal => {
                    self.merge(self.child(l, nl - 1), h - 1, self.child(r, 0), h - 1)
                }
            };
            children.extend(middle);
            if hr == h {
                for j in 1..nr {
                    retain(self.child(r, j));
                    children.push(self.child(r, j));
                }
            }
            self.rebalance(children, h)
        }
    }

    /// Spreads the slots of the children, whose references it takes, over
    /// as few nodes as keep a lookup's search short, and puts them in one
    /// or two nodes of height `h`.
    ///
    /// The nodes may number at most two more than the fewest that hold the
    /// slots (the search step invariant of the paper). Until they do, the
    /// first node that is not nearly full moves its slots into the nodes
    /// after it.
    unsafe fn rebalance(&mut self, children: Vec<*mut u8>, h: usize) -> Vec<*mut u8> {
        const EXTRA: usize = 2;
        // SAFETY: see above.
        unsafe {
            let mut plan: Vec<usize> = children.iter().map(|&c| self.slots(c)).collect();
            let fewest = plan.iter().sum::<usize>().div_ceil(WIDTH);
            while plan.len() > fewest + EXTRA {
                // Such a node exists, and the nodes after it have room for
                // its slots, since the slots fit in `fewest` full nodes.
                let i = plan.iter().position(|&n| n < WIDTH - EXTRA / 2).unwrap();
                let mut carry = plan.remove(i);
                for n in &mut plan[i..] {
                    let take = carry.min(WIDTH - *n);
                    *n += take;
                    carry -= take;
                }
                debug_assert_eq!(carry, 0);
            }
            let mut nodes = Vec::with_capacity(plan.len());
            let (mut c, mut offset) = (0, 0);
            for &size in &plan {
                if offset == 0 && self.slots(children[c]) == size {
                    nodes.push(children[c]);
                    c += 1;
                    continue;
                }
                // The node's slots: a leaf's elements, copied as they come,
                // or an inner node's children.
                let leaf = if h == 1 {
                    self.new_leaf()
                } else {
                    std::ptr::null_mut()
                };
                let mut gathered = Vec::with_capacity(size);
                let mut filled = 0;
                while filled < size {
                    let from = children[c];
                    let take = (size - filled).min(self.slots(from) - offset);
                    for k in offset..offset + take {
                        if h == 1 {
                            self.copy_elem(from, k, leaf, filled);
                        } else {
                            retain(self.child(from, k));
                            gathered.push(self.child(from, k));
                        }
                        filled += 1;
                    }
                    offset += take;
                    if offset == self.slots(from) {
                        drop_box(self.heap, self.types, from);
                        c += 1;
                        offset = 0;
                    }
                }
                if h == 1 {
                    self.set_slots(leaf, size);
                    nodes.push(leaf);
                } else {
                    nodes.push(self.new_inner(&gathered, h - 1));
                }
            }
            nodes
                .chunks(WIDTH)
                .map(|chunk| self.new_inner(chunk, h))
                .collect()
        }
    }
}

/// The length of a list.
///
/// # Safety
///
/// `list` points at a live list.
unsafe fn len(list: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { at(list, LEN_OFFSET as usize).read() as usize }
}

/// # Safety
///
/// `list` points at a live list.
unsafe fn tree(list: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe { at(list, TREE).cast::<*mut u8>().read() }
}

/// # Safety
///
/// `list` points at a live list.
unsafe fn height(list: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { at(list, HEIGHT).read() as usize }
}

/// # Safety
///
/// `list` points at a live list the caller holds the only reference to,
/// and the tree is of its type, or null.
unsafe fn set_tree(list: *mut u8, tree: *mut u8, h: usize) {
    // SAFETY: as the caller promises.
    unsafe {
        at(list, TREE).cast::<*mut u8>().write(tree);
        at(list, HEIGHT).write(h as u64);
    }
}

/// A new empty list of the type with this index, as generated code
/// allocates it.
pub fn empty(heap: &mut Heap, index: u32) -> *mut u8 {
    let list = alloc_box(heap, LIST_SIZE as usize, index.into());
    // SAFETY: the box has the words.
    unsafe {
        at(list, LEN_OFFSET as usize).write(0);
        set_tree(list, std::ptr::null_mut(), 0);
    }
    list
}

/// The number of elements of a list.
///
/// # Safety
///
/// `list` points at a live list.
pub unsafe fn length(list: *mut u8) -> usize {
    // SAFETY: as the caller promises.
    unsafe { len(list) }
}

/// The address of the words of element `i`, valid while the list is.
///
/// # Safety
///
/// `list` points at a live list whose type `types` describes, and `i` is
/// less than its length.
pub unsafe fn get(types: &Types, list: *mut u8, mut i: usize) -> *mut u64 {
    // SAFETY: as the caller promises; `types.of` dies for a list without a
    // descriptor.
    unsafe {
        let TypeDescriptor::List { element } = types.of(list) else {
            die("a list whose type is not a list type");
        };
        let mut node = tree(list);
        if element.words == 0 {
            return list.cast();
        }
        let lists = Lookup {
            words: element.words as usize,
        };
        let mut h = height(list);
        while h > 0 {
            let (j, rest) = lists.find(node, h, i);
            node = at(node, CHILDREN + 8 * j).cast::<*mut u8>().read();
            i = rest;
            h -= 1;
        }
        lists.elem(node, i).cast()
    }
}

/// What a lookup needs: no heap. Mirrors `Lists::find`.
struct Lookup {
    words: usize,
}

impl Lookup {
    /// # Safety
    ///
    /// `node` is a live inner node of height `h` holding index `i`.
    unsafe fn find(&self, node: *mut u8, h: usize, i: usize) -> (usize, usize) {
        let mut j = i / complete(h - 1);
        // SAFETY: as the caller promises.
        unsafe {
            if at(node, RELAXED).read() == 0 {
                return (j, i - j * complete(h - 1));
            }
            while at(node, SIZES + 8 * j).read() as usize <= i {
                j += 1;
            }
            let lo = if j == 0 {
                0
            } else {
                at(node, SIZES + 8 * (j - 1)).read()
            };
            (j, i - lo as usize)
        }
    }

    /// # Safety
    ///
    /// `leaf` is a live leaf with element `i`.
    unsafe fn elem(&self, leaf: *mut u8, i: usize) -> *mut u8 {
        // SAFETY: as the caller promises.
        unsafe { leaf.add(ELEMS + 8 * self.words * i) }
    }
}

/// The list with `value` appended, whose words are its first. It takes the
/// list's reference and the value's.
///
/// # Safety
///
/// `list` points at a live list whose type `types` describes, owned by the
/// caller, and `value` holds an element of its type.
pub unsafe fn push(heap: &mut Heap, types: &Types, list: *mut u8, value: &[u64]) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let mut l = Lists::new(heap, types, list);
        let list = l.unique_list(list);
        if l.words > 0 {
            let root = tree(list);
            let h = height(list);
            if root.is_null() {
                let leaf = l.new_leaf();
                l.write(leaf, 0, value);
                l.set_slots(leaf, 1);
                set_tree(list, leaf, 0);
            } else {
                let root = l.unique(root, h);
                match l.push_node(root, h, value) {
                    None => set_tree(list, root, h),
                    Some(new) => set_tree(list, l.new_inner(&[root, new], h + 1), h + 1),
                }
            }
        }
        at(list, LEN_OFFSET as usize).write(len(list) as u64 + 1);
        list
    }
}

/// The list with element `i` replaced by `value`. It takes the list's
/// reference and the value's, and releases the old element.
///
/// # Safety
///
/// As for [`push`], and `i` is less than the list's length.
pub unsafe fn set(
    heap: &mut Heap,
    types: &Types,
    list: *mut u8,
    mut i: usize,
    value: &[u64],
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let mut l = Lists::new(heap, types, list);
        let list = l.unique_list(list);
        if l.words == 0 {
            return list;
        }
        let mut h = height(list);
        let mut node = l.unique(tree(list), h);
        set_tree(list, node, h);
        while h > 0 {
            let (j, rest) = l.find(node, h, i);
            let child = l.unique(l.child(node, j), h - 1);
            l.set_child(node, j, child);
            node = child;
            i = rest;
            h -= 1;
        }
        let elem = l.elem(node, i);
        release_value(l.heap, l.types, elem, l.element);
        l.write(node, i, value);
        list
    }
}

/// A new list of the elements without the first `front` and the last
/// `back`. It borrows the list.
///
/// # Safety
///
/// `list` points at a live list whose type `types` describes, and
/// `front + back` is at most its length.
pub unsafe fn slice(
    heap: &mut Heap,
    types: &Types,
    list: *mut u8,
    front: usize,
    back: usize,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let mut l = Lists::new(heap, types, list);
        let n = len(list);
        let out = empty(l.heap, l.index as u32);
        at(out, LEN_OFFSET as usize).write((n - front - back) as u64);
        if l.words == 0 || front + back == n {
            return out;
        }
        let mut h = height(list);
        let mut node = l.slice_node(tree(list), h, front, n - back);
        // A root with one child is that child.
        while h > 0 && l.slots(node) == 1 {
            let child = l.child(node, 0);
            retain(child);
            drop_box(l.heap, l.types, node);
            node = child;
            h -= 1;
        }
        set_tree(out, node, h);
        out
    }
}

/// A new list of the elements of `a` followed by those of `b`, of the same
/// type. It borrows both.
///
/// # Safety
///
/// `a` and `b` point at live lists of one type that `types` describes.
pub unsafe fn concat(heap: &mut Heap, types: &Types, a: *mut u8, b: *mut u8) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let mut l = Lists::new(heap, types, a);
        if len(b) == 0 || len(a) == 0 {
            let whole = if len(b) == 0 { a } else { b };
            retain(whole);
            return whole;
        }
        let out = empty(l.heap, l.index as u32);
        at(out, LEN_OFFSET as usize).write((len(a) + len(b)) as u64);
        if l.words == 0 {
            return out;
        }
        let h = height(a).max(height(b));
        let nodes = l.merge(tree(a), height(a), tree(b), height(b));
        match nodes[..] {
            [one] => set_tree(out, one, h),
            _ => set_tree(out, l.new_inner(&nodes, h + 1), h + 1),
        }
        out
    }
}

/// Calls `f` with each box a list's box or node holds: the tree, the
/// children, or what the elements hold.
///
/// # Safety
///
/// `ptr` points at a live list or node of a list type with this element
/// layout, and `kind` is its kind.
pub(crate) unsafe fn boxes_of(
    ptr: *mut u8,
    kind: u32,
    element: &ElementLayout,
    f: &mut impl FnMut(*mut u8),
) {
    // SAFETY: as the caller promises.
    unsafe {
        match kind {
            LEAF => {
                let words = element.words as usize;
                for i in 0..at(ptr, SLOTS).read() as usize {
                    let elem = ptr.add(ELEMS + 8 * words * i);
                    crate::rc::boxes_in(elem, &element.counted, &mut *f);
                }
            }
            INNER => {
                for j in 0..at(ptr, SLOTS).read() as usize {
                    f(at(ptr, CHILDREN + 8 * j).cast::<*mut u8>().read());
                }
            }
            _ => {
                let tree = tree(ptr);
                if !tree.is_null() {
                    f(tree);
                }
            }
        }
    }
}

system_stack_fn! {
    /// `rt_list_push(ctx, list, w0, w1)`: see `crag_abi::RuntimeFn::ListPush`.
    fn rt_list_push(ctx: *const TaskContext, list: *mut u8, w0: u64, w1: u64) -> *mut u8
        => push_entry
}

system_stack_fn! {
    /// `rt_list_elem(ctx, list, index)`: see `crag_abi::RuntimeFn::ListElem`.
    fn rt_list_elem(ctx: *const TaskContext, list: *mut u8, index: u64) -> *mut u64
        => elem_entry
}

system_stack_fn! {
    /// `rt_list_slice(ctx, list, front, back)`: see
    /// `crag_abi::RuntimeFn::ListSlice`.
    fn rt_list_slice(ctx: *const TaskContext, list: *mut u8, front: u64, back: u64) -> *mut u8
        => slice_entry
}

/// The Rust halves of the functions above, on the system stack.
///
/// # Safety
///
/// Called only by those functions, with what generated code passed them.
unsafe extern "C" fn push_entry(
    ctx: *const TaskContext,
    list: *mut u8,
    w0: u64,
    w1: u64,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        push(heap, types, list, &[w0, w1])
    }
}

/// See `push_entry`.
///
/// # Safety
///
/// See `push_entry`.
unsafe extern "C" fn elem_entry(ctx: *const TaskContext, list: *mut u8, index: u64) -> *mut u64 {
    // SAFETY: as the caller promises.
    unsafe {
        let (_, types) = worker_of(ctx);
        get(types, list, index as usize)
    }
}

/// See `push_entry`.
///
/// # Safety
///
/// See `push_entry`.
unsafe extern "C" fn slice_entry(
    ctx: *const TaskContext,
    list: *mut u8,
    front: u64,
    back: u64,
) -> *mut u8 {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        slice(heap, types, list, front as usize, back as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crag_abi::CountedField;

    use crate::testing::{REC, Rng, boxed, unboxed};

    const INTS: u32 = 20;
    const BOXES: u32 = 21;
    const UNIONS: u32 = 22;
    const UNITS: u32 = 23;
    /// The index a union of `UNIONS` carries for an `Int`.
    const INT: u64 = 1;

    fn types() -> Types {
        let list = |words, counted| TypeDescriptor::List {
            element: ElementLayout { words, counted },
        };
        Types::new([
            (REC, TypeDescriptor::Record { counted: vec![] }),
            (INTS, list(1, vec![])),
            (BOXES, list(1, vec![CountedField::Box(0)])),
            (
                UNIONS,
                list(
                    2,
                    vec![CountedField::Union {
                        offset: 0,
                        boxed: vec![REC],
                    }],
                ),
            ),
            (UNITS, list(0, vec![])),
        ])
    }

    /// An element of a list of type `index` standing for `v`.
    fn make(heap: &mut Heap, index: u32, v: u64) -> Vec<u64> {
        match index {
            INTS => vec![v],
            BOXES => vec![boxed(heap, v) as u64],
            UNIONS if v.is_multiple_of(2) => vec![INT, v],
            UNIONS => vec![u64::from(REC), boxed(heap, v) as u64],
            _ => vec![],
        }
    }

    /// What the element at `ptr` stands for.
    unsafe fn read(index: u32, ptr: *mut u64) -> u64 {
        // SAFETY: as the caller promises.
        unsafe {
            match index {
                INTS => ptr.read(),
                BOXES => unboxed(ptr.read() as *mut u8),
                UNIONS if ptr.read() == INT => ptr.add(1).read(),
                UNIONS => unboxed(ptr.add(1).read() as *mut u8),
                _ => 0,
            }
        }
    }

    /// Checks the shape of a subtree: slots, sizes, balance and height; its
    /// size.
    unsafe fn check_node(l: &Lists, node: *mut u8, h: usize) -> usize {
        // SAFETY: the tree is live.
        unsafe {
            let n = l.slots(node);
            assert!((1..=WIDTH).contains(&n));
            assert_eq!(
                (header(node) >> 32) as u32,
                if h == 0 { LEAF } else { INNER }
            );
            if h == 0 {
                return n;
            }
            let mut total = 0;
            let mut balanced = true;
            for j in 0..n {
                let child = l.child(node, j);
                let size = check_node(l, child, h - 1);
                balanced &= !l.relaxed(child, h - 1) && (j + 1 == n || size == complete(h - 1));
                total += size;
                if l.relaxed(node, h) {
                    assert_eq!(l.cumulative(node, j), total);
                }
            }
            if !l.relaxed(node, h) {
                assert!(balanced, "a balanced node with a child that does not fit");
            }
            assert_eq!(l.size(node, h), total);
            total
        }
    }

    /// Checks a list against its model, every element or a few.
    unsafe fn check(
        heap: &mut Heap,
        types: &Types,
        list: *mut u8,
        model: &[u64],
        rng: &mut Rng,
        all: bool,
    ) {
        // SAFETY: the list is live.
        unsafe {
            assert_eq!(len(list), model.len());
            let index = header(list) as u32;
            let tree = tree(list);
            let l = Lists::new(heap, types, list);
            if l.words == 0 || model.is_empty() {
                assert!(tree.is_null());
                return;
            }
            assert_eq!(check_node(&l, tree, height(list)), model.len());
            let picks: Vec<usize> = match all {
                true => (0..model.len()).collect(),
                false => (0..8).map(|_| rng.below(model.len())).collect(),
            };
            for i in picks {
                assert_eq!(read(index, get(types, list, i)), model[i], "element {i}");
            }
        }
    }

    /// Random pushes, sets, slices, joins and drops over versions that share
    /// structure, against vectors.
    fn random_operations(index: u32, seed: u64, steps: usize) {
        let mut heap = Heap::new();
        let types = types();
        let mut rng = Rng(seed);
        let mut pool: Vec<(*mut u8, Vec<u64>)> = vec![(empty(&mut heap, index), Vec::new())];
        let mut next = 0;
        // SAFETY: every list in the pool is live and owned by it.
        unsafe {
            for step in 0..steps {
                let k = rng.below(pool.len());
                let (list, model) = pool[k].clone();
                // Keep the old version sometimes, so the update must copy.
                let keep = rng.below(3) == 0;
                if keep {
                    retain(list);
                    pool.push((list, model.clone()));
                }
                match rng.below(10) {
                    0..=4 => {
                        let mut model = model;
                        let most = if rng.below(4) == 0 { 2000 } else { 40 };
                        let count = 1 + rng.below(most);
                        let mut list = list;
                        for _ in 0..count {
                            next += 1;
                            let value = make(&mut heap, index, next);
                            list = push(&mut heap, &types, list, &value);
                            model.push(next);
                        }
                        pool[k] = (list, model);
                    }
                    5 if !model.is_empty() => {
                        let i = rng.below(model.len());
                        next += 1;
                        let value = make(&mut heap, index, next);
                        let list = set(&mut heap, &types, list, i, &value);
                        let mut model = model;
                        model[i] = next;
                        pool[k] = (list, model);
                    }
                    6 | 7 => {
                        let front = rng.below(model.len() + 1);
                        let back = rng.below(model.len() - front + 1);
                        let part = slice(&mut heap, &types, list, front, back);
                        pool.push((part, model[front..model.len() - back].to_vec()));
                    }
                    8 => {
                        let (other, rest) = pool[rng.below(pool.len())].clone();
                        if model.len() + rest.len() < 100_000 {
                            let joined = concat(&mut heap, &types, list, other);
                            pool.push((joined, [model, rest].concat()));
                        }
                    }
                    _ if pool.len() > 1 => {
                        let (list, _) = pool.swap_remove(k);
                        drop_box(&mut heap, &types, list);
                    }
                    _ => {}
                }
                while pool.len() > 24 {
                    let (list, _) = pool.swap_remove(rng.below(pool.len()));
                    drop_box(&mut heap, &types, list);
                }
                for (list, model) in &pool {
                    check(&mut heap, &types, *list, model, &mut rng, step % 64 == 0);
                }
            }
            for (list, _) in pool {
                drop_box(&mut heap, &types, list);
            }
        }
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn lists_of_words_behave_like_vectors() {
        random_operations(INTS, 1, 1500);
    }

    #[test]
    fn lists_of_boxes_count_their_elements() {
        random_operations(BOXES, 2, 800);
    }

    #[test]
    fn lists_of_unions_count_the_boxes_among_them() {
        random_operations(UNIONS, 3, 800);
    }

    #[test]
    fn lists_without_words_are_their_length() {
        random_operations(UNITS, 4, 300);
    }

    #[test]
    fn a_unique_list_grows_in_place() {
        let mut heap = Heap::new();
        let types = types();
        let mut list = empty(&mut heap, INTS);
        let first = list;
        // SAFETY: the list is live, and only this reference holds it.
        unsafe {
            for v in 0..100_000 {
                list = push(&mut heap, &types, list, &[v]);
            }
            assert_eq!(list, first);
            // The tree is balanced and as low as it can be.
            assert_eq!(height(list), 3);
            assert_eq!(at(tree(list), RELAXED).read(), 0);
            let before = heap.live_blocks();
            list = set(&mut heap, &types, list, 77_777, &[1]);
            assert_eq!(heap.live_blocks(), before);
            assert_eq!(get(&types, list, 77_777).read(), 1);
            drop_box(&mut heap, &types, list);
        }
        assert_eq!(heap.live_blocks(), 0);
    }

    /// The leaves of a subtree.
    unsafe fn leaves(l: &Lists, node: *mut u8, h: usize) -> usize {
        // SAFETY: the tree is live.
        unsafe {
            match h {
                0 => 1,
                _ => (0..l.slots(node))
                    .map(|j| leaves(l, l.child(node, j), h - 1))
                    .sum(),
            }
        }
    }

    #[test]
    fn joined_lists_stay_shallow() {
        let mut heap = Heap::new();
        let types = types();
        let mut rng = Rng(5);
        let mut model = Vec::new();
        // SAFETY: every list is live and owned here.
        unsafe {
            let mut whole = empty(&mut heap, INTS);
            for _ in 0..2000 {
                let mut part = empty(&mut heap, INTS);
                for _ in 0..1 + rng.below(50) {
                    let v = model.len() as u64;
                    part = push(&mut heap, &types, part, &[v]);
                    model.push(v);
                }
                let joined = concat(&mut heap, &types, whole, part);
                drop_box(&mut heap, &types, whole);
                drop_box(&mut heap, &types, part);
                whole = joined;
            }
            check(&mut heap, &types, whole, &model, &mut rng, true);
            // About 50 000 elements fit in a tree of height 3, and in not
            // many more leaves than they fill. Without rebalancing the
            // leaves would be a third more than that.
            assert_eq!(height(whole), 3);
            let l = Lists::new(&mut heap, &types, whole);
            let fewest = model.len().div_ceil(WIDTH);
            let leaves = leaves(&l, tree(whole), 3);
            assert!(leaves <= fewest + fewest / 10, "{leaves} leaves");
            drop_box(&mut heap, &types, whole);
        }
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn taking_the_first_element_off_again_and_again_walks_the_list() {
        let mut heap = Heap::new();
        let types = types();
        // SAFETY: every list is live and owned here.
        unsafe {
            let mut list = empty(&mut heap, BOXES);
            for v in 0..5000 {
                let value = [boxed(&mut heap, v) as u64];
                list = push(&mut heap, &types, list, &value);
            }
            for v in 0..5000 {
                assert_eq!(unboxed(get(&types, list, 0).read() as *mut u8), v);
                let rest = slice(&mut heap, &types, list, 1, 0);
                drop_box(&mut heap, &types, list);
                list = rest;
            }
            assert_eq!(len(list), 0);
            drop_box(&mut heap, &types, list);
        }
        assert_eq!(heap.live_blocks(), 0);
    }
}
