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

//! The structural node store (Plan §11.11.3): durable collection values
//! over the storage facade of `crag-dur`.
//!
//! A durable collection is the tree its in-memory form has (Plan
//! §11.4.13), each node stored under a [`NodeId`] and naming its children
//! by their ids instead of pointers. Reading walks ids through [`load`]:
//! decoded nodes live in a [`NodeCache`] shared by every task, which
//! needs no invalidation because an id never changes meaning, and only
//! the nodes along the path fault in, so a large value is never loaded
//! whole. An update path-copies: the fresh nodes ([`Node`]) carry the
//! changed path and keep the subtrees they share as [`Child::Stored`]
//! ids, so [`collect_overlay`] is exactly the set of nodes the commit
//! writes.
//!
//! A [`DurRoot`] names a committed value. Holding it pins the root in
//! the process-wide pin table, so the reclamation sweep
//! ([`sweep_free_list`], Plan §11.11.9) leaves that version readable
//! while a task still walks it; after a crash the table is empty and the
//! startup sweep frees what old roots left.
//!
//! Lists are structural ([`DurList`]), for elements without references;
//! maps, and elements with references (Plan §11.11.6), follow. A slot
//! whose value has no structural encoding stays the whole-value node of
//! `dur` (`KIND_WORDS`).

use std::collections::HashMap;
use std::sync::{Arc, LazyLock, Mutex};

use crag_abi::ElementLayout;
use crag_dur::{
    CommitBatch, DescriptorId, HeadKey, HeadMove, NodeHeader, NodeId, NodeStore, StoreError,
    decode_node, encode_node,
};

use crate::die;
use crate::heap::Heap;
use crate::list;
use crate::rc::Types;

/// The kind bytes of the structural nodes; `dur::KIND_WORDS` is 0.
pub(crate) const LIST: u8 = 1;
pub(crate) const LIST_LEAF: u8 = 2;
pub(crate) const LIST_INNER: u8 = 3;

/// The branching of the trees, as in `list`.
const BITS: usize = 5;
const WIDTH: usize = 1 << BITS;

/// A stored node, decoded once: its header and the payload behind it.
pub struct DecodedNode {
    pub header: NodeHeader,
    pub payload: Box<[u8]>,
}

impl DecodedNode {
    fn decode(bytes: &[u8]) -> Result<DecodedNode, StoreError> {
        let (header, payload) = decode_node(bytes)?;
        Ok(DecodedNode {
            header,
            payload: payload.into(),
        })
    }

    /// What the node costs the cache, with the entry around it.
    fn bytes(&self) -> usize {
        64 + 8 * self.header.children.len() + self.payload.len()
    }
}

/// The shared cache of decoded nodes: sharded, bounded by bytes, evicting
/// entries no task borrows in CLOCK order. It needs no invalidation: an
/// id never changes meaning, so an entry is only ever stale when its node
/// was freed, and then nothing asks for it.
pub struct NodeCache {
    shards: Vec<Mutex<Shard>>,
    /// The byte bound of one shard.
    limit: usize,
}

#[derive(Default)]
struct Shard {
    entries: HashMap<u64, Entry>,
    /// The ids of the entries, the CLOCK's ring; each entry is on it once.
    ring: Vec<u64>,
    /// Where the CLOCK's hand points into `ring`.
    hand: usize,
    bytes: usize,
}

struct Entry {
    node: Arc<DecodedNode>,
    /// Set on a hit, cleared when the hand passes: a second chance.
    used: bool,
}

const SHARDS: usize = 16;

impl NodeCache {
    /// A cache holding at most about `bytes`. The bound may be exceeded
    /// while borrowed nodes keep their entries unevictable.
    pub fn new(bytes: usize) -> NodeCache {
        NodeCache {
            shards: (0..SHARDS).map(|_| Mutex::new(Shard::default())).collect(),
            limit: (bytes / SHARDS).max(1),
        }
    }

    fn shard(&self, id: NodeId) -> &Mutex<Shard> {
        let spread = id.0.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        &self.shards[(spread >> 59) as usize % SHARDS]
    }

    fn hit(&self, id: NodeId) -> Option<Arc<DecodedNode>> {
        let mut shard = self.shard(id).lock().expect("a poisoned cache");
        let entry = shard.entries.get_mut(&id.0)?;
        entry.used = true;
        Some(entry.node.clone())
    }

    fn insert(&self, id: NodeId, node: Arc<DecodedNode>) {
        let mut shard = self.shard(id).lock().expect("a poisoned cache");
        if shard.entries.contains_key(&id.0) {
            // Another task loaded it first; the copies are equal.
            return;
        }
        shard.bytes += node.bytes();
        shard.entries.insert(id.0, Entry { node, used: true });
        shard.ring.push(id.0);
        // The CLOCK: clear second chances and evict unborrowed entries
        // until the shard fits, giving up after two turns of the ring.
        let mut scanned = 0;
        while shard.bytes > self.limit && scanned < 2 * shard.ring.len() {
            scanned += 1;
            if shard.hand >= shard.ring.len() {
                shard.hand = 0;
            }
            let candidate = shard.ring[shard.hand];
            let evict = {
                let entry = shard
                    .entries
                    .get_mut(&candidate)
                    .expect("every ring id has its entry");
                if entry.used {
                    entry.used = false;
                    None
                } else if Arc::strong_count(&entry.node) > 1 {
                    None
                } else {
                    Some(entry.node.bytes())
                }
            };
            match evict {
                None => shard.hand += 1,
                Some(cost) => {
                    shard.entries.remove(&candidate);
                    shard.bytes -= cost;
                    let hand = shard.hand;
                    shard.ring.swap_remove(hand);
                }
            }
        }
    }

    /// The bytes the cached nodes take, for `stats`.
    pub fn bytes(&self) -> usize {
        self.shards
            .iter()
            .map(|s| s.lock().expect("a poisoned cache").bytes)
            .sum()
    }
}

/// The bytes of a stored node, decoded, through the cache.
pub fn load(
    cache: &NodeCache,
    store: &dyn NodeStore,
    id: NodeId,
) -> Result<Arc<DecodedNode>, StoreError> {
    if let Some(node) = cache.hit(id) {
        return Ok(node);
    }
    let bytes = store.get(id)?;
    let node = Arc::new(DecodedNode::decode(&bytes)?);
    drop(bytes);
    cache.insert(id, node.clone());
    Ok(node)
}

/// A subtree under an update: kept whole from the store, or created by
/// the update.
pub enum Child {
    /// A stored subtree, unchanged, named by its id.
    Stored(NodeId),
    /// A node the update created.
    Fresh(Box<Node>),
}

/// An in-memory node an uncommitted update created on top of a stored
/// value: the overlay of Plan §11.11.3. Path copying makes the fresh
/// nodes under a new root exactly the set a commit writes.
pub struct Node {
    pub(crate) kind: u8,
    pub(crate) children: Vec<Child>,
    pub(crate) payload: Vec<u8>,
}

impl Node {
    /// The fresh nodes under this root, itself included.
    pub fn fresh_count(&self) -> u64 {
        let children: u64 = self
            .children
            .iter()
            .map(|c| match c {
                Child::Stored(_) => 0,
                Child::Fresh(f) => f.fresh_count(),
            })
            .sum();
        children + 1
    }

    /// Encodes this node and its fresh descendants into `out`, children
    /// first; the node's own id.
    pub fn encode(
        &self,
        descriptor: DescriptorId,
        ids: &mut IdAllocator,
        out: &mut Vec<(NodeId, Vec<u8>)>,
    ) -> NodeId {
        let children = self
            .children
            .iter()
            .map(|c| match c {
                Child::Stored(id) => *id,
                Child::Fresh(f) => f.encode(descriptor, ids, out),
            })
            .collect();
        let id = ids.take();
        let header = NodeHeader {
            descriptor,
            kind: self.kind,
            children,
        };
        out.push((id, encode_node(&header, &self.payload)));
        id
    }
}

/// The nodes of an update not already stored, every parent after its
/// children: a subtree that still carries a stored id is skipped whole.
pub fn collect_overlay(root: &Node) -> Vec<&Node> {
    fn walk<'a>(node: &'a Node, out: &mut Vec<&'a Node>) {
        for child in &node.children {
            if let Child::Fresh(f) = child {
                walk(f, out);
            }
        }
        out.push(node);
    }
    let mut out = Vec::new();
    walk(root, &mut out);
    out
}

/// Fresh node ids for one commit, taken from the store in one call.
pub struct IdAllocator {
    next: u64,
}

impl IdAllocator {
    pub fn new(store: &dyn NodeStore, count: u64) -> IdAllocator {
        IdAllocator {
            next: store.allocate(count).0,
        }
    }

    fn take(&mut self) -> NodeId {
        let id = NodeId(self.next);
        self.next += 1;
        id
    }
}

/// The batch of one update: the overlay encoded under fresh ids, and the
/// head moved from the version read to the new root; the new root's id.
pub fn overlay_batch(
    store: &dyn NodeStore,
    root: &Node,
    key: HeadKey,
    descriptor: DescriptorId,
    read: u64,
) -> (NodeId, CommitBatch) {
    let mut ids = IdAllocator::new(store, root.fresh_count());
    let mut nodes = Vec::new();
    let id = root.encode(descriptor, &mut ids, &mut nodes);
    let batch = CommitBatch {
        nodes,
        heads: vec![HeadMove {
            key,
            root: id,
            descriptor,
            read,
        }],
        descriptors: Vec::new(),
        frees: Vec::new(),
    };
    (id, batch)
}

/// The process-wide pins of durable roots (Plan §11.11.9): how many
/// holders pin each node of each store. After a crash the table is empty,
/// so the startup sweep frees every old root.
static PINS: LazyLock<Mutex<HashMap<(usize, u64), u64>>> = LazyLock::new(Default::default);

/// One store's identity in the pin table.
fn store_key(store: &Arc<dyn NodeStore>) -> usize {
    Arc::as_ptr(store) as *const () as usize
}

/// Holds a pin on a root; dropping it releases the pin.
pub struct PinGuard {
    store: usize,
    id: u64,
}

/// Pins `root`, so the sweep leaves it and everything under it stored.
pub fn pin(store: &Arc<dyn NodeStore>, root: NodeId) -> PinGuard {
    let key = (store_key(store), root.0);
    *PINS
        .lock()
        .expect("a poisoned pin table")
        .entry(key)
        .or_insert(0) += 1;
    PinGuard {
        store: key.0,
        id: key.1,
    }
}

impl Drop for PinGuard {
    fn drop(&mut self) {
        let mut pins = PINS.lock().expect("a poisoned pin table");
        let count = pins
            .get_mut(&(self.store, self.id))
            .expect("every guard has its pin");
        *count -= 1;
        if *count == 0 {
            pins.remove(&(self.store, self.id));
        }
    }
}

fn pinned(store: usize, id: u64) -> bool {
    PINS.lock()
        .expect("a poisoned pin table")
        .contains_key(&(store, id))
}

/// Frees up to `budget` nodes of the store's durable free list, pinned
/// roots excepted; what it freed. A freed node's children reach the free
/// list in its place, so the sweep runs until the budget or the list,
/// pins aside, is spent.
pub fn sweep_free_list(store: &Arc<dyn NodeStore>, budget: usize) -> Result<usize, StoreError> {
    let key = store_key(store);
    let mut freed = 0;
    while freed < budget {
        let candidates = store.freeable(budget)?;
        let free: Vec<NodeId> = candidates
            .into_iter()
            .filter(|id| !pinned(key, id.0))
            .take(budget - freed)
            .collect();
        if free.is_empty() {
            break;
        }
        store.free(&free)?;
        freed += free.len();
    }
    Ok(freed)
}

/// A committed value: its store, its root node and the commit version
/// that moved it there. Holding it pins the root (Plan §11.11.9), so the
/// version stays readable until the handle drops.
pub struct DurRoot {
    store: Arc<dyn NodeStore>,
    root: NodeId,
    version: u64,
    _pin: PinGuard,
}

impl DurRoot {
    pub fn new(store: Arc<dyn NodeStore>, root: NodeId, version: u64) -> DurRoot {
        let pin = pin(&store, root);
        DurRoot {
            store,
            root,
            version,
            _pin: pin,
        }
    }

    pub fn store(&self) -> &Arc<dyn NodeStore> {
        &self.store
    }

    pub fn root(&self) -> NodeId {
        self.root
    }

    pub fn version(&self) -> u64 {
        self.version
    }
}

/// A corrupt stored node.
fn corrupt(what: &str) -> StoreError {
    StoreError::StoreFault(format!("a stored list is corrupt: {what}"))
}

/// The length and height of a stored list, off its root node's payload.
fn list_parts(node: &DecodedNode) -> Result<(usize, usize), StoreError> {
    if node.header.kind != LIST || node.payload.len() != 16 {
        return Err(corrupt("the root is not a list node"));
    }
    let len = u64::from_le_bytes(node.payload[..8].try_into().expect("sized"));
    let height = u64::from_le_bytes(node.payload[8..].try_into().expect("sized"));
    Ok((len as usize, height as usize))
}

fn list_payload(len: usize, height: usize) -> Vec<u8> {
    let mut payload = Vec::with_capacity(16);
    payload.extend_from_slice(&(len as u64).to_le_bytes());
    payload.extend_from_slice(&(height as u64).to_le_bytes());
    payload
}

/// Whether an inner node's payload says it is relaxed.
fn payload_relaxed(payload: &[u8]) -> Result<bool, StoreError> {
    match payload.first() {
        Some(flag) => Ok(*flag != 0),
        None => Err(corrupt("an inner node without its relaxed flag")),
    }
}

/// The elements of a relaxed node's children `0..=j`, off its payload.
fn payload_cumulative(payload: &[u8], j: usize) -> Result<usize, StoreError> {
    let bytes = payload
        .get(1 + 8 * j..9 + 8 * j)
        .ok_or_else(|| corrupt("a relaxed node without its sizes"))?;
    Ok(u64::from_le_bytes(bytes.try_into().expect("sized")) as usize)
}

/// How a subtree of an update grew: in place along a fresh path, or past
/// its width into a new sibling.
enum Push {
    /// A fresh version of the subtree, the value appended.
    Grown(Node),
    /// The subtree was full; a fresh sibling of its height holding the
    /// value alone.
    Split(Node),
}

/// Reading and updating a durable list of this element layout, over a
/// store and the shared cache. Elements hold no references until Plan
/// §11.11.6.
pub struct DurList<'a> {
    pub store: &'a dyn NodeStore,
    pub cache: &'a NodeCache,
    pub element: &'a ElementLayout,
}

impl DurList<'_> {
    fn load(&self, id: NodeId) -> Result<Arc<DecodedNode>, StoreError> {
        load(self.cache, self.store, id)
    }

    fn size(&self) -> usize {
        self.element.size as usize
    }

    /// The elements a complete subtree of height `h` holds.
    fn complete(&self, h: usize) -> usize {
        list::leaf_width(self.element) << (BITS * h)
    }

    fn leaf_slots(&self, node: &DecodedNode) -> Result<usize, StoreError> {
        if node.header.kind != LIST_LEAF || !node.payload.len().is_multiple_of(self.size()) {
            return Err(corrupt("a leaf of torn elements"));
        }
        Ok(node.payload.len() / self.size())
    }

    /// The number of elements of the stored list under `root`.
    pub fn len(&self, root: NodeId) -> Result<usize, StoreError> {
        let node = self.load(root)?;
        Ok(list_parts(&node)?.0)
    }

    /// Copies the bytes of element `i` into `out`, faulting in only the
    /// path to its leaf.
    pub fn get(&self, root: NodeId, mut i: usize, out: &mut [u8]) -> Result<(), StoreError> {
        let size = self.size();
        debug_assert_eq!(out.len(), size);
        let root = self.load(root)?;
        let (len, mut h) = list_parts(&root)?;
        if i >= len {
            die("a durable list element read outside the list");
        }
        if size == 0 {
            return Ok(());
        }
        let mut id = *root
            .header
            .children
            .first()
            .ok_or_else(|| corrupt("elements without a tree"))?;
        loop {
            let node = self.load(id)?;
            if h == 0 {
                let n = self.leaf_slots(&node)?;
                if i >= n {
                    return Err(corrupt("an element past its leaf"));
                }
                out.copy_from_slice(&node.payload[size * i..size * (i + 1)]);
                return Ok(());
            }
            if node.header.kind != LIST_INNER {
                return Err(corrupt("a leaf where the height says an inner node"));
            }
            let (j, rest) = self.find(&node, h, i)?;
            id = *node
                .header
                .children
                .get(j)
                .ok_or_else(|| corrupt("an index past its node's children"))?;
            i = rest;
            h -= 1;
        }
    }

    /// The child of a stored inner node holding index `i`, and the index
    /// in it. Mirrors `list`'s lookup.
    fn find(&self, node: &DecodedNode, h: usize, i: usize) -> Result<(usize, usize), StoreError> {
        let complete = self.complete(h - 1);
        let mut j = i / complete;
        if !payload_relaxed(&node.payload)? {
            return Ok((j, i - j * complete));
        }
        while payload_cumulative(&node.payload, j)? <= i {
            j += 1;
        }
        let lo = match j {
            0 => 0,
            _ => payload_cumulative(&node.payload, j - 1)?,
        };
        Ok((j, i - lo))
    }

    /// The elements of a stored subtree, found along its right edge.
    fn stored_size(&self, mut id: NodeId, mut h: usize) -> Result<usize, StoreError> {
        let mut total = 0;
        loop {
            let node = self.load(id)?;
            if h == 0 {
                return Ok(total + self.leaf_slots(&node)?);
            }
            let n = node.header.children.len();
            if n == 0 {
                return Err(corrupt("an inner node without children"));
            }
            if payload_relaxed(&node.payload)? {
                return Ok(total + payload_cumulative(&node.payload, n - 1)?);
            }
            total += (n - 1) * self.complete(h - 1);
            id = node.header.children[n - 1];
            h -= 1;
        }
    }

    /// The elements of a subtree of an update, stored or fresh.
    fn child_size(&self, child: &Child, h: usize) -> Result<usize, StoreError> {
        match child {
            Child::Stored(id) => self.stored_size(*id, h),
            Child::Fresh(node) if h == 0 => Ok(node.payload.len() / self.size().max(1)),
            Child::Fresh(node) => {
                let n = node.children.len();
                if payload_relaxed(&node.payload)? {
                    return payload_cumulative(&node.payload, n - 1);
                }
                Ok((n - 1) * self.complete(h - 1)
                    + self.child_size(&node.children[n - 1], h - 1)?)
            }
        }
    }

    /// Whether a subtree of an update is relaxed.
    fn child_relaxed(&self, child: &Child, h: usize) -> Result<bool, StoreError> {
        if h == 0 {
            return Ok(false);
        }
        match child {
            Child::Stored(id) => payload_relaxed(&self.load(*id)?.payload),
            Child::Fresh(node) => payload_relaxed(&node.payload),
        }
    }

    /// A fresh inner node of height `h` holding the children, its balance
    /// and sizes computed as `list` computes them.
    fn new_inner(&self, children: Vec<Child>, h: usize) -> Result<Node, StoreError> {
        let mut balanced = true;
        let mut total = 0;
        let mut sizes = Vec::with_capacity(children.len());
        for (j, child) in children.iter().enumerate() {
            let size = self.child_size(child, h - 1)?;
            balanced &= !self.child_relaxed(child, h - 1)?
                && (j + 1 == children.len() || size == self.complete(h - 1));
            total += size;
            sizes.push(total);
        }
        let mut payload = vec![u8::from(!balanced)];
        if !balanced {
            for size in sizes {
                payload.extend_from_slice(&(size as u64).to_le_bytes());
            }
        }
        Ok(Node {
            kind: LIST_INNER,
            children,
            payload,
        })
    }

    /// The overlay of the list with `value` appended: the fresh path, the
    /// rest of the tree kept by id.
    pub fn push(&self, root: NodeId, value: &[u8]) -> Result<Node, StoreError> {
        let size = self.size();
        debug_assert_eq!(value.len(), size);
        let root = self.load(root)?;
        let (len, h) = list_parts(&root)?;
        if size == 0 {
            return Ok(Node {
                kind: LIST,
                children: Vec::new(),
                payload: list_payload(len + 1, 0),
            });
        }
        let Some(&tree) = root.header.children.first() else {
            let leaf = Node {
                kind: LIST_LEAF,
                children: Vec::new(),
                payload: value.to_vec(),
            };
            return Ok(Node {
                kind: LIST,
                children: vec![Child::Fresh(Box::new(leaf))],
                payload: list_payload(len + 1, 0),
            });
        };
        let (tree, h) = match self.push_node(tree, h, value)? {
            Push::Grown(t) => (t, h),
            Push::Split(new) => (
                self.new_inner(
                    vec![Child::Stored(tree), Child::Fresh(Box::new(new))],
                    h + 1,
                )?,
                h + 1,
            ),
        };
        Ok(Node {
            kind: LIST,
            children: vec![Child::Fresh(Box::new(tree))],
            payload: list_payload(len + 1, h),
        })
    }

    /// Appends along the stored subtree's right edge, path-copying, as
    /// `list`'s push does in place.
    fn push_node(&self, id: NodeId, h: usize, value: &[u8]) -> Result<Push, StoreError> {
        let node = self.load(id)?;
        if h == 0 {
            if self.leaf_slots(&node)? == list::leaf_width(self.element) {
                return Ok(Push::Split(Node {
                    kind: LIST_LEAF,
                    children: Vec::new(),
                    payload: value.to_vec(),
                }));
            }
            let mut payload = node.payload.to_vec();
            payload.extend_from_slice(value);
            return Ok(Push::Grown(Node {
                kind: LIST_LEAF,
                children: Vec::new(),
                payload,
            }));
        }
        if node.header.kind != LIST_INNER {
            return Err(corrupt("a leaf where the height says an inner node"));
        }
        let n = node.header.children.len();
        if n == 0 {
            return Err(corrupt("an inner node without children"));
        }
        let relaxed = payload_relaxed(&node.payload)?;
        let mut children: Vec<Child> = node
            .header
            .children
            .iter()
            .copied()
            .map(Child::Stored)
            .collect();
        let mut payload = node.payload.to_vec();
        match self.push_node(node.header.children[n - 1], h - 1, value)? {
            Push::Grown(grown) => {
                children[n - 1] = Child::Fresh(Box::new(grown));
                if relaxed {
                    let last = payload_cumulative(&payload, n - 1)? + 1;
                    payload[1 + 8 * (n - 1)..9 + 8 * (n - 1)]
                        .copy_from_slice(&(last as u64).to_le_bytes());
                }
            }
            Push::Split(new) => {
                if n == WIDTH {
                    return Ok(Push::Split(
                        self.new_inner(vec![Child::Fresh(Box::new(new))], h)?,
                    ));
                }
                children.push(Child::Fresh(Box::new(new)));
                if relaxed {
                    // In a balanced node a full last child was complete,
                    // so the node stays balanced.
                    let last = payload_cumulative(&payload, n - 1)? + 1;
                    payload.extend_from_slice(&(last as u64).to_le_bytes());
                }
            }
        }
        Ok(Push::Grown(Node {
            kind: LIST_INNER,
            children,
            payload,
        }))
    }

    /// The overlay of the list with element `i` replaced by `value`.
    pub fn set(&self, root: NodeId, i: usize, value: &[u8]) -> Result<Node, StoreError> {
        let size = self.size();
        debug_assert_eq!(value.len(), size);
        let root = self.load(root)?;
        let (len, h) = list_parts(&root)?;
        if i >= len {
            die("a durable list element set outside the list");
        }
        if size == 0 {
            return Ok(Node {
                kind: LIST,
                children: root
                    .header
                    .children
                    .iter()
                    .copied()
                    .map(Child::Stored)
                    .collect(),
                payload: root.payload.to_vec(),
            });
        }
        let tree = *root
            .header
            .children
            .first()
            .ok_or_else(|| corrupt("elements without a tree"))?;
        let tree = self.set_node(tree, h, i, value)?;
        Ok(Node {
            kind: LIST,
            children: vec![Child::Fresh(Box::new(tree))],
            payload: list_payload(len, h),
        })
    }

    /// Path-copies down to the element's slot.
    fn set_node(&self, id: NodeId, h: usize, i: usize, value: &[u8]) -> Result<Node, StoreError> {
        let size = self.size();
        let node = self.load(id)?;
        if h == 0 {
            let n = self.leaf_slots(&node)?;
            if i >= n {
                return Err(corrupt("an element past its leaf"));
            }
            let mut payload = node.payload.to_vec();
            payload[size * i..size * (i + 1)].copy_from_slice(value);
            return Ok(Node {
                kind: LIST_LEAF,
                children: Vec::new(),
                payload,
            });
        }
        if node.header.kind != LIST_INNER {
            return Err(corrupt("a leaf where the height says an inner node"));
        }
        let (j, rest) = self.find(&node, h, i)?;
        let child = *node
            .header
            .children
            .get(j)
            .ok_or_else(|| corrupt("an index past its node's children"))?;
        let child = self.set_node(child, h - 1, rest, value)?;
        let mut children: Vec<Child> = node
            .header
            .children
            .iter()
            .copied()
            .map(Child::Stored)
            .collect();
        children[j] = Child::Fresh(Box::new(child));
        Ok(Node {
            kind: LIST_INNER,
            children,
            payload: node.payload.to_vec(),
        })
    }
}

/// The overlay of a whole heap list, every node fresh: its first commit.
///
/// # Safety
///
/// `ptr` points at a live list of elements of `element`.
pub unsafe fn encode_list(element: &ElementLayout, ptr: *mut u8) -> Node {
    if !element.counted.is_empty() {
        die("a durable list of elements with references is not storable yet (Plan §11.11.6)");
    }
    // SAFETY: as the caller promises.
    let (len, height, tree) = unsafe { list::parts::list(ptr) };
    let mut children = Vec::new();
    if !tree.is_null() {
        // SAFETY: the tree is the list's, of that height.
        children.push(Child::Fresh(Box::new(unsafe {
            encode_tree(element, tree, height)
        })));
    }
    Node {
        kind: LIST,
        children,
        payload: list_payload(len, height),
    }
}

/// A heap subtree as a fresh overlay node.
///
/// # Safety
///
/// `node` points at a live node of height `h` of a list of `element`.
unsafe fn encode_tree(element: &ElementLayout, node: *mut u8, h: usize) -> Node {
    // SAFETY: as the caller promises.
    unsafe {
        let n = list::parts::slots(node);
        if h == 0 {
            return Node {
                kind: LIST_LEAF,
                children: Vec::new(),
                payload: list::parts::elements(node, element.size as usize, n).to_vec(),
            };
        }
        let relaxed = list::parts::relaxed(node, h);
        let mut payload = vec![u8::from(relaxed)];
        if relaxed {
            for j in 0..n {
                payload.extend_from_slice(&(list::parts::cumulative(node, j) as u64).to_le_bytes());
            }
        }
        let children = (0..n)
            .map(|j| {
                Child::Fresh(Box::new(encode_tree(
                    element,
                    list::parts::child(node, j),
                    h - 1,
                )))
            })
            .collect();
        Node {
            kind: LIST_INNER,
            children,
            payload,
        }
    }
}

/// The whole stored list under `root` as a heap list, for a `use` of the
/// value; faulting per read replaces this where only parts are read.
///
/// # Safety
///
/// `index` is the type of a list of `list.element`'s elements in `types`.
pub unsafe fn fault_list(
    heap: &mut Heap,
    types: &Types,
    index: u32,
    list: &DurList,
    root: NodeId,
) -> Result<*mut u8, StoreError> {
    let size = list.size();
    let len = list.len(root)?;
    let mut out = list::empty(heap, index);
    let mut words = vec![0u64; size.div_ceil(8).max(1)];
    for i in 0..len {
        if size > 0 {
            // SAFETY: the words cover `size` bytes.
            let buf =
                unsafe { std::slice::from_raw_parts_mut(words.as_mut_ptr().cast::<u8>(), size) };
            list.get(root, i, buf)?;
        }
        // SAFETY: as the caller promises, and the value holds no
        // references.
        out = unsafe { list::push(heap, types, out, &words) };
    }
    Ok(out)
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;

    use crag_abi::TypeDescriptor;
    use crag_dur::CommitOutcome;
    use crag_dur::fault::{Fault, FaultStore};
    use crag_dur::mem::MemStore;

    use crate::rc::drop_box;
    use crate::testing::Rng;

    const INTS: u32 = 40;
    const SHORTS: u32 = 41;

    fn types() -> Types {
        let list = |element: ElementLayout| TypeDescriptor::List {
            cell: element.clone(),
            ref_cell: element.clone(),
            element,
        };
        Types::new([
            (INTS, list(ElementLayout::of_words(1, vec![]))),
            (
                SHORTS,
                list(ElementLayout {
                    size: 2,
                    align: 2,
                    counted: vec![],
                }),
            ),
        ])
    }

    fn element(types: &Types, index: u32) -> &ElementLayout {
        match types.get(index).unwrap() {
            TypeDescriptor::List { element, .. } => element,
            _ => unreachable!("a list"),
        }
    }

    fn key() -> HeadKey {
        HeadKey(b"slot".to_vec())
    }

    /// Commits the overlay as the slot's new value; the root and version.
    fn commit(store: &Arc<dyn NodeStore>, root: &Node, read: u64) -> (NodeId, u64) {
        let (id, batch) = overlay_batch(&**store, root, key(), DescriptorId(0), read);
        match store.commit(batch).unwrap() {
            CommitOutcome::Committed { version } => (id, version),
            CommitOutcome::Conflict { .. } => panic!("an unexpected conflict"),
        }
    }

    /// The bytes an element of a list of type `index` takes for `v`.
    fn value(index: u32, v: u64) -> Vec<u8> {
        match index {
            SHORTS => (v as u16).to_le_bytes().to_vec(),
            _ => v.to_le_bytes().to_vec(),
        }
    }

    /// Checks every element and the length against the model.
    fn check(list: &DurList, root: NodeId, index: u32, model: &[u64]) {
        assert_eq!(list.len(root).unwrap(), model.len());
        let mut buf = vec![0u8; list.size()];
        for (i, v) in model.iter().enumerate() {
            list.get(root, i, &mut buf).unwrap();
            assert_eq!(buf, value(index, *v), "element {i}");
        }
    }

    /// A heap list of the model's elements.
    unsafe fn heap_list(heap: &mut Heap, types: &Types, index: u32, model: &[u64]) -> *mut u8 {
        let mut list = list::empty(heap, index);
        for &v in model {
            // SAFETY: the list is live and owned here.
            list = unsafe { list::push(heap, types, list, &[v]) };
        }
        list
    }

    fn round_trip(index: u32, count: u64) {
        let mut heap = Heap::new();
        let types = types();
        let store: Arc<dyn NodeStore> = Arc::new(MemStore::new());
        let cache = NodeCache::new(1 << 20);
        let model: Vec<u64> = (0..count)
            .map(|v| if index == SHORTS { v & 0xffff } else { v })
            .collect();
        // SAFETY: the lists are live and owned here.
        unsafe {
            let list = heap_list(&mut heap, &types, index, &model);
            let overlay = encode_list(element(&types, index), list);
            assert_eq!(
                collect_overlay(&overlay).len() as u64,
                overlay.fresh_count()
            );
            let (root, _) = commit(&store, &overlay, 0);
            let dur = DurList {
                store: &*store,
                cache: &cache,
                element: element(&types, index),
            };
            check(&dur, root, index, &model);
            let back = fault_list(&mut heap, &types, index, &dur, root).unwrap();
            for (i, v) in model.iter().enumerate() {
                let bytes =
                    std::slice::from_raw_parts(list::get(&types, back, i).cast::<u8>(), dur.size());
                assert_eq!(bytes, value(index, *v), "element {i}");
            }
            drop_box(&mut heap, &types, list);
            drop_box(&mut heap, &types, back);
        }
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn a_heap_list_round_trips_through_the_store() {
        // Heights 0 to 2: a leaf of 64 words fills at 64, a tree of
        // height 2 past 2048.
        for count in [0, 1, 64, 65, 3000] {
            round_trip(INTS, count);
        }
        // Short elements pack 256 to a leaf.
        round_trip(SHORTS, 2000);
    }

    #[test]
    fn durable_updates_path_copy_and_read_back() {
        let mut heap = Heap::new();
        let types = types();
        let store: Arc<dyn NodeStore> = Arc::new(MemStore::new());
        let cache = NodeCache::new(1 << 18);
        let dur = DurList {
            store: &*store,
            cache: &cache,
            element: element(&types, INTS),
        };
        let mut model: Vec<u64> = (0..3000).collect();
        // SAFETY: the list is live and owned here.
        let (mut root, mut version) = unsafe {
            let list = heap_list(&mut heap, &types, INTS, &model);
            let overlay = encode_list(dur.element, list);
            drop_box(&mut heap, &types, list);
            commit(&store, &overlay, 0)
        };
        let mut rng = Rng(11);
        let mut next = 3000;
        for step in 0..400 {
            next += 1;
            let overlay = if rng.below(2) == 0 {
                model.push(next);
                dur.push(root, &value(INTS, next)).unwrap()
            } else {
                let i = rng.below(model.len());
                model[i] = next;
                dur.set(root, i, &value(INTS, next)).unwrap()
            };
            // The overlay is the path alone: the root node, one node per
            // level, and at most one new sibling.
            let (_, height) = list_parts(&dur.load(root).unwrap()).unwrap();
            assert!(
                collect_overlay(&overlay).len() <= height + 3,
                "an update wrote {} nodes into a tree of height {height}",
                collect_overlay(&overlay).len()
            );
            (root, version) = commit(&store, &overlay, version);
            if step % 50 == 0 {
                check(&dur, root, INTS, &model);
            }
        }
        check(&dur, root, INTS, &model);
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn relaxed_trees_round_trip_and_update() {
        let mut heap = Heap::new();
        let types = types();
        let store: Arc<dyn NodeStore> = Arc::new(MemStore::new());
        let cache = NodeCache::new(1 << 18);
        let dur = DurList {
            store: &*store,
            cache: &cache,
            element: element(&types, INTS),
        };
        let mut rng = Rng(13);
        let mut model: Vec<u64> = Vec::new();
        // SAFETY: the lists are live and owned here.
        let (mut root, mut version) = unsafe {
            // Joining many small lists leaves relaxed nodes.
            let mut whole = list::empty(&mut heap, INTS);
            for _ in 0..200 {
                let mut part = list::empty(&mut heap, INTS);
                for _ in 0..1 + rng.below(40) {
                    let v = model.len() as u64;
                    part = list::push(&mut heap, &types, part, &[v]);
                    model.push(v);
                }
                let joined = list::concat(&mut heap, &types, whole, part);
                drop_box(&mut heap, &types, whole);
                drop_box(&mut heap, &types, part);
                whole = joined;
            }
            let overlay = encode_list(dur.element, whole);
            drop_box(&mut heap, &types, whole);
            commit(&store, &overlay, 0)
        };
        check(&dur, root, INTS, &model);
        let mut next = 1 << 32;
        for _ in 0..200 {
            next += 1;
            let overlay = if rng.below(2) == 0 {
                model.push(next);
                dur.push(root, &value(INTS, next)).unwrap()
            } else {
                let i = rng.below(model.len());
                model[i] = next;
                dur.set(root, i, &value(INTS, next)).unwrap()
            };
            (root, version) = commit(&store, &overlay, version);
        }
        check(&dur, root, INTS, &model);
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn a_stale_read_version_conflicts() {
        let types = types();
        let store: Arc<dyn NodeStore> = Arc::new(MemStore::new());
        let cache = NodeCache::new(1 << 16);
        let dur = DurList {
            store: &*store,
            cache: &cache,
            element: element(&types, INTS),
        };
        let mut heap = Heap::new();
        // SAFETY: the list is live and owned here.
        let (root, version) = unsafe {
            let list = heap_list(&mut heap, &types, INTS, &[1, 2, 3]);
            let overlay = encode_list(dur.element, list);
            drop_box(&mut heap, &types, list);
            commit(&store, &overlay, 0)
        };
        let one = dur.push(root, &value(INTS, 4)).unwrap();
        let two = dur.push(root, &value(INTS, 5)).unwrap();
        commit(&store, &one, version);
        let (_, batch) = overlay_batch(&*store, &two, key(), DescriptorId(0), version);
        assert!(matches!(
            store.commit(batch).unwrap(),
            CommitOutcome::Conflict { .. }
        ));
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn pinned_roots_survive_the_sweep() {
        let types = types();
        let store: Arc<dyn NodeStore> = Arc::new(MemStore::new());
        let cache = NodeCache::new(1 << 18);
        let dur = DurList {
            store: &*store,
            cache: &cache,
            element: element(&types, INTS),
        };
        let mut heap = Heap::new();
        let model: Vec<u64> = (0..1000).collect();
        // SAFETY: the list is live and owned here.
        let (old, version) = unsafe {
            let list = heap_list(&mut heap, &types, INTS, &model);
            let overlay = encode_list(dur.element, list);
            drop_box(&mut heap, &types, list);
            commit(&store, &overlay, 0)
        };
        let snapshot = DurRoot::new(store.clone(), old, version);
        let overlay = dur.set(old, 0, &value(INTS, 7777)).unwrap();
        let (new, _) = commit(&store, &overlay, version);

        // The old root lost its head, but the pin holds it and so its
        // whole version.
        assert_eq!(sweep_free_list(&store, 10_000).unwrap(), 0);
        let mut buf = [0u8; 8];
        dur.get(old, 0, &mut buf).unwrap();
        assert_eq!(buf, value(INTS, 0).as_slice());
        dur.get(new, 0, &mut buf).unwrap();
        assert_eq!(buf, value(INTS, 7777).as_slice());

        // Unpinned, the sweep frees the old version: exactly the path the
        // update copied, since everything else is shared with the new one.
        let before = store.stats().unwrap().nodes;
        drop(snapshot);
        let freed = sweep_free_list(&store, 10_000).unwrap();
        let stats = store.stats().unwrap();
        assert_eq!(stats.nodes, before - freed as u64);
        assert_eq!(stats.free_list, 0);
        assert_eq!(freed, collect_overlay(&overlay).len());
        check(&dur, new, INTS, &{
            let mut m = model;
            m[0] = 7777;
            m
        });
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn the_cache_stays_bounded_and_reloads() {
        let types = types();
        let store: Arc<dyn NodeStore> = Arc::new(MemStore::new());
        // Far smaller than the list, so reads evict and fault again.
        let cache = NodeCache::new(4096);
        let dur = DurList {
            store: &*store,
            cache: &cache,
            element: element(&types, INTS),
        };
        let mut heap = Heap::new();
        let model: Vec<u64> = (0..5000).collect();
        // SAFETY: the list is live and owned here.
        let root = unsafe {
            let list = heap_list(&mut heap, &types, INTS, &model);
            let overlay = encode_list(dur.element, list);
            drop_box(&mut heap, &types, list);
            commit(&store, &overlay, 0).0
        };
        check(&dur, root, INTS, &model);
        // Each shard may keep the one node a load has in hand past its
        // slice of the budget, and no more: far below the list's bytes.
        let node = 64 + 8 * WIDTH + 512;
        assert!(
            cache.bytes() <= 4096 + SHARDS * node,
            "the cache holds {} bytes",
            cache.bytes()
        );
        assert_eq!(heap.live_blocks(), 0);
    }

    #[test]
    fn a_failed_get_surfaces_the_fault() {
        let types = types();
        let backend = Arc::new(FaultStore::new(MemStore::new()));
        let store: Arc<dyn NodeStore> = backend.clone();
        let cache = NodeCache::new(1 << 16);
        let dur = DurList {
            store: &*store,
            cache: &cache,
            element: element(&types, INTS),
        };
        let mut heap = Heap::new();
        // SAFETY: the list is live and owned here.
        let root = unsafe {
            let list = heap_list(&mut heap, &types, INTS, &[1, 2, 3]);
            let overlay = encode_list(dur.element, list);
            drop_box(&mut heap, &types, list);
            commit(&store, &overlay, 0).0
        };
        // A fresh cache must fault the root in, and the store fails.
        let empty = NodeCache::new(1 << 16);
        let failing = DurList {
            store: &*store,
            cache: &empty,
            element: element(&types, INTS),
        };
        let fault = || StoreError::StoreFault("planned".into());
        backend.plan(Fault::Get(fault()));
        assert_eq!(failing.len(root).unwrap_err(), fault());
        // The failure was not cached: the next read works.
        assert_eq!(failing.len(root).unwrap(), 3);
        assert_eq!(heap.live_blocks(), 0);
    }
}
