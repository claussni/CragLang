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

//! Durable stores (Plan §11.11.1, Specification §21.9): the storage facade
//! the runtime commits through, and its backends.
//!
//! The runtime never calls a storage engine directly. It sees immutable
//! nodes under 64-bit ids and a small table of slot heads, through
//! [`NodeStore`]: commit new nodes together with moved heads, get a node,
//! free nodes. Everything above the facade is engine-independent, so the
//! first backend ([`lmdb`], Plan §11.11.2) can be replaced by an own
//! engine without touching the language runtime. [`mem`] is the backend of
//! `Store.memory()`, the same semantics without a file, and [`fault`]
//! wraps any backend to inject failures (Plan §11.11.11).
//!
//! The facade owns the node's wire header: each stored node begins with
//! its type descriptor, a kind byte the runtime defines, and the ids of
//! its children, followed by an opaque payload. The header lets a backend
//! keep the parent counts of reclamation (Plan §11.11.9) by itself: a
//! commit bumps the count of every child a new node names and of every
//! root a head moves to, and a head move or a `free` that drops a count
//! to zero puts the node on the durable free list, which the runtime
//! sweeps with [`NodeStore::freeable`] and [`NodeStore::free`].
//!
//! Optimistic commits validate against a head's `version`. Every commit
//! takes the store's next commit sequence number as the version of all
//! heads it moves; a batch names, beside each head, the version it read,
//! with zero for a head it expects absent. A mismatch is a
//! [`CommitOutcome::Conflict`], not an error: the caller reruns its block.

use std::fmt;
use std::ops::Deref;

pub mod fault;
pub mod lmdb;
pub mod mem;

/// The version of the storage format, kept in the store's meta table. A
/// store whose format is newer than the running toolchain's refuses to
/// open.
pub const FORMAT: u64 = 1;

/// The id of a stored node: monotonically increasing per store, never
/// reused while any reference to it exists.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct NodeId(pub u64);

/// The id of a stored type descriptor (Plan §11.11.7).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct DescriptorId(pub u64);

/// The encoded key of a slot, type identity included (Plan §11.11.6).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct HeadKey(pub Vec<u8>);

/// A slot's current state: the root of its value's node tree, the commit
/// sequence number that moved it last, and its stored type descriptor.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Head {
    pub root: NodeId,
    pub version: u64,
    pub descriptor: DescriptorId,
}

/// One head a commit moves: the key, the new root and descriptor, and the
/// version the transaction read, zero for a head it expects absent.
#[derive(Clone, Debug)]
pub struct HeadMove {
    pub key: HeadKey,
    pub root: NodeId,
    pub descriptor: DescriptorId,
    pub read: u64,
}

/// What one storage transaction writes: the path-copied nodes, the heads
/// it moves with the versions it read, descriptors met for the first
/// time, and nodes whose reclamation rides along.
#[derive(Clone, Default, Debug)]
pub struct CommitBatch {
    pub nodes: Vec<(NodeId, Vec<u8>)>,
    pub heads: Vec<HeadMove>,
    pub descriptors: Vec<(DescriptorId, Vec<u8>)>,
    pub frees: Vec<NodeId>,
}

/// How a commit ended. A conflict is not an error: the caller reruns.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum CommitOutcome {
    Committed { version: u64 },
    Conflict { key: HeadKey },
}

/// What `stats` reports of a store's file (Specification §21.3); the
/// language-level `stats` adds the pinned versions, which the runtime
/// holds.
#[derive(Clone, Copy, Default, Debug)]
pub struct StoreStats {
    /// The reserved size of the memory map, zero for the memory backend.
    pub map_size: u64,
    /// The bytes the file takes on disk.
    pub disk: u64,
    /// The stored nodes.
    pub nodes: u64,
    /// The nodes on the durable free list.
    pub free_list: u64,
}

/// The runtime mirror of the language's `StoreError` members
/// (Specification §21.7).
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum StoreError {
    AlreadyOpen,
    SchemaMismatch { stored: String, declared: String },
    NoMigration { stored: String },
    KeyTypeClash,
    MixedStores,
    StoreFull,
    StoreFault(String),
    ReadOnly,
}

impl fmt::Display for StoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            StoreError::AlreadyOpen => write!(f, "the store file is already open"),
            StoreError::SchemaMismatch { stored, declared } => {
                write!(f, "the slot stores a {stored}, not a {declared}")
            }
            StoreError::NoMigration { stored } => {
                write!(
                    f,
                    "no migration reaches the declared type from the stored {stored}"
                )
            }
            StoreError::KeyTypeClash => write!(f, "the key is bound with another value type"),
            StoreError::MixedStores => write!(f, "the block touches two stores"),
            StoreError::StoreFull => write!(f, "the store's map size is exhausted"),
            StoreError::StoreFault(message) => write!(f, "storage failed: {message}"),
            StoreError::ReadOnly => write!(f, "the store is read-only after a failed sync"),
        }
    }
}

impl std::error::Error for StoreError {}

/// When a commit is on disk (Specification §21.3): `Full` syncs data and
/// meta page, `Flush` syncs data only, `Buffered` leaves syncing to the
/// operating system until `sync` is called.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Durability {
    Full,
    Flush,
    Buffered,
}

/// The bytes of a stored node, borrowed from the backend: from the
/// memory map under a read transaction, or shared with an in-memory
/// table. Dropping it ends the borrow.
pub struct NodeRef<'s>(Box<dyn Deref<Target = [u8]> + 's>);

impl<'s> NodeRef<'s> {
    pub fn new(bytes: Box<dyn Deref<Target = [u8]> + 's>) -> NodeRef<'s> {
        NodeRef(bytes)
    }
}

impl Deref for NodeRef<'_> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0
    }
}

/// The storage facade (Plan §11.11.1). Everything the language runtime
/// wants from an engine; an implementation serializes its writes itself
/// (the runtime drives it from one writer thread per store, Plan
/// §11.11.4, but tests call it from anywhere).
pub trait NodeStore: Send + Sync {
    /// Writes the batch in one storage transaction: validates each head's
    /// read version, stores the nodes, moves the heads, keeps the parent
    /// counts, and frees `batch.frees`. On a conflict nothing is written.
    fn commit(&self, batch: CommitBatch) -> Result<CommitOutcome, StoreError>;

    /// The bytes of a stored node.
    fn get(&self, id: NodeId) -> Result<NodeRef<'_>, StoreError>;

    /// The head of a slot, none when the key holds nothing.
    fn head(&self, key: &HeadKey) -> Result<Option<Head>, StoreError>;

    /// Every head: for `slots`, `:store` and the verification sweeps.
    fn heads(&self) -> Result<Vec<(HeadKey, Head)>, StoreError>;

    /// The stored bytes of a type descriptor.
    fn descriptor(&self, id: DescriptorId) -> Result<Vec<u8>, StoreError>;

    /// Deletes nodes whose count is zero and no pin holds: each node's
    /// record leaves the store, the counts of its children drop, and a
    /// child reaching zero goes onto the free list in its place.
    fn free(&self, ids: &[NodeId]) -> Result<(), StoreError>;

    /// Up to `limit` nodes of the durable free list, for the reclamation
    /// sweep (Plan §11.11.9).
    fn freeable(&self, limit: usize) -> Result<Vec<NodeId>, StoreError>;

    /// Takes `count` fresh node ids and returns the first: ids are handed
    /// out above every id the store ever stored, also after a restart.
    fn allocate(&self, count: u64) -> NodeId;

    /// Takes a fresh descriptor id, above every stored one.
    fn allocate_descriptor(&self) -> DescriptorId;

    /// Forces a sync, for `durability: Buffered`. After a failed sync the
    /// store is read-only: every later commit returns `ReadOnly`.
    fn sync(&self) -> Result<(), StoreError>;

    fn stats(&self) -> Result<StoreStats, StoreError>;
}

/// The fixed part of a stored node's bytes: its descriptor, a kind byte
/// the runtime gives meaning, and its children's ids. The payload behind
/// it is opaque to storage.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct NodeHeader {
    pub descriptor: DescriptorId,
    pub kind: u8,
    pub children: Vec<NodeId>,
}

/// Bytes of the header: descriptor, kind, three reserved zero bytes, the
/// child count, then the children, all little-endian.
const HEADER: usize = 8 + 1 + 3 + 4;

/// Encodes a node for [`CommitBatch::nodes`].
pub fn encode_node(header: &NodeHeader, payload: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(HEADER + 8 * header.children.len() + payload.len());
    out.extend_from_slice(&header.descriptor.0.to_le_bytes());
    out.push(header.kind);
    out.extend_from_slice(&[0; 3]);
    let count = u32::try_from(header.children.len()).expect("more children than a node can hold");
    out.extend_from_slice(&count.to_le_bytes());
    for child in &header.children {
        out.extend_from_slice(&child.0.to_le_bytes());
    }
    out.extend_from_slice(payload);
    out
}

/// Reads a node's header back, with the payload behind it.
pub fn decode_node(bytes: &[u8]) -> Result<(NodeHeader, &[u8]), StoreError> {
    let corrupt = || StoreError::StoreFault("a stored node is shorter than its header".into());
    let fixed = bytes.get(..HEADER).ok_or_else(corrupt)?;
    let descriptor = DescriptorId(u64::from_le_bytes(fixed[..8].try_into().expect("sized")));
    let kind = fixed[8];
    let count = u32::from_le_bytes(fixed[12..16].try_into().expect("sized")) as usize;
    let rest = bytes.get(HEADER..).ok_or_else(corrupt)?;
    if rest.len() < 8 * count {
        return Err(corrupt());
    }
    let children = rest[..8 * count]
        .as_chunks::<8>()
        .0
        .iter()
        .map(|c| NodeId(u64::from_le_bytes(*c)))
        .collect();
    Ok((
        NodeHeader {
            descriptor,
            kind,
            children,
        },
        &rest[8 * count..],
    ))
}

/// The children of an encoded node, for the backends' parent counts.
pub fn children_of(bytes: &[u8]) -> Result<Vec<NodeId>, StoreError> {
    Ok(decode_node(bytes)?.0.children)
}
