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

//! The in-memory backend: `Store.memory()` (Specification §21.3), the
//! same semantics as a file store without a file, for tests. It is also
//! the reference the backends are compared against (Plan §11.11.11).

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ops::Deref;
use std::sync::Mutex;
use std::sync::atomic::{AtomicU64, Ordering};

use crate::{
    CommitBatch, CommitOutcome, DescriptorId, Head, HeadKey, NodeId, NodeRef, NodeStore,
    StoreError, StoreStats, children_of,
};

/// A store backed by tables in memory.
pub struct MemStore {
    inner: Mutex<Inner>,
    next_node: AtomicU64,
    next_descriptor: AtomicU64,
}

#[derive(Default)]
struct Inner {
    nodes: BTreeMap<u64, Shared>,
    heads: BTreeMap<Vec<u8>, Head>,
    descriptors: BTreeMap<u64, Vec<u8>>,
    /// How many stored parents reference each node; a head counts as a
    /// parent of its root.
    counts: HashMap<u64, u32>,
    /// The free list: nodes whose count reached zero.
    free: BTreeSet<u64>,
    /// The last commit sequence number.
    version: u64,
}

/// A node's bytes, shared with readers that still hold them.
#[derive(Clone)]
struct Shared(std::sync::Arc<Vec<u8>>);

impl Deref for Shared {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0
    }
}

impl MemStore {
    pub fn new() -> MemStore {
        MemStore {
            inner: Mutex::new(Inner::default()),
            // Id zero is never handed out, so it can mean "none".
            next_node: AtomicU64::new(1),
            next_descriptor: AtomicU64::new(1),
        }
    }
}

impl Default for MemStore {
    fn default() -> MemStore {
        MemStore::new()
    }
}

impl Inner {
    fn bump(&mut self, id: NodeId) {
        *self.counts.entry(id.0).or_insert(0) += 1;
        self.free.remove(&id.0);
    }

    fn drop_count(&mut self, id: NodeId) -> Result<(), StoreError> {
        let count = self
            .counts
            .get_mut(&id.0)
            .filter(|c| **c > 0)
            .ok_or_else(|| StoreError::StoreFault(format!("node {} is not referenced", id.0)))?;
        *count -= 1;
        if *count == 0 {
            self.free.insert(id.0);
        }
        Ok(())
    }

    /// Deletes nodes of count zero; their children's counts drop, and a
    /// child reaching zero takes their place on the free list.
    fn free_nodes(&mut self, ids: &[NodeId]) -> Result<(), StoreError> {
        for id in ids {
            if self.counts.get(&id.0).copied().unwrap_or(0) != 0 {
                return Err(StoreError::StoreFault(format!(
                    "node {} is freed while referenced",
                    id.0
                )));
            }
            let node = self
                .nodes
                .remove(&id.0)
                .ok_or_else(|| StoreError::StoreFault(format!("node {} is freed twice", id.0)))?;
            self.counts.remove(&id.0);
            self.free.remove(&id.0);
            for child in children_of(&node)? {
                self.drop_count(child)?;
            }
        }
        Ok(())
    }
}

impl NodeStore for MemStore {
    fn commit(&self, batch: CommitBatch) -> Result<CommitOutcome, StoreError> {
        let mut inner = self.inner.lock().expect("a poisoned store");
        // Validate every head first: on a conflict nothing is written.
        for head in &batch.heads {
            let version = inner.heads.get(&head.key.0).map_or(0, |h| h.version);
            if version != head.read {
                return Ok(CommitOutcome::Conflict {
                    key: head.key.clone(),
                });
            }
        }
        let version = inner.version + 1;
        for (id, descriptor) in &batch.descriptors {
            inner.descriptors.insert(id.0, descriptor.clone());
        }
        for (id, bytes) in &batch.nodes {
            let children = children_of(bytes)?;
            if inner
                .nodes
                .insert(id.0, Shared(bytes.clone().into()))
                .is_some()
            {
                return Err(StoreError::StoreFault(format!(
                    "node {} is stored twice",
                    id.0
                )));
            }
            for child in children {
                inner.bump(child);
            }
        }
        for head in &batch.heads {
            inner.bump(head.root);
            let new = Head {
                root: head.root,
                version,
                descriptor: head.descriptor,
            };
            if let Some(old) = inner.heads.insert(head.key.0.clone(), new) {
                inner.drop_count(old.root)?;
            }
        }
        inner.free_nodes(&batch.frees)?;
        inner.version = version;
        Ok(CommitOutcome::Committed { version })
    }

    fn get(&self, id: NodeId) -> Result<NodeRef<'_>, StoreError> {
        let inner = self.inner.lock().expect("a poisoned store");
        let node = inner
            .nodes
            .get(&id.0)
            .cloned()
            .ok_or_else(|| StoreError::StoreFault(format!("node {} is not stored", id.0)))?;
        Ok(NodeRef::new(Box::new(node)))
    }

    fn head(&self, key: &HeadKey) -> Result<Option<Head>, StoreError> {
        let inner = self.inner.lock().expect("a poisoned store");
        Ok(inner.heads.get(&key.0).copied())
    }

    fn heads(&self) -> Result<Vec<(HeadKey, Head)>, StoreError> {
        let inner = self.inner.lock().expect("a poisoned store");
        Ok(inner
            .heads
            .iter()
            .map(|(key, head)| (HeadKey(key.clone()), *head))
            .collect())
    }

    fn descriptor(&self, id: DescriptorId) -> Result<Vec<u8>, StoreError> {
        let inner = self.inner.lock().expect("a poisoned store");
        inner
            .descriptors
            .get(&id.0)
            .cloned()
            .ok_or_else(|| StoreError::StoreFault(format!("descriptor {} is not stored", id.0)))
    }

    fn free(&self, ids: &[NodeId]) -> Result<(), StoreError> {
        let mut inner = self.inner.lock().expect("a poisoned store");
        inner.free_nodes(ids)
    }

    fn freeable(&self, limit: usize) -> Result<Vec<NodeId>, StoreError> {
        let inner = self.inner.lock().expect("a poisoned store");
        Ok(inner
            .free
            .iter()
            .take(limit)
            .map(|&id| NodeId(id))
            .collect())
    }

    fn allocate(&self, count: u64) -> NodeId {
        NodeId(self.next_node.fetch_add(count, Ordering::Relaxed))
    }

    fn allocate_descriptor(&self) -> DescriptorId {
        DescriptorId(self.next_descriptor.fetch_add(1, Ordering::Relaxed))
    }

    fn sync(&self) -> Result<(), StoreError> {
        Ok(())
    }

    fn stats(&self) -> Result<StoreStats, StoreError> {
        let inner = self.inner.lock().expect("a poisoned store");
        Ok(StoreStats {
            map_size: 0,
            disk: 0,
            nodes: inner.nodes.len() as u64,
            free_list: inner.free.len() as u64,
        })
    }
}
