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

//! Fault injection (Plan §11.11.1, §11.11.11): a wrapper over any backend
//! that fails on command, so tests see every failure surface as the
//! specified `StoreError` or signal.

use std::collections::VecDeque;
use std::sync::Mutex;

use crate::{
    CommitBatch, CommitOutcome, DescriptorId, Head, HeadKey, NodeId, NodeRef, NodeStore,
    StoreError, StoreStats,
};

/// What the next matching operation does.
#[derive(Clone, Debug)]
pub enum Fault {
    /// The next commit fails with this error; nothing is written.
    Commit(StoreError),
    /// The next commit writes its nodes but loses its head moves and
    /// frees, as a tear across the batch, and reports the error.
    TornCommit(StoreError),
    /// The next sync fails with this error.
    Sync(StoreError),
    /// The next get fails with this error.
    Get(StoreError),
}

/// A store that fails as planned, in the order the faults were planned.
pub struct FaultStore<S: NodeStore> {
    inner: S,
    plan: Mutex<VecDeque<Fault>>,
}

impl<S: NodeStore> FaultStore<S> {
    pub fn new(inner: S) -> FaultStore<S> {
        FaultStore {
            inner,
            plan: Mutex::new(VecDeque::new()),
        }
    }

    /// Plans the next fault; faults fire in planning order, each when the
    /// first operation of its kind reaches it.
    pub fn plan(&self, fault: Fault) {
        self.plan.lock().expect("a poisoned plan").push_back(fault);
    }

    /// Takes the front fault when `matches` picks it.
    fn take(&self, matches: impl Fn(&Fault) -> bool) -> Option<Fault> {
        let mut plan = self.plan.lock().expect("a poisoned plan");
        if plan.front().is_some_and(matches) {
            plan.pop_front()
        } else {
            None
        }
    }
}

impl<S: NodeStore> NodeStore for FaultStore<S> {
    fn commit(&self, batch: CommitBatch) -> Result<CommitOutcome, StoreError> {
        match self.take(|f| matches!(f, Fault::Commit(_) | Fault::TornCommit(_))) {
            Some(Fault::Commit(e)) => Err(e),
            Some(Fault::TornCommit(e)) => {
                let torn = CommitBatch {
                    nodes: batch.nodes,
                    ..CommitBatch::default()
                };
                self.inner.commit(torn)?;
                Err(e)
            }
            _ => self.inner.commit(batch),
        }
    }

    fn get(&self, id: NodeId) -> Result<NodeRef<'_>, StoreError> {
        match self.take(|f| matches!(f, Fault::Get(_))) {
            Some(Fault::Get(e)) => Err(e),
            _ => self.inner.get(id),
        }
    }

    fn head(&self, key: &HeadKey) -> Result<Option<Head>, StoreError> {
        self.inner.head(key)
    }

    fn heads(&self) -> Result<Vec<(HeadKey, Head)>, StoreError> {
        self.inner.heads()
    }

    fn descriptor(&self, id: DescriptorId) -> Result<Vec<u8>, StoreError> {
        self.inner.descriptor(id)
    }

    fn free(&self, ids: &[NodeId]) -> Result<(), StoreError> {
        self.inner.free(ids)
    }

    fn freeable(&self, limit: usize) -> Result<Vec<NodeId>, StoreError> {
        self.inner.freeable(limit)
    }

    fn allocate(&self, count: u64) -> NodeId {
        self.inner.allocate(count)
    }

    fn allocate_descriptor(&self) -> DescriptorId {
        self.inner.allocate_descriptor()
    }

    fn sync(&self) -> Result<(), StoreError> {
        match self.take(|f| matches!(f, Fault::Sync(_))) {
            Some(Fault::Sync(e)) => Err(e),
            _ => self.inner.sync(),
        }
    }

    fn stats(&self) -> Result<StoreStats, StoreError> {
        self.inner.stats()
    }
}
