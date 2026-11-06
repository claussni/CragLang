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

//! Durable cells and the writer of a store (Plan §11.11.3, §11.11.4,
//! Specification §21.6): the runtime side over the storage facade of
//! `crag-dur`.
//!
//! A [`DurCell`] is a ref cell whose latest committed value also lives
//! under a head of a store. The in-memory cell carries the value and the
//! TL2 version, as every ref does; beside it the cell remembers the
//! version of its durable head, which the backend validates. In one
//! process the two move together, under the cell's lock, so the head
//! check is a safety net, not the coordination: transactions already
//! serialize on the in-memory cell.
//!
//! A [`DurStore`] owns the writer thread of its store, which serializes
//! commits so a committing task never runs the backend itself. The
//! transaction side lives in `stm`: reads and writes of durable cells go
//! through the fiber's log, and a commit with durable writes hands its
//! batch to the writer and waits.
//!
//! First step: a slot's value is one node holding the cell's two words,
//! for values without references, as a counter. The structural encoding
//! of lists and maps, the node cache and roots faulted in on demand
//! (Plan §11.11.3) replace it slot by slot; the whole-value node stays
//! the fallback, as boxing is for layouts.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::mpsc::{Receiver, SyncSender, sync_channel};
use std::sync::{Arc, Mutex};

use crag_dur::{
    CommitBatch, CommitOutcome, DescriptorId, HeadKey, NodeHeader, NodeStore, StoreError,
    decode_node, encode_node,
};

use crate::refs::Cell;
use crate::stm::TxLog;

/// The kind byte of a node holding a cell's two words raw: a value
/// without references, little-endian.
pub(crate) const KIND_WORDS: u8 = 0;

/// A store the runtime commits to: the backend and its writer thread.
pub struct DurStore {
    nodes: Arc<dyn NodeStore>,
    /// Hands a commit to the writer; closed when the store drops.
    sender: Mutex<Option<SyncSender<Request>>>,
    writer: Mutex<Option<std::thread::JoinHandle<()>>>,
}

/// One commit waiting for the writer, and where its outcome goes.
struct Request {
    batch: CommitBatch,
    reply: SyncSender<Result<CommitOutcome, StoreError>>,
}

impl DurStore {
    /// Wraps a backend and starts its writer thread.
    pub fn new(nodes: Arc<dyn NodeStore>) -> Arc<DurStore> {
        let (sender, receiver) = sync_channel::<Request>(64);
        let backend = nodes.clone();
        let writer = std::thread::Builder::new()
            .name("crag-dur-writer".into())
            .spawn(move || writer_loop(&*backend, &receiver))
            .expect("no thread for the store's writer");
        Arc::new(DurStore {
            nodes,
            sender: Mutex::new(Some(sender)),
            writer: Mutex::new(Some(writer)),
        })
    }

    /// The backend, for what needs no writer: reads, stats, reclamation.
    pub fn nodes(&self) -> &Arc<dyn NodeStore> {
        &self.nodes
    }

    /// Opens the slot at `key` for a value of two raw words: the stored
    /// words, or `default` when the key holds nothing, which writes
    /// nothing until the first commit. One cell per key per process is
    /// the caller's duty until the slot table of Plan §11.11.7.
    pub fn slot_words(
        self: &Arc<DurStore>,
        key: &[u8],
        default: [u64; 2],
    ) -> Result<Arc<DurCell>, StoreError> {
        let key = HeadKey(key.to_vec());
        let (words, version, descriptor) = match self.nodes.head(&key)? {
            Some(head) => {
                let node = self.nodes.get(head.root)?;
                let (header, payload) = decode_node(&node)?;
                if header.kind != KIND_WORDS || payload.len() != 16 {
                    return Err(StoreError::StoreFault(format!(
                        "the slot's node has kind {}, not a value of two words",
                        header.kind
                    )));
                }
                let words = [
                    u64::from_le_bytes(payload[..8].try_into().expect("sized")),
                    u64::from_le_bytes(payload[8..].try_into().expect("sized")),
                ];
                (words, head.version, head.descriptor)
            }
            None => (default, 0, DescriptorId(0)),
        };
        Ok(Arc::new(DurCell {
            cell: Cell::new(words),
            store: self.clone(),
            key,
            descriptor,
            head: AtomicU64::new(version),
            list: 0,
        }))
    }

    /// Hands a batch to the writer and waits for its outcome.
    pub(crate) fn commit(&self, batch: CommitBatch) -> Result<CommitOutcome, StoreError> {
        let (reply, outcome) = sync_channel(1);
        let sender = self
            .sender
            .lock()
            .expect("a poisoned store")
            .as_ref()
            .ok_or_else(|| StoreError::StoreFault("the store is closed".into()))?
            .clone();
        sender
            .send(Request { batch, reply })
            .map_err(|_| StoreError::StoreFault("the store's writer is gone".into()))?;
        outcome
            .recv()
            .map_err(|_| StoreError::StoreFault("the store's writer is gone".into()))?
    }

    /// Whether two handles are the same store, for the one-store rule of
    /// an atomic block (Specification §21.6).
    pub(crate) fn same(a: &Arc<DurStore>, b: &Arc<DurStore>) -> bool {
        Arc::ptr_eq(a, b)
    }
}

impl Drop for DurStore {
    fn drop(&mut self) {
        // Closing the channel ends the writer; joining it bounds every
        // run that holds a store.
        *self.sender.lock().expect("a poisoned store") = None;
        if let Some(writer) = self.writer.lock().expect("a poisoned store").take() {
            let _ = writer.join();
        }
    }
}

/// Drains commits until the store closes. Commits are already serialized
/// by the channel; sharing one backend transaction over waiting commits
/// (group commit) can land here without changing callers.
fn writer_loop(nodes: &dyn NodeStore, receiver: &Receiver<Request>) {
    while let Ok(request) = receiver.recv() {
        let outcome = nodes.commit(request.batch);
        // A waiter that gave up is its own problem; the commit stands.
        let _ = request.reply.send(outcome);
    }
}

/// A durable cell: a ref cell plus its head in a store. The words and
/// `head` change together under the cell's lock, so a reader that sees
/// the cell unlocked at one version has the pair of that version.
pub struct DurCell {
    pub(crate) cell: Cell,
    pub(crate) store: Arc<DurStore>,
    pub(crate) key: HeadKey,
    pub(crate) descriptor: DescriptorId,
    /// The durable head version of the value in the cell.
    pub(crate) head: AtomicU64,
    /// The list type of the value's words, 0 while only values without
    /// references are stored.
    pub(crate) list: u64,
}

impl DurCell {
    /// The value, its TL2 version and its head version, consistent with
    /// one another; none while a write holds the cell.
    pub(crate) fn snapshot(&self) -> Option<(u64, [u64; 2], u64)> {
        let (version, words) = self.cell.try_read()?;
        let head = self.head.load(Ordering::Acquire);
        // The head is written under the cell's lock, so an unchanged,
        // unlocked cell version pins the pair.
        (self.cell.version() == version).then_some((version, words, head))
    }

    /// As `snapshot`, waiting out writes under way.
    pub(crate) fn snapshot_blocking(&self) -> (u64, [u64; 2], u64) {
        let mut spins = 0;
        loop {
            if let Some(read) = self.snapshot() {
                return read;
            }
            crate::refs::back_off(&mut spins);
        }
    }

    /// The current value, as a plain read outside a block (`use` without
    /// a closure).
    pub fn get(&self) -> [u64; 2] {
        self.snapshot_blocking().1
    }

    /// The node holding `words`, for this cell's next commit.
    pub(crate) fn encode(&self, words: [u64; 2]) -> Vec<u8> {
        let header = NodeHeader {
            descriptor: self.descriptor,
            kind: KIND_WORDS,
            children: Vec::new(),
        };
        let mut payload = [0; 16];
        payload[..8].copy_from_slice(&words[0].to_le_bytes());
        payload[8..].copy_from_slice(&words[1].to_le_bytes());
        encode_node(&header, &payload)
    }

    /// An optimistic update of this cell alone, as `d.update(f)` outside
    /// an `atomic` block (Specification §9.3, §21.6): reruns on conflict,
    /// returns the value `f` gave, or the first storage error.
    pub fn update(
        self: &Arc<DurCell>,
        mut f: impl FnMut([u64; 2]) -> [u64; 2],
    ) -> Result<[u64; 2], StoreError> {
        let mut spins = 0;
        loop {
            let mut log = TxLog::headless();
            let Some(read) = log.read_dur(self) else {
                crate::refs::back_off(&mut spins);
                continue;
            };
            let words = f(read);
            if words == read {
                return Ok(words);
            }
            log.write_dur(self, words)?;
            // SAFETY: the cell is live for the call, and its words hold
            // no references (`list` 0), so the lapsed log releases
            // nothing.
            match unsafe { log.store_durable() }? {
                Some(_) => return Ok(words),
                None => crate::refs::back_off(&mut spins),
            }
        }
    }
}

#[cfg(all(test, not(loom)))]
mod tests {
    use super::*;
    use crag_dur::mem::MemStore;

    fn counter(store: &Arc<DurStore>) -> Arc<DurCell> {
        store.slot_words(b"hits", [0, 0]).unwrap()
    }

    #[test]
    fn an_update_commits_and_a_reopen_reads_it() {
        let backend = Arc::new(MemStore::new());
        let store = DurStore::new(backend.clone());
        let hits = counter(&store);
        assert_eq!(hits.get(), [0, 0]);
        hits.update(|[n, _]| [n + 1, 0]).unwrap();
        hits.update(|[n, _]| [n + 1, 0]).unwrap();
        assert_eq!(hits.get(), [2, 0]);
        drop((hits, store));

        // The same backend, as a process that opens the file again.
        let store = DurStore::new(backend);
        let hits = counter(&store);
        assert_eq!(hits.get(), [2, 0]);
    }

    #[test]
    fn racing_updates_lose_none() {
        let store = DurStore::new(Arc::new(MemStore::new()));
        let hits = counter(&store);
        std::thread::scope(|s| {
            for _ in 0..4 {
                let hits = hits.clone();
                s.spawn(move || {
                    for _ in 0..250 {
                        hits.update(|[n, _]| [n + 1, 0]).unwrap();
                    }
                });
            }
        });
        assert_eq!(hits.get(), [1000, 0]);
        // The head agrees with the cell.
        let head = store
            .nodes()
            .head(&HeadKey(b"hits".to_vec()))
            .unwrap()
            .unwrap();
        let node = store.nodes().get(head.root).unwrap();
        let (_, payload) = decode_node(&node).unwrap();
        assert_eq!(payload[..8], 1000u64.to_le_bytes());
    }

    #[test]
    fn an_unchanged_update_writes_nothing() {
        let store = DurStore::new(Arc::new(MemStore::new()));
        let hits = counter(&store);
        hits.update(|words| words).unwrap();
        assert!(
            store
                .nodes()
                .head(&HeadKey(b"hits".to_vec()))
                .unwrap()
                .is_none()
        );
    }
}
