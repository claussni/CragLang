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

//! The storage facade and its backends (Plan §11.11.1, §11.11.2): the
//! same commits against the LMDB file and the memory store, survival of
//! a reopen, conflicts, reclamation counts and planned faults.

use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU32, Ordering};

use crag_dur::fault::{Fault, FaultStore};
use crag_dur::lmdb::LmdbStore;
use crag_dur::mem::MemStore;
use crag_dur::{
    CommitBatch, CommitOutcome, DescriptorId, Durability, HeadKey, HeadMove, NodeHeader, NodeId,
    NodeStore, StoreError, encode_node,
};

/// A fresh directory under the system's temporary directory, removed on
/// drop.
struct TempDir(PathBuf);

impl TempDir {
    fn new() -> TempDir {
        static NEXT: AtomicU32 = AtomicU32::new(0);
        let name = format!(
            "crag-dur-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        );
        let dir = std::env::temp_dir().join(name);
        fs::create_dir_all(&dir).unwrap();
        TempDir(dir)
    }

    fn file(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const MAP: usize = 10 << 20;

fn open(dir: &TempDir) -> std::sync::Arc<LmdbStore> {
    LmdbStore::open(&dir.file("store.crag"), MAP, Durability::Full).unwrap()
}

/// A leaf node without children, holding `value`.
fn leaf(store: &dyn NodeStore, value: u64) -> (NodeId, Vec<u8>) {
    let id = store.allocate(1);
    let header = NodeHeader {
        descriptor: DescriptorId(1),
        kind: 0,
        children: Vec::new(),
    };
    (id, encode_node(&header, &value.to_le_bytes()))
}

/// An inner node over `children`.
fn branch(store: &dyn NodeStore, children: Vec<NodeId>) -> (NodeId, Vec<u8>) {
    let id = store.allocate(1);
    let header = NodeHeader {
        descriptor: DescriptorId(1),
        kind: 1,
        children,
    };
    (id, encode_node(&header, &[]))
}

fn key(name: &str) -> HeadKey {
    HeadKey(name.as_bytes().to_vec())
}

/// Moves `key` to a fresh leaf of `value`, expecting version `read`.
fn put(store: &dyn NodeStore, name: &str, value: u64, read: u64) -> CommitOutcome {
    let (id, bytes) = leaf(store, value);
    let batch = CommitBatch {
        nodes: vec![(id, bytes)],
        heads: vec![HeadMove {
            key: key(name),
            root: id,
            descriptor: DescriptorId(1),
            read,
        }],
        ..CommitBatch::default()
    };
    store.commit(batch).unwrap()
}

fn committed(outcome: CommitOutcome) -> u64 {
    match outcome {
        CommitOutcome::Committed { version } => version,
        CommitOutcome::Conflict { key } => {
            panic!(
                "an unexpected conflict on {:?}",
                String::from_utf8_lossy(&key.0)
            )
        }
    }
}

/// The semantics every backend shares.
fn behaves(store: &dyn NodeStore) {
    // A head is written with its node and read back.
    let version = committed(put(store, "hits", 0, 0));
    let head = store.head(&key("hits")).unwrap().expect("a head");
    assert_eq!(head.version, version);
    let node = store.get(head.root).unwrap();
    let (header, payload) = crag_dur::decode_node(&node).unwrap();
    assert_eq!(payload, 0u64.to_le_bytes());
    assert_eq!(header.children, Vec::new());
    drop(node);

    // A stale read conflicts and writes nothing; the version read commits.
    let outcome = put(store, "hits", 1, version + 7);
    assert!(matches!(outcome, CommitOutcome::Conflict { key } if key == self::key("hits")));
    assert_eq!(
        store.head(&key("hits")).unwrap().expect("a head").version,
        version
    );
    committed(put(store, "hits", 1, version));

    // The old root is unreferenced now and only it; freeing it leaves the
    // store to the new one.
    assert_eq!(store.freeable(16).unwrap(), vec![head.root]);
    store.free(&[head.root]).unwrap();
    assert!(store.freeable(16).unwrap().is_empty());
    assert!(store.get(head.root).is_err());

    // A tree: freeing a branch drops its leaves onto the free list, but a
    // leaf a second parent shares stays.
    let (l1, b1) = leaf(store, 10);
    let (l2, b2) = leaf(store, 20);
    let (p, bp) = branch(store, vec![l1, l2]);
    let (q, bq) = branch(store, vec![l2]);
    let batch = CommitBatch {
        nodes: vec![(l1, b1), (l2, b2), (p, bp), (q, bq)],
        heads: vec![
            HeadMove {
                key: key("tree"),
                root: p,
                descriptor: DescriptorId(1),
                read: 0,
            },
            HeadMove {
                key: key("shared"),
                root: q,
                descriptor: DescriptorId(1),
                read: 0,
            },
        ],
        ..CommitBatch::default()
    };
    let version = committed(store.commit(batch).unwrap());
    let (root, bytes) = leaf(store, 30);
    let batch = CommitBatch {
        nodes: vec![(root, bytes)],
        heads: vec![HeadMove {
            key: key("tree"),
            root,
            descriptor: DescriptorId(1),
            read: version,
        }],
        ..CommitBatch::default()
    };
    committed(store.commit(batch).unwrap());
    assert_eq!(store.freeable(16).unwrap(), vec![p]);
    store.free(&[p]).unwrap();
    assert_eq!(store.freeable(16).unwrap(), vec![l1]);
    store.free(&[l1]).unwrap();
    assert!(store.freeable(16).unwrap().is_empty());
    assert_eq!(
        crag_dur::decode_node(&store.get(l2).unwrap()).unwrap().1,
        20u64.to_le_bytes()
    );

    // Both heads are listed.
    let mut names: Vec<Vec<u8>> = store
        .heads()
        .unwrap()
        .into_iter()
        .map(|(k, _)| k.0)
        .collect();
    names.sort();
    assert_eq!(
        names,
        vec![b"hits".to_vec(), b"shared".to_vec(), b"tree".to_vec()]
    );

    // Descriptors are stored with the commit and read back.
    let d = store.allocate_descriptor();
    let batch = CommitBatch {
        descriptors: vec![(d, b"a type".to_vec())],
        ..CommitBatch::default()
    };
    committed(store.commit(batch).unwrap());
    assert_eq!(store.descriptor(d).unwrap(), b"a type".to_vec());
    assert!(store.descriptor(DescriptorId(d.0 + 1)).is_err());

    // Freeing a referenced or unknown node is refused.
    assert!(store.free(&[root]).is_err());
    assert!(store.free(&[NodeId(u64::MAX)]).is_err());
}

#[test]
fn the_lmdb_store_behaves() {
    let dir = TempDir::new();
    behaves(&*open(&dir));
}

#[test]
fn the_memory_store_behaves() {
    behaves(&MemStore::new());
}

#[test]
fn a_head_survives_a_reopen() {
    let dir = TempDir::new();
    let (root, version, next) = {
        let store = open(&dir);
        let version = committed(put(&*store, "hits", 0, 0));
        let version = committed(put(&*store, "hits", 1, version));
        let head = store.head(&key("hits")).unwrap().expect("a head");
        (head.root, version, store.allocate(1).0)
    };
    let store = open(&dir);
    let head = store
        .head(&key("hits"))
        .unwrap()
        .expect("a head after the reopen");
    assert_eq!(head.root, root);
    assert_eq!(head.version, version);
    let node = store.get(head.root).unwrap();
    let (_, payload) = crag_dur::decode_node(&node).unwrap();
    assert_eq!(payload, 1u64.to_le_bytes());
    drop(node);
    // Ids keep rising over the restart, and the free list survived: the
    // first value's node is still on it.
    assert!(store.allocate(1).0 > next - 1);
    assert_eq!(store.freeable(16).unwrap().len(), 1);
    // The next commit validates against the stored version.
    assert!(matches!(
        put(&*store, "hits", 2, 0),
        CommitOutcome::Conflict { .. }
    ));
    committed(put(&*store, "hits", 2, version));
}

#[test]
fn a_file_opens_once() {
    let dir = TempDir::new();
    let store = open(&dir);
    let again = LmdbStore::open(&dir.file("store.crag"), MAP, Durability::Full);
    assert!(matches!(again, Err(StoreError::AlreadyOpen)));
    drop(store);
    open(&dir);
}

#[test]
fn a_compacted_copy_holds_the_same() {
    let dir = TempDir::new();
    let store = open(&dir);
    let version = committed(put(&*store, "hits", 41, 0));
    store.compact_copy(&dir.file("copy.crag")).unwrap();
    let copy = LmdbStore::open(&dir.file("copy.crag"), MAP, Durability::Full).unwrap();
    let head = copy
        .head(&key("hits"))
        .unwrap()
        .expect("a head in the copy");
    assert_eq!(head.version, version);
    let node = copy.get(head.root).unwrap();
    assert_eq!(crag_dur::decode_node(&node).unwrap().1, 41u64.to_le_bytes());
}

#[test]
fn stats_count_nodes_and_free_list() {
    let dir = TempDir::new();
    let store = open(&dir);
    let version = committed(put(&*store, "hits", 0, 0));
    committed(put(&*store, "hits", 1, version));
    let stats = store.stats().unwrap();
    assert_eq!(stats.nodes, 2);
    assert_eq!(stats.free_list, 1);
    assert_eq!(stats.map_size, MAP as u64);
    assert!(stats.disk > 0);
}

#[test]
fn a_buffered_store_syncs_on_demand() {
    let dir = TempDir::new();
    let store = LmdbStore::open(&dir.file("store.crag"), MAP, Durability::Buffered).unwrap();
    committed(put(&*store, "hits", 7, 0));
    store.sync().unwrap();
}

#[test]
fn planned_faults_surface_as_their_errors() {
    let store = FaultStore::new(MemStore::new());
    let version = committed(put(&store, "hits", 0, 0));

    // A failed commit writes nothing.
    store.plan(Fault::Commit(StoreError::StoreFull));
    let (id, bytes) = leaf(&store, 1);
    let batch = CommitBatch {
        nodes: vec![(id, bytes.clone())],
        heads: vec![HeadMove {
            key: key("hits"),
            root: id,
            descriptor: DescriptorId(1),
            read: version,
        }],
        ..CommitBatch::default()
    };
    assert_eq!(store.commit(batch.clone()), Err(StoreError::StoreFull));
    assert!(store.get(id).is_err());

    // A torn commit keeps the nodes but loses the head move; the head
    // still answers with its old version.
    store.plan(Fault::TornCommit(StoreError::StoreFault("torn".into())));
    assert!(store.commit(batch).is_err());
    assert_eq!(
        store.head(&key("hits")).unwrap().expect("a head").version,
        version
    );
    assert!(store.get(id).is_ok());

    // A failed sync and a failed get report as planned.
    store.plan(Fault::Sync(StoreError::StoreFault("sync".into())));
    assert!(store.sync().is_err());
    store.plan(Fault::Get(StoreError::StoreFault("get".into())));
    assert!(store.get(id).is_err());
}
