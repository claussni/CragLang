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

//! The LMDB backend (Plan §11.11.2): crash-safe transactions over a
//! memory-mapped file, through [heed](https://docs.rs/heed).
//!
//! Three settings follow from Crag's runtime. The environment is opened
//! without thread-local storage (`MDB_NOTLS`), because a fiber's read may
//! resume on another thread. A process-wide registry keyed by the
//! canonical path guarantees that a file is opened once, which LMDB
//! requires of a process. And read transactions stay short, because
//! Crag's own nodes, not LMDB's snapshots, hold old versions
//! (Specification §21.9).
//!
//! The file holds six tables: `nodes`, `heads`, `types` (the descriptors,
//! Plan §11.11.7), `parents` (the counts of reclamation, Plan §11.11.9),
//! `free` (the durable free list) and `meta`, which carries the storage
//! format version, the commit sequence and the id high-water marks, so
//! ids stay monotonic across restarts.

use std::collections::HashMap;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock, Weak};

use heed::byteorder::BE;
use heed::types::{Bytes, Str, U64};
use heed::{Database, Env, EnvFlags, EnvOpenOptions, PutFlags, RoTxn, WithoutTls};

use crate::{
    CommitBatch, CommitOutcome, DescriptorId, Durability, FORMAT, Head, HeadKey, NodeId, NodeRef,
    NodeStore, StoreError, StoreStats, children_of,
};

/// A store in one LMDB file.
pub struct LmdbStore {
    env: Env<WithoutTls>,
    nodes: Database<U64<BE>, Bytes>,
    heads: Database<Bytes, Bytes>,
    types: Database<U64<BE>, Bytes>,
    parents: Database<U64<BE>, U64<BE>>,
    free: Database<U64<BE>, Bytes>,
    meta: Database<Str, U64<BE>>,
    path: PathBuf,
    /// Commits serialize on this lock; LMDB would otherwise block the
    /// whole OS thread on its writer mutex.
    write: Mutex<()>,
    next_node: AtomicU64,
    next_descriptor: AtomicU64,
    version: AtomicU64,
    /// Set by a failed sync: every later commit returns `ReadOnly`
    /// (Specification §21.7).
    read_only: AtomicBool,
}

/// The files the process holds open, so a second open of one returns
/// `AlreadyOpen` (Specification §21.3).
static OPEN: OnceLock<Mutex<HashMap<PathBuf, Weak<LmdbStore>>>> = OnceLock::new();

fn registry() -> &'static Mutex<HashMap<PathBuf, Weak<LmdbStore>>> {
    OPEN.get_or_init(Mutex::default)
}

/// The canonical form of `path`; the file itself may not exist yet, so
/// the parent is canonicalized and the file name joined back.
fn canonical(path: &Path) -> Result<PathBuf, StoreError> {
    if let Ok(whole) = path.canonicalize() {
        return Ok(whole);
    }
    let parent = match path.parent() {
        Some(parent) if parent.as_os_str().is_empty() => Path::new("."),
        Some(parent) => parent,
        None => {
            return Err(StoreError::StoreFault(format!(
                "no parent of {}",
                path.display()
            )));
        }
    };
    let name = path
        .file_name()
        .ok_or_else(|| StoreError::StoreFault(format!("no file name in {}", path.display())))?;
    let parent = parent
        .canonicalize()
        .map_err(|e| StoreError::StoreFault(format!("{}: {e}", parent.display())))?;
    Ok(parent.join(name))
}

fn fault(e: impl std::fmt::Display) -> StoreError {
    StoreError::StoreFault(e.to_string())
}

/// Maps a heed error to the store errors the language declares.
fn store_error(e: heed::Error) -> StoreError {
    match e {
        heed::Error::Mdb(heed::MdbError::MapFull) => StoreError::StoreFull,
        heed::Error::EnvAlreadyOpened => StoreError::AlreadyOpen,
        other => fault(other),
    }
}

/// A head's stored record: root, version and descriptor, little-endian.
fn encode_head(head: &Head) -> [u8; 24] {
    let mut out = [0; 24];
    out[..8].copy_from_slice(&head.root.0.to_le_bytes());
    out[8..16].copy_from_slice(&head.version.to_le_bytes());
    out[16..].copy_from_slice(&head.descriptor.0.to_le_bytes());
    out
}

fn decode_head(bytes: &[u8]) -> Result<Head, StoreError> {
    if bytes.len() != 24 {
        return Err(StoreError::StoreFault(
            "a stored head has the wrong size".into(),
        ));
    }
    Ok(Head {
        root: NodeId(u64::from_le_bytes(bytes[..8].try_into().expect("sized"))),
        version: u64::from_le_bytes(bytes[8..16].try_into().expect("sized")),
        descriptor: DescriptorId(u64::from_le_bytes(bytes[16..].try_into().expect("sized"))),
    })
}

impl LmdbStore {
    /// Opens the store file, creating it when it does not exist.
    /// `AlreadyOpen` when this process already holds it.
    pub fn open(
        path: &Path,
        map_size: usize,
        durability: Durability,
    ) -> Result<Arc<LmdbStore>, StoreError> {
        let path = canonical(path)?;
        let mut open = registry().lock().expect("a poisoned registry");
        open.retain(|_, store| store.strong_count() > 0);
        if open.contains_key(&path) {
            return Err(StoreError::AlreadyOpen);
        }
        let mut options = EnvOpenOptions::new().read_txn_without_tls();
        options.map_size(map_size).max_dbs(6);
        let mut flags = EnvFlags::NO_SUB_DIR;
        match durability {
            Durability::Full => {}
            Durability::Flush => flags |= EnvFlags::NO_META_SYNC,
            Durability::Buffered => flags |= EnvFlags::NO_SYNC,
        }
        // SAFETY: flags do not change LMDB's aliasing rules (no
        // `MDB_WRITEMAP`), and the registry keeps the file opened once.
        let env = unsafe {
            options.flags(flags);
            options.open(&path)
        }
        .map_err(store_error)?;
        let mut wtxn = env.write_txn().map_err(store_error)?;
        let nodes = env
            .create_database(&mut wtxn, Some("nodes"))
            .map_err(store_error)?;
        let heads = env
            .create_database(&mut wtxn, Some("heads"))
            .map_err(store_error)?;
        let types = env
            .create_database(&mut wtxn, Some("types"))
            .map_err(store_error)?;
        let parents = env
            .create_database(&mut wtxn, Some("parents"))
            .map_err(store_error)?;
        let free = env
            .create_database(&mut wtxn, Some("free"))
            .map_err(store_error)?;
        let meta: Database<Str, U64<BE>> = env
            .create_database(&mut wtxn, Some("meta"))
            .map_err(store_error)?;
        match meta.get(&wtxn, "format").map_err(store_error)? {
            None => meta
                .put(&mut wtxn, "format", &FORMAT)
                .map_err(store_error)?,
            Some(format) if format <= FORMAT => {}
            Some(format) => {
                return Err(StoreError::StoreFault(format!(
                    "the store has format {format}, this runtime reads up to {FORMAT}"
                )));
            }
        }
        let version = meta
            .get(&wtxn, "version")
            .map_err(store_error)?
            .unwrap_or(0);
        // Id zero is never handed out, so it can mean "none".
        let next_node = meta
            .get(&wtxn, "next_node")
            .map_err(store_error)?
            .unwrap_or(1);
        let next_descriptor = meta
            .get(&wtxn, "next_descriptor")
            .map_err(store_error)?
            .unwrap_or(1);
        wtxn.commit().map_err(store_error)?;
        let store = Arc::new(LmdbStore {
            env,
            nodes,
            heads,
            types,
            parents,
            free,
            meta,
            path: path.clone(),
            write: Mutex::new(()),
            next_node: AtomicU64::new(next_node),
            next_descriptor: AtomicU64::new(next_descriptor),
            version: AtomicU64::new(version),
            read_only: AtomicBool::new(false),
        });
        open.insert(path, Arc::downgrade(&store));
        Ok(store)
    }

    /// Writes a compacted copy of the file, for `:store compact`
    /// (Specification §21.10).
    pub fn compact_copy(&self, to: &Path) -> Result<(), StoreError> {
        let mut file = std::fs::File::create_new(to)
            .map_err(|e| StoreError::StoreFault(format!("{}: {e}", to.display())))?;
        self.env
            .copy_to_file(&mut file, heed::CompactionOption::Enabled)
            .map_err(store_error)
    }

    fn read_txn(&self) -> Result<RoTxn<'_, WithoutTls>, StoreError> {
        self.env.read_txn().map_err(store_error)
    }

    /// Drops a node's parent count by one; at zero the node goes onto the
    /// free list.
    fn drop_count(&self, wtxn: &mut heed::RwTxn<'_>, id: NodeId) -> Result<(), StoreError> {
        let count = self
            .parents
            .get(wtxn, &id.0)
            .map_err(store_error)?
            .filter(|&c| c > 0)
            .ok_or_else(|| StoreError::StoreFault(format!("node {} is not referenced", id.0)))?;
        self.parents
            .put(wtxn, &id.0, &(count - 1))
            .map_err(store_error)?;
        if count == 1 {
            self.free.put(wtxn, &id.0, &[]).map_err(store_error)?;
        }
        Ok(())
    }

    fn bump_count(&self, wtxn: &mut heed::RwTxn<'_>, id: NodeId) -> Result<(), StoreError> {
        let count = self
            .parents
            .get(wtxn, &id.0)
            .map_err(store_error)?
            .unwrap_or(0);
        self.parents
            .put(wtxn, &id.0, &(count + 1))
            .map_err(store_error)?;
        if count == 0 {
            self.free.delete(wtxn, &id.0).map_err(store_error)?;
        }
        Ok(())
    }

    /// Deletes nodes of count zero inside `wtxn`, as
    /// [`crate::NodeStore::free`] promises.
    fn free_nodes(&self, wtxn: &mut heed::RwTxn<'_>, ids: &[NodeId]) -> Result<(), StoreError> {
        for id in ids {
            if self
                .parents
                .get(wtxn, &id.0)
                .map_err(store_error)?
                .unwrap_or(0)
                != 0
            {
                return Err(StoreError::StoreFault(format!(
                    "node {} is freed while referenced",
                    id.0
                )));
            }
            let children = {
                let node = self
                    .nodes
                    .get(wtxn, &id.0)
                    .map_err(store_error)?
                    .ok_or_else(|| {
                        StoreError::StoreFault(format!("node {} is freed twice", id.0))
                    })?;
                children_of(node)?
            };
            self.nodes.delete(wtxn, &id.0).map_err(store_error)?;
            self.parents.delete(wtxn, &id.0).map_err(store_error)?;
            self.free.delete(wtxn, &id.0).map_err(store_error)?;
            for child in children {
                self.drop_count(wtxn, child)?;
            }
        }
        Ok(())
    }
}

impl Drop for LmdbStore {
    fn drop(&mut self) {
        let mut open = registry().lock().expect("a poisoned registry");
        open.remove(&self.path);
    }
}

/// A node's bytes in the memory map, under the read transaction that
/// keeps its pages valid.
struct MapBytes<'e> {
    _txn: RoTxn<'e, WithoutTls>,
    ptr: *const u8,
    len: usize,
}

// SAFETY: the bytes are read-only pages of the map, and the transaction
// moves between threads only whole (`MDB_NOTLS`).
unsafe impl Send for MapBytes<'_> {}
unsafe impl Sync for MapBytes<'_> {}

impl Deref for MapBytes<'_> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        // SAFETY: the pointer is into pages of the memory map, which LMDB
        // leaves in place and unchanged while the read transaction lives;
        // it does not point into the transaction value, so the move into
        // `MapBytes` did not invalidate it.
        unsafe { std::slice::from_raw_parts(self.ptr, self.len) }
    }
}

impl NodeStore for LmdbStore {
    fn commit(&self, batch: CommitBatch) -> Result<CommitOutcome, StoreError> {
        if self.read_only.load(Ordering::Relaxed) {
            return Err(StoreError::ReadOnly);
        }
        let _writer = self.write.lock().expect("a poisoned writer lock");
        let mut wtxn = self.env.write_txn().map_err(store_error)?;
        // Validate every head first: on a conflict nothing is written.
        for head in &batch.heads {
            let stored = self.heads.get(&wtxn, &head.key.0).map_err(store_error)?;
            let version = stored
                .map(decode_head)
                .transpose()?
                .map_or(0, |h| h.version);
            if version != head.read {
                return Ok(CommitOutcome::Conflict {
                    key: head.key.clone(),
                });
            }
        }
        let version = self.version.load(Ordering::Relaxed) + 1;
        for (id, descriptor) in &batch.descriptors {
            self.types
                .put(&mut wtxn, &id.0, descriptor)
                .map_err(store_error)?;
        }
        let mut nodes: Vec<&(NodeId, Vec<u8>)> = batch.nodes.iter().collect();
        nodes.sort_by_key(|(id, _)| *id);
        let mut highest = 0;
        for (id, bytes) in nodes {
            highest = highest.max(id.0);
            self.nodes
                .put_with_flags(&mut wtxn, PutFlags::NO_OVERWRITE, &id.0, bytes)
                .map_err(|e| match e {
                    heed::Error::Mdb(heed::MdbError::KeyExist) => {
                        StoreError::StoreFault(format!("node {} is stored twice", id.0))
                    }
                    other => store_error(other),
                })?;
            for child in children_of(bytes)? {
                self.bump_count(&mut wtxn, child)?;
            }
        }
        for head in &batch.heads {
            self.bump_count(&mut wtxn, head.root)?;
            let new = Head {
                root: head.root,
                version,
                descriptor: head.descriptor,
            };
            let old = self.heads.get(&wtxn, &head.key.0).map_err(store_error)?;
            let old = old.map(decode_head).transpose()?;
            self.heads
                .put(&mut wtxn, &head.key.0, &encode_head(&new))
                .map_err(store_error)?;
            if let Some(old) = old {
                self.drop_count(&mut wtxn, old.root)?;
            }
        }
        self.free_nodes(&mut wtxn, &batch.frees)?;
        self.meta
            .put(&mut wtxn, "version", &version)
            .map_err(store_error)?;
        let next = self.next_node.load(Ordering::Relaxed).max(highest + 1);
        self.meta
            .put(&mut wtxn, "next_node", &next)
            .map_err(store_error)?;
        let descriptor = self.next_descriptor.load(Ordering::Relaxed);
        self.meta
            .put(&mut wtxn, "next_descriptor", &descriptor)
            .map_err(store_error)?;
        wtxn.commit().map_err(store_error)?;
        self.version.store(version, Ordering::Relaxed);
        Ok(CommitOutcome::Committed { version })
    }

    fn get(&self, id: NodeId) -> Result<NodeRef<'_>, StoreError> {
        let txn = self.read_txn()?;
        let bytes = self
            .nodes
            .get(&txn, &id.0)
            .map_err(store_error)?
            .ok_or_else(|| StoreError::StoreFault(format!("node {} is not stored", id.0)))?;
        let (ptr, len) = (bytes.as_ptr(), bytes.len());
        Ok(NodeRef::new(Box::new(MapBytes {
            _txn: txn,
            ptr,
            len,
        })))
    }

    fn head(&self, key: &HeadKey) -> Result<Option<Head>, StoreError> {
        let txn = self.read_txn()?;
        let stored = self.heads.get(&txn, &key.0).map_err(store_error)?;
        stored.map(decode_head).transpose()
    }

    fn heads(&self) -> Result<Vec<(HeadKey, Head)>, StoreError> {
        let txn = self.read_txn()?;
        let mut out = Vec::new();
        for entry in self.heads.iter(&txn).map_err(store_error)? {
            let (key, head) = entry.map_err(store_error)?;
            out.push((HeadKey(key.to_vec()), decode_head(head)?));
        }
        Ok(out)
    }

    fn descriptor(&self, id: DescriptorId) -> Result<Vec<u8>, StoreError> {
        let txn = self.read_txn()?;
        self.types
            .get(&txn, &id.0)
            .map_err(store_error)?
            .map(<[u8]>::to_vec)
            .ok_or_else(|| StoreError::StoreFault(format!("descriptor {} is not stored", id.0)))
    }

    fn free(&self, ids: &[NodeId]) -> Result<(), StoreError> {
        let _writer = self.write.lock().expect("a poisoned writer lock");
        let mut wtxn = self.env.write_txn().map_err(store_error)?;
        self.free_nodes(&mut wtxn, ids)?;
        wtxn.commit().map_err(store_error)
    }

    fn freeable(&self, limit: usize) -> Result<Vec<NodeId>, StoreError> {
        let txn = self.read_txn()?;
        let mut out = Vec::new();
        for entry in self.free.iter(&txn).map_err(store_error)?.take(limit) {
            let (id, _) = entry.map_err(store_error)?;
            out.push(NodeId(id));
        }
        Ok(out)
    }

    fn allocate(&self, count: u64) -> NodeId {
        NodeId(self.next_node.fetch_add(count, Ordering::Relaxed))
    }

    fn allocate_descriptor(&self) -> DescriptorId {
        DescriptorId(self.next_descriptor.fetch_add(1, Ordering::Relaxed))
    }

    fn sync(&self) -> Result<(), StoreError> {
        match self.env.force_sync() {
            Ok(()) => Ok(()),
            Err(e) => {
                // A failed sync loses an unknown tail of commits, so the
                // store stops taking more (Specification §21.7).
                self.read_only.store(true, Ordering::Relaxed);
                Err(store_error(e))
            }
        }
    }

    fn stats(&self) -> Result<StoreStats, StoreError> {
        let txn = self.read_txn()?;
        let nodes = self.nodes.len(&txn).map_err(store_error)?;
        let free_list = self.free.len(&txn).map_err(store_error)?;
        let info = self.env.info();
        let disk = std::fs::metadata(&self.path).map(|m| m.len()).unwrap_or(0);
        Ok(StoreStats {
            map_size: info.map_size as u64,
            disk,
            nodes,
            free_list,
        })
    }
}
