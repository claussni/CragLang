//! Incremental query facade (Implementation Plan §11.3.7).
//!
//! Inputs, tracked and interned queries, durability levels and cancellation.
//!
//! The compiler is a network of queries, and Salsa is the engine that caches
//! them. Only this crate depends on Salsa. The other compiler crates define
//! their queries with the macros re-exported here and take the database as
//! `&dyn crag_db::Db`.
//!
//! # Using the facade from another crate
//!
//! Salsa's macros expand to paths that start with `::salsa`, so a crate that
//! uses them must know this crate under that name. Put one line at its root:
//!
//! ```ignore
//! extern crate crag_db as salsa;
//! ```
//!
//! and then write `crag_db::` everywhere in the code itself:
//!
//! ```ignore
//! #[crag_db::input]
//! pub struct SourceFile {
//!     #[returns(ref)]
//!     pub text: String,
//! }
//!
//! #[crag_db::tracked]
//! pub fn line_count(db: &dyn crag_db::Db, file: SourceFile) -> usize {
//!     file.text(db).lines().count()
//! }
//! ```
//!
//! A query returns a reference to its cached result, which borrows the
//! database; copy or clone the value to keep it longer.
//!
//! # What is Salsa's and what is ours
//!
//! The macros, [`Durability`] and the [`Setter`] trait of input setters are
//! Salsa's, re-exported. A new Salsa release that changes them is absorbed
//! here where possible, and otherwise changes query definitions in a
//! mechanical way.
//!
//! The database type, snapshots and cancellation are ours: [`RootDatabase`],
//! [`Snapshot`], [`check_cancelled`] and [`catch_cancelled`]. Salsa signals
//! cancellation by unwinding, so a process that cancels queries must be built
//! with unwinding panics, as the workspace profiles are.

use std::panic::AssertUnwindSafe;

// The query macros, and the derive for plain types stored in query results.
pub use salsa::{SalsaValue, Supertype, accumulator, input, interned, tracked};
// Used when setting inputs: `file.set_text(&mut db).with_durability(..).to(..)`.
pub use salsa::{Durability, Setter};

// What the expansions of the macros name at the root of `::salsa`. These are
// not part of the facade; they are here only for the `extern crate` line.
#[doc(hidden)]
pub use salsa::{Accumulator, Cycle, Database, Id, SalsaAsDeref, SalsaAsRef, plumbing};

/// The database as queries see it. Every query takes `&dyn Db` as its first
/// parameter.
#[salsa::db]
pub trait Db: salsa::Database {}

/// The database: all inputs and all cached results.
///
/// Changing an input needs `&mut RootDatabase` and starts a new revision.
/// Reading happens through `&dyn Db`, on this handle or on a [`Snapshot`].
#[salsa::db]
#[derive(Clone, Default)]
pub struct RootDatabase {
    storage: salsa::Storage<Self>,
}

#[salsa::db]
impl salsa::Database for RootDatabase {}

#[salsa::db]
impl Db for RootDatabase {}

impl RootDatabase {
    pub fn new() -> RootDatabase {
        RootDatabase::default()
    }

    /// A read view for another thread, such as the language server's
    /// request handlers or reload planning.
    ///
    /// A snapshot sees a consistent state: while it exists, no input changes.
    /// A change waits until every snapshot is dropped, and meanwhile asks the
    /// queries running on them to stop (see [`check_cancelled`]).
    pub fn snapshot(&self) -> Snapshot {
        Snapshot(self.clone())
    }
}

/// A read-only handle on the database that can move to another thread.
pub struct Snapshot(RootDatabase);

impl Snapshot {
    pub fn db(&self) -> &dyn Db {
        &self.0
    }
}

impl std::ops::Deref for Snapshot {
    type Target = dyn Db;

    fn deref(&self) -> &dyn Db {
        &self.0
    }
}

/// The reason a query stopped early: an input is about to change, so its
/// result would be out of date.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cancelled;

impl std::fmt::Display for Cancelled {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("the query was cancelled because an input is changing")
    }
}

impl std::error::Error for Cancelled {}

/// Stops the current query if an input is waiting to change. Salsa checks
/// this whenever one query calls another; long loops that call no queries,
/// such as compile-time evaluation, call it themselves.
///
/// It does not return when the query is cancelled: it unwinds to the nearest
/// [`catch_cancelled`].
pub fn check_cancelled(db: &dyn Db) {
    db.unwind_if_revision_cancelled();
}

/// Runs queries and reports whether they were cancelled. Callers on a
/// snapshot wrap their work in this and drop the snapshot on `Err`, which
/// lets the pending change proceed.
///
/// Other panics pass through.
pub fn catch_cancelled<T>(work: impl FnOnce() -> T) -> Result<T, Cancelled> {
    // The database stays consistent when a query unwinds: Salsa discards the
    // unfinished result.
    salsa::Cancelled::catch(AssertUnwindSafe(work)).map_err(|_| Cancelled)
}
