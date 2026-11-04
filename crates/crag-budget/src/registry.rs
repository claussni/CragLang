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

//! The budgets of a process: those it enforces as a receiver and those it
//! sends under, read from its budget directory once, at startup.
//!
//! In the directory, each document `name.json` with its salt `name.salt`
//! gives budgets to enforce, and each token file `*.token` a budget to
//! send under. Other files are left alone. A document without its salt is
//! an error, as is a budget two documents of one name both list.
//!
//! A receiving budget counts the steps its runs took since it was last
//! reset, the memory they hold now and the trees it admitted. Admitting
//! a tree ([`Registry::admit`]) checks its stamp: the MAC, a number past
//! the last one the budget admitted, and a run left. A run then takes its
//! steps and memory from the budget while it runs ([`Registry::reserve`]):
//! the policy's limits, or what is left of the budget where that is less,
//! so runs at the same time cannot overdraw it. Once it stopped, the steps
//! it did not use and all its memory go back ([`Grant::settle`]). A grant
//! dropped unsettled did not run and gives everything back.
//!
//! A sending budget counts the trees it stamped. It numbers them from the
//! clock, in nanoseconds, so a sender that starts again goes on past the
//! numbers its receivers saw.
//!
//! `renew` reads a budget's files again and takes their limits, and with
//! them a new token; what was taken stays. `reset` gives back what was
//! taken: steps and runs, never the memory runs hold now, nor the last
//! number admitted, so no stamp can be used twice.

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

use crate::document::{Document, KEY, Limits, Origin, TokenFile, unhex};
use crate::message::{Stamp, mac, same_mac};

/// Which of a process's budgets: those it enforces or those it sends
/// under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Side {
    Receiving,
    Sending,
}

/// What a budget has taken: steps and runs since it was last reset, and
/// the memory its runs hold now. A sender knows only the runs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Usage {
    pub steps: Option<u64>,
    pub memory: Option<u64>,
    pub runs: u64,
}

/// Why a budget does not admit or run code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// No stamp, or one the receiver cannot verify.
    Unbudgeted(String),
    /// The receiving budget of this index is used up.
    Limit { index: usize, origin: Origin },
}

/// The budgets of a process.
#[derive(Default)]
pub struct Registry {
    receiving: Vec<Arc<Receiving>>,
    sending: Vec<Sending>,
}

/// A budget the process enforces.
struct Receiving {
    document: PathBuf,
    salt: PathBuf,
    state: Mutex<Enforced>,
}

#[derive(Debug)]
struct Enforced {
    origin: Origin,
    limits: Limits,
    token: [u8; KEY],
    /// Steps taken since the last reset, memory held now, trees admitted.
    steps: u64,
    memory: u64,
    runs: u64,
    /// The steps granted to the runs not yet stopped, which a reset keeps.
    held: u64,
    /// The number of the last stamp admitted.
    last: u64,
}

/// A budget the process sends under.
struct Sending {
    file: PathBuf,
    state: Mutex<TokenFile>,
    runs: AtomicU64,
    next: AtomicU64,
}

fn lock<T>(m: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

fn read(path: &Path) -> Result<String, String> {
    std::fs::read_to_string(path).map_err(|e| format!("cannot read {}: {e}", path.display()))
}

/// The document and salt at these paths.
fn document(document: &Path, salt: &Path) -> Result<(Document, [u8; KEY]), String> {
    let parsed = Document::parse(&read(document)?)
        .map_err(|why| format!("{}: {why}", document.display()))?;
    let key = unhex(&read(salt)?)
        .ok_or_else(|| format!("{}: does not hold 64 hex digits", salt.display()))?;
    Ok((parsed, key))
}

fn token_file(path: &Path) -> Result<TokenFile, String> {
    TokenFile::parse(&read(path)?).map_err(|why| format!("{}: {why}", path.display()))
}

impl Registry {
    /// The budgets of the directory at `dir`.
    pub fn load(dir: &Path) -> Result<Registry, String> {
        let entries = std::fs::read_dir(dir)
            .map_err(|e| format!("cannot read the budget directory {}: {e}", dir.display()))?;
        let mut paths: Vec<PathBuf> = entries
            .filter_map(|e| e.ok().map(|e| e.path()))
            .filter(|p| p.is_file())
            .collect();
        paths.sort();
        let mut registry = Registry::default();
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map_or(1, |d| d.as_nanos() as u64)
            .max(1);
        for path in &paths {
            match path.extension().and_then(|e| e.to_str()) {
                Some("json") => {
                    let salt = path.with_extension("salt");
                    if !salt.is_file() {
                        return Err(format!("{} has no salt {}", path.display(), salt.display()));
                    }
                    let (doc, key) = document(path, &salt)?;
                    for (name, limits) in &doc.budgets {
                        let origin = doc.budget(name).expect("listed").0;
                        if registry.find(&origin.document, name).is_some() {
                            return Err(format!(
                                "two documents named `{}` list budget `{name}`",
                                origin.document
                            ));
                        }
                        registry.receiving.push(Arc::new(Receiving {
                            document: path.clone(),
                            salt: salt.clone(),
                            state: Mutex::new(Enforced {
                                origin,
                                limits: *limits,
                                token: doc.token(&key, name),
                                steps: 0,
                                memory: 0,
                                runs: 0,
                                held: 0,
                                last: 0,
                            }),
                        }));
                    }
                }
                Some("token") => {
                    let file = token_file(path)?;
                    registry.sending.push(Sending {
                        file: path.clone(),
                        state: Mutex::new(file),
                        runs: AtomicU64::new(0),
                        next: AtomicU64::new(now),
                    });
                }
                _ => {}
            }
        }
        Ok(registry)
    }

    /// The process's budgets of one side.
    pub fn count(&self, side: Side) -> usize {
        match side {
            Side::Receiving => self.receiving.len(),
            Side::Sending => self.sending.len(),
        }
    }

    fn find(&self, document: &str, name: &str) -> Option<usize> {
        self.receiving.iter().position(|b| {
            let s = lock(&b.state);
            s.origin.document == document && s.origin.name == name
        })
    }

    /// A budget's origin and limits.
    pub fn describe(&self, side: Side, index: usize) -> Option<(Origin, Limits)> {
        match side {
            Side::Receiving => {
                let s = lock(&self.receiving.get(index)?.state);
                Some((s.origin.clone(), s.limits))
            }
            Side::Sending => {
                let s = lock(&self.sending.get(index)?.state);
                Some((s.origin.clone(), s.limits))
            }
        }
    }

    /// What a budget has taken.
    pub fn usage(&self, side: Side, index: usize) -> Option<Usage> {
        match side {
            Side::Receiving => {
                let s = lock(&self.receiving.get(index)?.state);
                Some(Usage {
                    steps: Some(s.steps),
                    memory: Some(s.memory),
                    runs: s.runs,
                })
            }
            Side::Sending => Some(Usage {
                steps: None,
                memory: None,
                runs: self.sending.get(index)?.runs.load(Ordering::Relaxed),
            }),
        }
    }

    /// Reads a budget's files again and takes their limits and token;
    /// what it has taken stays.
    pub fn renew(&self, side: Side, index: usize) -> Result<(), String> {
        match side {
            Side::Receiving => {
                let b = self.receiving.get(index).ok_or("no such budget")?;
                let (doc, key) = document(&b.document, &b.salt)?;
                let mut s = lock(&b.state);
                let name = s.origin.name.clone();
                let (origin, limits) = doc.budget(&name).ok_or_else(|| {
                    format!("{} no longer lists budget `{name}`", b.document.display())
                })?;
                if origin.document != s.origin.document {
                    return Err(format!(
                        "{} is now named `{}`, not `{}`",
                        b.document.display(),
                        origin.document,
                        s.origin.document
                    ));
                }
                s.origin = origin;
                s.limits = limits;
                s.token = doc.token(&key, &name);
                Ok(())
            }
            Side::Sending => {
                let b = self.sending.get(index).ok_or("no such budget")?;
                let file = token_file(&b.file)?;
                *lock(&b.state) = file;
                Ok(())
            }
        }
    }

    /// Gives back what a budget has taken: its runs and the steps of the
    /// runs that stopped. Runs still going keep their steps and memory.
    pub fn reset(&self, side: Side, index: usize) -> bool {
        match side {
            Side::Receiving => match self.receiving.get(index) {
                Some(b) => {
                    let mut s = lock(&b.state);
                    s.steps = s.held;
                    s.runs = 0;
                    true
                }
                None => false,
            },
            Side::Sending => match self.sending.get(index) {
                Some(b) => {
                    b.runs.store(0, Ordering::Relaxed);
                    true
                }
                None => false,
            },
        }
    }

    /// Stamps code with a sending budget, with a number past every one
    /// before.
    pub fn stamp(&self, index: usize, tree: &[u8], env: &[u8]) -> Option<Stamp> {
        let b = self.sending.get(index)?;
        let s = lock(&b.state);
        let sequence = b.next.fetch_add(1, Ordering::Relaxed);
        b.runs.fetch_add(1, Ordering::Relaxed);
        Some(Stamp {
            document: s.origin.document.clone(),
            budget: s.origin.name.clone(),
            sequence,
            mac: mac(&s.token, tree, env, sequence),
        })
    }

    /// Admits stamped code: the receiving budget it runs under, none when
    /// the process enforces no budget.
    pub fn admit(
        &self,
        stamp: Option<&Stamp>,
        tree: &[u8],
        env: &[u8],
    ) -> Result<Option<usize>, Refusal> {
        if self.receiving.is_empty() {
            return Ok(None);
        }
        let Some(stamp) = stamp else {
            return Err(Refusal::Unbudgeted(
                "the code carries no budget's stamp".into(),
            ));
        };
        let Some(index) = self.find(&stamp.document, &stamp.budget) else {
            return Err(Refusal::Unbudgeted(format!(
                "no budget `{}` of document `{}`",
                stamp.budget, stamp.document
            )));
        };
        let mut s = lock(&self.receiving[index].state);
        let expected = mac(&s.token, tree, env, stamp.sequence);
        if !same_mac(&expected, &stamp.mac) {
            return Err(Refusal::Unbudgeted(format!(
                "the stamp of budget `{}` is not valid",
                stamp.budget
            )));
        }
        if stamp.sequence <= s.last {
            return Err(Refusal::Unbudgeted(format!(
                "budget `{}` admitted this stamp's number already",
                stamp.budget
            )));
        }
        if s.limits.runs.is_some_and(|r| s.runs >= r) {
            let origin = s.origin.clone();
            return Err(Refusal::Limit { index, origin });
        }
        s.last = stamp.sequence;
        s.runs += 1;
        Ok(Some(index))
    }

    /// Takes a run's steps and memory from a receiving budget: the
    /// policy's, or what is left where that is less.
    pub fn reserve(&self, index: usize, steps: u64, memory: u64) -> Result<Grant, Refusal> {
        let budget = self
            .receiving
            .get(index)
            .ok_or_else(|| Refusal::Unbudgeted("no such budget".into()))?;
        let mut s = lock(&budget.state);
        let steps_left = s.limits.steps.map(|l| l.saturating_sub(s.steps));
        let memory_left = s.limits.memory.map(|l| l.saturating_sub(s.memory));
        if steps_left == Some(0) || memory_left == Some(0) {
            let origin = s.origin.clone();
            return Err(Refusal::Limit { index, origin });
        }
        let granted_steps = steps_left.map_or(steps, |l| l.min(steps));
        let granted_memory = memory_left.map_or(memory, |l| l.min(memory));
        s.steps += granted_steps;
        s.held += granted_steps;
        s.memory += granted_memory;
        Ok(Grant {
            budget: budget.clone(),
            origin: s.origin.clone(),
            steps: granted_steps,
            memory: granted_memory,
            steps_capped: granted_steps < steps,
            memory_capped: granted_memory < memory,
            settled: false,
        })
    }
}

/// The steps and memory a run took from its budget, until it stopped.
pub struct Grant {
    budget: Arc<Receiving>,
    pub origin: Origin,
    pub steps: u64,
    pub memory: u64,
    /// Whether the budget, not the policy, set the limit.
    pub steps_capped: bool,
    pub memory_capped: bool,
    settled: bool,
}

impl Grant {
    /// The run stopped with `steps_left` of the steps granted: the rest
    /// stays taken, the memory goes back.
    pub fn settle(mut self, steps_left: u64) {
        self.settled = true;
        self.give_back(steps_left.min(self.steps));
    }

    fn give_back(&self, steps: u64) {
        let mut s = lock(&self.budget.state);
        s.held -= self.steps;
        s.steps -= steps;
        s.memory -= self.memory;
    }
}

impl Drop for Grant {
    /// Unsettled, the code did not run: everything goes back.
    fn drop(&mut self) {
        if !self.settled {
            self.give_back(self.steps);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::document::hex;
    use crate::document::tests::{DOCUMENT, SALT};

    /// A directory with the document, its salt and its tokens.
    fn directory(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("crag-budget-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("partners.json"), DOCUMENT).unwrap();
        std::fs::write(dir.join("partners.salt"), hex(&SALT)).unwrap();
        let doc = Document::parse(DOCUMENT).unwrap();
        for (budget, text) in doc.token_files(&SALT) {
            std::fs::write(dir.join(format!("partners-{budget}.token")), text).unwrap();
        }
        dir
    }

    #[test]
    fn a_directory_gives_both_sides() {
        let dir = directory("sides");
        let r = Registry::load(&dir).unwrap();
        assert_eq!((r.count(Side::Receiving), r.count(Side::Sending)), (2, 2));
        let (origin, limits) = r.describe(Side::Sending, 0).unwrap();
        assert_eq!((origin.name.as_str(), limits.steps), ("acme", Some(1000)));
        // A document without its salt is an error.
        std::fs::remove_file(dir.join("partners.salt")).unwrap();
        assert!(Registry::load(&dir).err().unwrap().contains("no salt"));
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn a_stamp_is_verified_and_admitted_once() {
        let dir = directory("stamps");
        let r = Registry::load(&dir).unwrap();
        let stamp = r.stamp(0, b"t", b"e").unwrap();
        assert_eq!(r.admit(Some(&stamp), b"t", b"e"), Ok(Some(0)));
        assert_eq!(r.usage(Side::Sending, 0).unwrap().runs, 1);
        assert_eq!(r.usage(Side::Receiving, 0).unwrap().runs, 1);
        let again = r.admit(Some(&stamp), b"t", b"e");
        assert!(matches!(again, Err(Refusal::Unbudgeted(m)) if m.contains("already")));
        // Other captures under the stamp, no stamp, and a stamp of a
        // budget the receiver lacks are refused.
        let stamp = r.stamp(0, b"t", b"e").unwrap();
        let other = r.admit(Some(&stamp), b"t", b"f");
        assert!(matches!(other, Err(Refusal::Unbudgeted(m)) if m.contains("not valid")));
        assert!(r.admit(None, b"t", b"e").is_err());
        let unknown = Stamp {
            document: "x".into(),
            ..stamp
        };
        let e = r.admit(Some(&unknown), b"t", b"e");
        assert!(matches!(e, Err(Refusal::Unbudgeted(m)) if m.contains("no budget")));
        // A process that enforces no budget ignores stamps.
        assert_eq!(Registry::default().admit(None, b"t", b"e"), Ok(None));
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn runs_take_steps_and_hold_memory_until_they_stop() {
        let dir = directory("grants");
        let r = Registry::load(&dir).unwrap();
        let first = r.reserve(0, 600, 3000).unwrap();
        assert!(!first.steps_capped && !first.memory_capped);
        let second = r.reserve(0, 600, 3000).unwrap();
        assert_eq!((second.steps, second.memory), (400, 1096));
        assert!(second.steps_capped && second.memory_capped);
        assert_eq!(second.origin.name, "acme");
        first.settle(100);
        second.settle(400);
        let used = r.usage(Side::Receiving, 0).unwrap();
        assert_eq!((used.steps, used.memory), (Some(500), Some(0)));
        // Dropped unsettled, a grant gives everything back.
        drop(r.reserve(0, 10, 10).unwrap());
        assert_eq!(r.usage(Side::Receiving, 0).unwrap().steps, Some(500));
        // Used up, then reset.
        r.reserve(0, 500, 1).unwrap().settle(0);
        let e = r.reserve(0, 1, 1).err().unwrap();
        assert!(matches!(e, Refusal::Limit { index: 0, origin } if origin.name == "acme"));
        assert!(r.reset(Side::Receiving, 0));
        assert_eq!(r.usage(Side::Receiving, 0).unwrap().steps, Some(0));
        r.reserve(0, 1, 1).unwrap().settle(0);
        // Runs are counted at admission.
        for _ in 0..3 {
            let s = r.stamp(0, b"t", b"e").unwrap();
            r.admit(Some(&s), b"t", b"e").unwrap();
        }
        let s = r.stamp(0, b"t", b"e").unwrap();
        assert!(matches!(
            r.admit(Some(&s), b"t", b"e"),
            Err(Refusal::Limit { .. })
        ));
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn reset_keeps_held_memory_and_the_last_number() {
        let dir = directory("reset");
        let r = Registry::load(&dir).unwrap();
        let stamp = r.stamp(0, b"t", b"e").unwrap();
        r.admit(Some(&stamp), b"t", b"e").unwrap();
        r.reserve(0, 300, 1).unwrap().settle(0);
        let running = r.reserve(0, 100, 3000).unwrap();
        assert!(r.reset(Side::Receiving, 0));
        assert!(r.reset(Side::Sending, 0));
        let used = r.usage(Side::Receiving, 0).unwrap();
        assert_eq!(
            (used.steps, used.memory, used.runs),
            (Some(100), Some(3000), 0)
        );
        assert_eq!(r.usage(Side::Sending, 0).unwrap().runs, 0);
        // The running run's memory is still held, so a second run gets
        // only what is left.
        assert_eq!(r.reserve(0, 1, 3000).unwrap().memory, 1096);
        // What it leaves of its steps goes back when it ends.
        running.settle(60);
        assert_eq!(r.usage(Side::Receiving, 0).unwrap().steps, Some(40));
        assert!(r.reset(Side::Receiving, 0));
        assert_eq!(r.usage(Side::Receiving, 0).unwrap().steps, Some(0));
        // A replay stays refused.
        let again = r.admit(Some(&stamp), b"t", b"e");
        assert!(matches!(again, Err(Refusal::Unbudgeted(m)) if m.contains("already")));
        assert!(!r.reset(Side::Receiving, 9));
        let _ = std::fs::remove_dir_all(dir);
    }

    #[test]
    fn renew_takes_new_limits_and_keeps_what_was_taken() {
        let dir = directory("renew");
        let r = Registry::load(&dir).unwrap();
        r.reserve(0, 300, 1).unwrap().settle(0);
        let renewed = DOCUMENT.replace("1000", "5000");
        std::fs::write(dir.join("partners.json"), &renewed).unwrap();
        r.renew(Side::Receiving, 0).unwrap();
        assert_eq!(r.describe(Side::Receiving, 0).unwrap().1.steps, Some(5000));
        assert_eq!(r.usage(Side::Receiving, 0).unwrap().steps, Some(300));
        // The old token no longer verifies; a renewed sender's does.
        let old = r.stamp(0, b"t", b"e").unwrap();
        assert!(r.admit(Some(&old), b"t", b"e").is_err());
        let doc = Document::parse(&renewed).unwrap();
        for (budget, text) in doc.token_files(&SALT) {
            std::fs::write(dir.join(format!("partners-{budget}.token")), text).unwrap();
        }
        r.renew(Side::Sending, 0).unwrap();
        let new = r.stamp(0, b"t", b"e").unwrap();
        assert_eq!(r.admit(Some(&new), b"t", b"e"), Ok(Some(0)));
        // A budget the document drops cannot be renewed.
        std::fs::write(
            dir.join("partners.json"),
            renewed.replace("acme", "initech"),
        )
        .unwrap();
        assert!(
            r.renew(Side::Receiving, 0)
                .unwrap_err()
                .contains("no longer")
        );
        let _ = std::fs::remove_dir_all(dir);
    }
}
