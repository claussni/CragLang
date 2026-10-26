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

//! A Chase–Lev work-stealing deque of words (Plan §11.7.1), with the memory
//! orderings of Lê, Pop, Cohen and Zappa Nardelli, "Correct and efficient
//! work-stealing for weak memory models" (PPoPP 2013).
//!
//! The owner pushes and takes at the bottom without locks; thieves steal
//! from the top with a compare-and-swap of `top`. The buffer is a ring that
//! the owner doubles when it is full. A thief may still read the old ring,
//! so old rings are kept until the deque is dropped: they total less than
//! the current one.

use std::sync::atomic::Ordering;

use crate::sync::{Arc, AtomicIsize, AtomicPtr, AtomicUsize, Mutex, fence};

/// A ring of slots, its length a power of two.
struct Ring {
    slots: Box<[AtomicUsize]>,
}

impl Ring {
    fn new(len: usize) -> Ring {
        Ring {
            slots: (0..len).map(|_| AtomicUsize::new(0)).collect(),
        }
    }

    fn len(&self) -> isize {
        self.slots.len() as isize
    }

    fn slot(&self, i: isize) -> &AtomicUsize {
        &self.slots[(i & (self.len() - 1)) as usize]
    }
}

struct Inner {
    top: AtomicIsize,
    bottom: AtomicIsize,
    ring: AtomicPtr<Ring>,
    /// Every ring the deque has had, the current one last. Boxed, since
    /// thieves hold pointers to them.
    #[allow(clippy::vec_box)]
    rings: Mutex<Vec<Box<Ring>>>,
}

/// The owner's end: push and take. One thread uses it at a time.
pub struct Deque {
    inner: Arc<Inner>,
}

/// A thief's end: steal. Any thread may use it.
#[derive(Clone)]
pub struct Stealer {
    inner: Arc<Inner>,
}

/// What a steal found.
#[derive(Debug, PartialEq, Eq)]
pub enum Steal {
    Empty,
    /// Another thread took the top first; trying again may succeed.
    Retry,
    Taken(usize),
}

#[cfg(not(loom))]
const INITIAL: usize = 64;
/// Small, so that a model grows the ring.
#[cfg(loom)]
const INITIAL: usize = 2;

impl Deque {
    pub fn new() -> (Deque, Stealer) {
        let mut ring = Box::new(Ring::new(INITIAL));
        let inner = Arc::new(Inner {
            top: AtomicIsize::new(0),
            bottom: AtomicIsize::new(0),
            ring: AtomicPtr::new(&raw mut *ring),
            rings: Mutex::new(vec![ring]),
        });
        let stealer = Stealer {
            inner: inner.clone(),
        };
        (Deque { inner }, stealer)
    }

    /// Adds a word at the bottom.
    pub fn push(&self, word: usize) {
        let inner = &*self.inner;
        let b = inner.bottom.load(Ordering::Relaxed);
        let t = inner.top.load(Ordering::Acquire);
        let mut ring = inner.ring.load(Ordering::Relaxed);
        // SAFETY: the ring is kept alive by `rings` until the deque drops.
        if b - t > unsafe { (*ring).len() } - 1 {
            ring = self.grow(b, t);
        }
        // SAFETY: as above.
        unsafe { (*ring).slot(b).store(word, Ordering::Relaxed) };
        fence(Ordering::Release);
        inner.bottom.store(b + 1, Ordering::Relaxed);
    }

    /// A ring of twice the length, holding the words from `t` to `b`.
    fn grow(&self, b: isize, t: isize) -> *mut Ring {
        let inner = &*self.inner;
        let old = inner.ring.load(Ordering::Relaxed);
        // SAFETY: the current ring is live.
        let old = unsafe { &*old };
        let mut ring = Box::new(Ring::new(2 * old.len() as usize));
        for i in t..b {
            ring.slot(i)
                .store(old.slot(i).load(Ordering::Relaxed), Ordering::Relaxed);
        }
        let ptr: *mut Ring = &raw mut *ring;
        inner.ring.store(ptr, Ordering::Release);
        inner.rings.lock().unwrap().push(ring);
        ptr
    }

    /// Takes the word at the bottom, the one pushed last.
    pub fn take(&self) -> Option<usize> {
        let inner = &*self.inner;
        let b = inner.bottom.load(Ordering::Relaxed) - 1;
        let ring = inner.ring.load(Ordering::Relaxed);
        inner.bottom.store(b, Ordering::Relaxed);
        fence(Ordering::SeqCst);
        let t = inner.top.load(Ordering::Relaxed);
        if t > b {
            inner.bottom.store(b + 1, Ordering::Relaxed);
            return None;
        }
        // SAFETY: the ring is live.
        let word = unsafe { (*ring).slot(b).load(Ordering::Relaxed) };
        if t < b {
            return Some(word);
        }
        // The last word: a thief may want it too.
        let won = inner
            .top
            .compare_exchange(t, t + 1, Ordering::SeqCst, Ordering::Relaxed)
            .is_ok();
        inner.bottom.store(b + 1, Ordering::Relaxed);
        won.then_some(word)
    }

    /// How many words it holds, as far as thieves let it know.
    pub fn len(&self) -> usize {
        let b = self.inner.bottom.load(Ordering::Relaxed);
        let t = self.inner.top.load(Ordering::Relaxed);
        (b - t).max(0) as usize
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl Stealer {
    /// Takes the word at the top, the oldest.
    pub fn steal(&self) -> Steal {
        let inner = &*self.inner;
        let t = inner.top.load(Ordering::Acquire);
        fence(Ordering::SeqCst);
        let b = inner.bottom.load(Ordering::Acquire);
        if t >= b {
            return Steal::Empty;
        }
        let ring = inner.ring.load(Ordering::Acquire);
        // SAFETY: every ring lives as long as the deque.
        let word = unsafe { (*ring).slot(t).load(Ordering::Relaxed) };
        match inner
            .top
            .compare_exchange(t, t + 1, Ordering::SeqCst, Ordering::Relaxed)
        {
            Ok(_) => Steal::Taken(word),
            Err(_) => Steal::Retry,
        }
    }

    /// Whether the deque looked empty.
    pub fn is_empty(&self) -> bool {
        let t = self.inner.top.load(Ordering::Acquire);
        let b = self.inner.bottom.load(Ordering::Acquire);
        t >= b
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn the_owner_takes_last_in_first_out_and_thieves_the_oldest() {
        let (deque, stealer) = Deque::new();
        for i in 1..=3 {
            deque.push(i);
        }
        assert_eq!(stealer.steal(), Steal::Taken(1));
        assert_eq!(deque.take(), Some(3));
        assert_eq!(deque.take(), Some(2));
        assert_eq!(deque.take(), None);
        assert_eq!(stealer.steal(), Steal::Empty);
    }

    #[test]
    fn the_ring_grows_and_keeps_every_word() {
        let (deque, stealer) = Deque::new();
        for i in 0..1000 {
            deque.push(i);
        }
        assert_eq!(deque.len(), 1000);
        for i in 0..500 {
            assert_eq!(stealer.steal(), Steal::Taken(i));
        }
        for i in (500..1000).rev() {
            assert_eq!(deque.take(), Some(i));
        }
        assert!(deque.is_empty());
    }

    #[test]
    fn concurrent_thieves_take_each_word_once() {
        const WORDS: usize = 200_000;
        let (deque, stealer) = Deque::new();
        let thieves: Vec<_> = (0..3)
            .map(|_| {
                let stealer = stealer.clone();
                std::thread::spawn(move || {
                    let mut got = Vec::new();
                    let mut empty = 0;
                    while empty < 1000 {
                        match stealer.steal() {
                            Steal::Taken(w) => {
                                got.push(w);
                                empty = 0;
                            }
                            Steal::Retry => {}
                            Steal::Empty => {
                                empty += 1;
                                std::thread::yield_now();
                            }
                        }
                    }
                    got
                })
            })
            .collect();
        let mut own = Vec::new();
        for i in 1..=WORDS {
            deque.push(i);
            // The owner takes some back, racing the thieves for the last.
            if i % 3 == 0
                && let Some(w) = deque.take()
            {
                own.push(w);
            }
        }
        while let Some(w) = deque.take() {
            own.push(w);
        }
        let mut seen: HashSet<usize> = own.into_iter().collect();
        let mut total = seen.len();
        for thief in thieves {
            for w in thief.join().unwrap() {
                assert!(seen.insert(w), "{w} taken twice");
                total += 1;
            }
        }
        assert_eq!(total, WORDS);
        assert_eq!(seen.len(), WORDS);
    }
}

/// Loom model (Plan §11.7.13): an owner pushes past the ring's size and
/// takes while a thief steals; every word comes out exactly once.
#[cfg(all(test, loom))]
mod loom_models {
    use super::*;

    #[test]
    fn loom_model_deque() {
        crate::sync::model(|| {
            let (deque, stealer) = Deque::new();
            let thief = loom::thread::spawn(move || {
                let mut got = Vec::new();
                for _ in 0..2 {
                    if let Steal::Taken(word) = stealer.steal() {
                        got.push(word);
                    }
                }
                got
            });
            for word in 1..=3 {
                deque.push(word);
            }
            let mut got = Vec::new();
            while let Some(word) = deque.take() {
                got.push(word);
            }
            got.extend(thief.join().unwrap());
            got.sort_unstable();
            assert_eq!(got, [1, 2, 3]);
        });
    }
}
