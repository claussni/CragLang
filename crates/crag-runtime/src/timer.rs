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

//! A hierarchical timing wheel (Plan §11.7.2), after Varghese and Lauck,
//! "Hashed and hierarchical timing wheels" (SOSP 1987).
//!
//! Time is counted in ticks of a millisecond since the wheel was made. The
//! wheel has [`LEVELS`] levels of [`SLOTS`] slots; a slot of level `l`
//! spans `64^l` ticks. A timer goes to the lowest level at which its tick
//! and the wheel's current tick agree in all higher digits, into the slot
//! of its own digit there, so the slots of a level that hold timers all lie
//! ahead of the current tick. When the wheel reaches a slot of a higher
//! level, it moves the slot's timers down a level or more, until they reach
//! level 0, whose slots are single ticks.
//!
//! Adding and cancelling take constant time. A cancelled timer leaves a
//! stale entry in its slot, which the wheel skips when it reaches the slot;
//! its generation tells it from a later timer that reuses its place.
//!
//! A timer never fires early: its deadline is rounded up to a tick, and the
//! current time down. A deadline farther than the wheel spans, about two
//! years, waits in the top level's farthest slot and is moved again when
//! the wheel gets there.

use std::time::{Duration, Instant};

/// The levels of the wheel.
pub const LEVELS: usize = 6;
/// The slots of a level.
pub const SLOTS: usize = 64;
const SLOT_BITS: u32 = 6;
/// The ticks the wheel spans: a timer is never placed farther ahead.
const SPAN: u64 = 1 << (SLOT_BITS * LEVELS as u32);
const TICK: Duration = Duration::from_millis(1);

/// A timer, for cancelling it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TimerId {
    index: u32,
    generation: u32,
}

/// A place in a slot: the timer and its generation when placed.
type Placed = (u32, u32);

struct Level {
    /// Bit `s` is set when slot `s` may hold timers.
    occupied: u64,
    slots: [Vec<Placed>; SLOTS],
}

struct Entry<T> {
    generation: u32,
    /// The tick the timer fires at.
    when: u64,
    /// None once fired or cancelled.
    value: Option<T>,
}

/// Timers that each fire a value at their deadline.
pub struct TimerWheel<T> {
    start: Instant,
    /// The tick up to which the wheel has fired its timers.
    elapsed: u64,
    levels: [Level; LEVELS],
    entries: Vec<Entry<T>>,
    free: Vec<u32>,
    len: usize,
}

impl<T> TimerWheel<T> {
    /// An empty wheel whose ticks count from `start`.
    pub fn new(start: Instant) -> TimerWheel<T> {
        TimerWheel {
            start,
            elapsed: 0,
            levels: std::array::from_fn(|_| Level {
                occupied: 0,
                slots: std::array::from_fn(|_| Vec::new()),
            }),
            entries: Vec::new(),
            free: Vec::new(),
            len: 0,
        }
    }

    /// The timers waiting to fire.
    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Adds a timer that fires `value` once the time reaches `deadline`; a
    /// deadline already past fires at the next advance.
    pub fn add(&mut self, deadline: Instant, value: T) -> TimerId {
        let when = deadline
            .checked_duration_since(self.start)
            .map_or(0, |d| d.as_nanos().div_ceil(TICK.as_nanos()))
            .min(u64::MAX as u128) as u64;
        let index = match self.free.pop() {
            Some(index) => {
                let entry = &mut self.entries[index as usize];
                entry.when = when;
                entry.value = Some(value);
                index
            }
            None => {
                self.entries.push(Entry {
                    generation: 0,
                    when,
                    value: Some(value),
                });
                (self.entries.len() - 1) as u32
            }
        };
        self.len += 1;
        self.place(index);
        TimerId {
            index,
            generation: self.entries[index as usize].generation,
        }
    }

    /// Cancels a timer that has not fired, giving back its value.
    pub fn cancel(&mut self, id: TimerId) -> Option<T> {
        let entry = self.entries.get_mut(id.index as usize)?;
        if entry.generation != id.generation {
            return None;
        }
        let value = entry.value.take()?;
        self.retire(id.index);
        Some(value)
    }

    /// Fires the timers whose deadlines `now` has reached, in the order of
    /// their deadlines.
    pub fn advance(&mut self, now: Instant) -> Vec<T> {
        let target = (now.saturating_duration_since(self.start).as_nanos() / TICK.as_nanos())
            .min(u64::MAX as u128) as u64;
        let mut fired = Vec::new();
        while let Some((level, slot, tick)) = self.next_expiration() {
            if tick > target {
                break;
            }
            self.elapsed = self.elapsed.max(tick);
            let placed = std::mem::take(&mut self.levels[level].slots[slot]);
            self.levels[level].occupied &= !(1 << slot);
            for (index, generation) in placed {
                let entry = &mut self.entries[index as usize];
                if entry.generation != generation || entry.value.is_none() {
                    continue;
                }
                if entry.when <= self.elapsed {
                    fired.push(entry.value.take().expect("live"));
                    self.retire(index);
                } else {
                    self.place(index);
                }
            }
        }
        self.elapsed = self.elapsed.max(target);
        fired
    }

    /// When the wheel next has to advance: the deadline of its next timer,
    /// or earlier, when timers have to move down a level first or a
    /// cancelled one leaves its slot to be cleared. None without timers.
    pub fn next_deadline(&self) -> Option<Instant> {
        if self.len == 0 {
            return None;
        }
        let (_, _, tick) = self.next_expiration()?;
        Some(self.start + Duration::from_millis(tick))
    }

    /// Takes every timer that has not fired, in no particular order.
    pub fn drain(&mut self) -> Vec<T> {
        for level in &mut self.levels {
            level.occupied = 0;
            level.slots.iter_mut().for_each(Vec::clear);
        }
        let values: Vec<T> = self
            .entries
            .iter_mut()
            .filter_map(|e| e.value.take())
            .collect();
        self.entries.clear();
        self.free.clear();
        self.len = 0;
        values
    }

    /// Puts timer `index` into the slot for its tick.
    fn place(&mut self, index: u32) {
        let entry = &self.entries[index as usize];
        let when = entry.when.clamp(self.elapsed, self.elapsed + (SPAN - 1));
        let level = level_for(self.elapsed, when);
        let slot = ((when >> (SLOT_BITS * level as u32)) as usize) & (SLOTS - 1);
        let level = &mut self.levels[level];
        level.slots[slot].push((index, entry.generation));
        level.occupied |= 1 << slot;
    }

    /// Frees the place of a timer that fired or was cancelled.
    fn retire(&mut self, index: u32) {
        let entry = &mut self.entries[index as usize];
        entry.generation = entry.generation.wrapping_add(1);
        self.free.push(index);
        self.len -= 1;
    }

    /// The next slot the wheel reaches that may hold timers, with the tick
    /// at which it reaches it. The slots of a lower level all come before
    /// those of a higher one.
    fn next_expiration(&self) -> Option<(usize, usize, u64)> {
        for (l, level) in self.levels.iter().enumerate() {
            if level.occupied == 0 {
                continue;
            }
            let slot_span = 1u64 << (SLOT_BITS * l as u32);
            let level_span = slot_span << SLOT_BITS;
            let current = ((self.elapsed / slot_span) as usize) & (SLOTS - 1);
            let ahead = level.occupied.rotate_right(current as u32).trailing_zeros() as usize;
            let slot = (current + ahead) % SLOTS;
            let level_start = self.elapsed & !(level_span - 1);
            let mut tick = level_start + slot as u64 * slot_span;
            if tick < self.elapsed && l > 0 {
                // Only the top level wraps: a slot behind the current one
                // lies in its next turn.
                tick += level_span;
            }
            return Some((l, slot, tick.max(self.elapsed)));
        }
        None
    }
}

/// The level for a timer at tick `when`: the highest digit in which it
/// differs from the current tick, but at least level 0 and at most the
/// top.
fn level_for(elapsed: u64, when: u64) -> usize {
    let differing = (elapsed ^ when) | (SLOTS as u64 - 1);
    let significant = 63 - differing.leading_zeros();
    ((significant / SLOT_BITS) as usize).min(LEVELS - 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ms(n: u64) -> Duration {
        Duration::from_millis(n)
    }

    #[test]
    fn timers_fire_in_the_order_of_their_deadlines_and_never_early() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        for (i, d) in [30, 5, 4100, 70, 5, 1].into_iter().enumerate() {
            wheel.add(start + ms(d), i);
        }
        assert_eq!(wheel.len(), 6);
        assert!(wheel.advance(start).is_empty());
        assert_eq!(wheel.advance(start + ms(4)), [5]);
        assert_eq!(wheel.advance(start + ms(5)), [1, 4]);
        assert!(wheel.advance(start + ms(29)).is_empty());
        assert_eq!(wheel.advance(start + ms(4099)), [0, 3]);
        assert_eq!(wheel.advance(start + ms(4100)), [2]);
        assert!(wheel.is_empty());
        assert_eq!(wheel.next_deadline(), None);
    }

    #[test]
    fn a_deadline_between_ticks_waits_for_the_next() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        wheel.add(start + Duration::from_micros(2500), ());
        assert!(
            wheel
                .advance(start + Duration::from_micros(2999))
                .is_empty()
        );
        assert_eq!(wheel.advance(start + ms(3)).len(), 1);
    }

    #[test]
    fn a_past_deadline_fires_at_the_next_advance() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start + ms(10));
        wheel.advance(start + ms(50));
        wheel.add(start, 'a');
        wheel.add(start + ms(20), 'b');
        assert_eq!(wheel.next_deadline(), Some(start + ms(50)));
        assert_eq!(wheel.advance(start + ms(50)), ['a', 'b']);
        // Far behind, in a digit above the lowest, it still fires at once.
        wheel.advance(start + ms(5000));
        wheel.add(start + ms(100), 'c');
        assert_eq!(wheel.advance(start + ms(5000)), ['c']);
    }

    #[test]
    fn a_cancelled_timer_does_not_fire_and_its_place_is_reused() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        let a = wheel.add(start + ms(10), 'a');
        assert_eq!(wheel.cancel(a), Some('a'));
        assert_eq!(wheel.cancel(a), None);
        assert!(wheel.is_empty());
        // The new timer takes the cancelled one's entry; the stale id
        // cannot cancel it, and the stale slot entry does not fire it.
        let b = wheel.add(start + ms(20), 'b');
        assert_eq!(wheel.cancel(a), None);
        assert!(wheel.advance(start + ms(15)).is_empty());
        assert_eq!(wheel.advance(start + ms(20)), ['b']);
        assert_eq!(wheel.cancel(b), None);
    }

    #[test]
    fn the_next_deadline_is_never_after_the_next_timer() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        wheel.add(start + ms(100_000), ());
        let next = wheel.next_deadline().unwrap();
        assert!(next <= start + ms(100_000));
        // Advancing to each deadline it gives reaches the timer.
        let mut steps = 0;
        while wheel.advance(wheel.next_deadline().unwrap()).is_empty() {
            steps += 1;
            assert!(steps < LEVELS * 2, "never reached");
        }
        assert!(wheel.is_empty());
    }

    #[test]
    fn deadlines_beyond_the_span_wait_and_fire() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        let far = ms(3 * SPAN + 12_345);
        wheel.add(start + far, 'f');
        wheel.add(start + ms(SPAN - 1), 'e');
        let mut fired = Vec::new();
        let mut steps = 0;
        while let Some(next) = wheel.next_deadline() {
            assert!(next <= start + far);
            fired.extend(wheel.advance(next));
            steps += 1;
            assert!(steps < 100, "never reached");
        }
        assert_eq!(fired, ['e', 'f']);
        // And at exactly their tick, not before.
        let mut wheel = TimerWheel::new(start);
        wheel.add(start + far, 'f');
        assert!(wheel.advance(start + far - ms(1)).is_empty());
        assert_eq!(wheel.advance(start + far), ['f']);
    }

    #[test]
    fn many_timers_fire_as_a_sorted_list_says() {
        // A pseudo-random mix of deadlines, cancellations and advances,
        // against a list kept sorted.
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        let mut reference: Vec<(u64, usize)> = Vec::new();
        let mut ids = Vec::new();
        let mut seed: u64 = 0x2545_f491_4f6c_dd1d;
        let mut next = || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut now = 0u64;
        for i in 0..20_000 {
            match next() % 10 {
                0..=5 => {
                    let delay = match next() % 4 {
                        0 => next() % 64,
                        1 => next() % 5000,
                        2 => next() % 400_000,
                        _ => next() % 30_000_000,
                    };
                    let id = wheel.add(start + ms(now + delay), i);
                    reference.push((now + delay, i));
                    ids.push((id, i));
                }
                6 if !ids.is_empty() => {
                    let (id, value) = ids.swap_remove((next() as usize) % ids.len());
                    let live = reference.iter().position(|&(_, v)| v == value);
                    assert_eq!(wheel.cancel(id), live.map(|_| value));
                    if let Some(p) = live {
                        reference.remove(p);
                    }
                }
                _ => {
                    now += match next() % 3 {
                        0 => next() % 10,
                        1 => next() % 10_000,
                        _ => next() % 2_000_000,
                    };
                    let mut fired = wheel.advance(start + ms(now));
                    let mut due: Vec<usize> = reference
                        .iter()
                        .filter(|&&(t, _)| t <= now)
                        .map(|&(_, v)| v)
                        .collect();
                    fired.sort_unstable();
                    due.sort_unstable();
                    assert_eq!(fired, due, "at {now}");
                    reference.retain(|&(t, _)| t > now);
                    assert_eq!(wheel.len(), reference.len());
                    if let Some(&(first, _)) = reference.iter().min() {
                        assert!(wheel.next_deadline().unwrap() <= start + ms(first));
                    }
                }
            }
        }
    }

    #[test]
    fn draining_takes_every_timer_left() {
        let start = Instant::now();
        let mut wheel = TimerWheel::new(start);
        let a = wheel.add(start + ms(5), 1);
        wheel.add(start + ms(5000), 2);
        wheel.add(start + ms(5_000_000), 3);
        wheel.cancel(a);
        let mut left = wheel.drain();
        left.sort_unstable();
        assert_eq!(left, [2, 3]);
        assert!(wheel.is_empty());
        assert!(wheel.advance(start + ms(10_000_000)).is_empty());
    }
}
