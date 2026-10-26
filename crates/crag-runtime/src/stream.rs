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

//! Streams and hubs (Plan §11.7.5, Specification §10.5–10.6).
//!
//! One channel serves all three: a stream is a fan-out with one producer
//! and one consumer, sealed from the start, whose producer learns when the
//! consumer goes. A stream or a fan-out has one buffer, from which each
//! value goes to one consumer; a broadcast has a buffer per consumer and
//! hands each value to all of them, with a reference each.
//!
//! A put that finds a consumer waiting hands the value over, writing it
//! where the consumer asked; otherwise it goes into the buffer while there
//! is room, and else the producer waits with it. A consumer that takes a
//! value from the buffer lets the oldest waiting put in. With a capacity of
//! zero there is no buffer: a value goes only to a consumer that waits, or
//! one takes it from a waiting put, which is a hand-off.
//!
//! The ends belong to the generated code, one owner each. Closing an end
//! ends the stream deliberately; disposing one that was not closed
//! abandons it, so the other side reads `Abandoned` (§10.5.2). The
//! runtime knows the values' layout from a list type, to release those no
//! one will take. Values still in the buffer when the channel is freed
//! without a consumer leaving, which only a scheduler's shutdown does,
//! are not released.
//!
//! Waiting puts and takes are suspension points where cancellation takes
//! effect (§11.7.4): a cancelled wait leaves the channel, and the value of
//! a cancelled put stays with its frame, which the unwinder releases.

use std::collections::{HashMap, VecDeque};
use std::sync::{Arc, Mutex};

use crag_abi::{
    ElementLayout, HUB_BROADCAST, STREAM_ABANDONED, STREAM_CLOSED, STREAM_FULL, STREAM_OK, TrapKind,
};

use crate::cancel::{Waiting, raise, stop_if_due, wait_for};
use crate::die;
use crate::fiber::TaskContext;
use crate::heap::Heap;
use crate::io::Words;
use crate::rc::{Types, release_value, retain_value};
use crate::sched::{FiberRef, WaitReason, scheduler_of, suspend, wake};
use crate::system::worker_of;

/// The words of a value, as far as its layout has words.
type Value = [u64; 2];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    Stream,
    FanOut,
    Broadcast,
}

/// A stream or a hub.
pub(crate) struct Channel {
    kind: Kind,
    capacity: usize,
    layout: ElementLayout,
    state: Mutex<State>,
}

// SAFETY: the values and the places to write them belong to suspended
// fibers or to the channel, and the lock hands them to one thread at a
// time.
unsafe impl Send for Channel {}
unsafe impl Sync for Channel {}

struct State {
    /// The buffer of a stream or a fan-out.
    queue: VecDeque<Value>,
    consumers: HashMap<u64, Consumer>,
    /// The consumers of a stream or a fan-out waiting for a value, in the
    /// order they came.
    waiting: VecDeque<u64>,
    /// Puts waiting for room, oldest first.
    pending: VecDeque<Pending>,
    /// Producers that have not left.
    producers: usize,
    /// Set once no producer can join.
    sealed: bool,
    /// Set once a producer left without closing.
    abandoned: bool,
    /// Whether the hub's handle is held, so that consumers may still join.
    joinable: bool,
    /// Set once no consumer will ever take a value: what puts then give.
    orphaned: Option<u64>,
    /// Consumers of a fan-out still to read `Closed`, from `release`.
    released: usize,
    /// Numbers consumers and waits.
    next_id: u64,
}

struct Consumer {
    /// The buffer of a broadcast's consumer.
    queue: VecDeque<Value>,
    waiter: Option<Waiter>,
}

/// A consumer suspended until a value comes.
struct Waiter {
    fiber: FiberRef,
    /// Where the value goes.
    out: *mut u64,
    token: u64,
}

/// A put suspended until there is room.
struct Pending {
    fiber: FiberRef,
    value: Value,
    token: u64,
}

enum Role {
    Producer,
    Consumer(u64),
}

/// An end of a stream or of a hub, which generated code holds.
pub(crate) struct End {
    chan: Arc<Channel>,
    role: Role,
    closed: bool,
}

/// Fibers to wake once the lock is released, with their status.
type Wakes = Vec<(FiberRef, u64)>;

impl Channel {
    fn new(kind: Kind, capacity: usize, layout: ElementLayout) -> Channel {
        Channel {
            kind,
            capacity,
            layout,
            state: Mutex::new(State {
                queue: VecDeque::new(),
                consumers: HashMap::new(),
                waiting: VecDeque::new(),
                pending: VecDeque::new(),
                producers: 0,
                sealed: false,
                abandoned: false,
                joinable: kind != Kind::Stream,
                orphaned: None,
                released: 0,
                next_id: 0,
            }),
        }
    }

    /// Writes a value where a waiting consumer asked for it, and wakes it.
    fn hand(&self, waiter: Waiter, value: Value, wakes: &mut Wakes) {
        // SAFETY: the place stays where it is while its fiber waits.
        unsafe {
            for (i, &word) in value.iter().enumerate().take(self.layout.words as usize) {
                waiter.out.add(i).write(word);
            }
        }
        wakes.push((waiter.fiber, STREAM_OK));
    }

    /// Writes a value where the calling consumer asked for it.
    fn give(&self, out: *mut u64, value: Value) {
        // SAFETY: generated code passes a place for the words.
        unsafe {
            for (i, &word) in value.iter().enumerate().take(self.layout.words as usize) {
                out.add(i).write(word);
            }
        }
    }

    /// Gives up the references of a value no one will take.
    fn discard(&self, heap: &mut Heap, types: &Types, mut value: Value) {
        // SAFETY: the channel owns the value.
        unsafe { release_value(heap, types, value.as_mut_ptr().cast(), &self.layout) }
    }

    /// Whether a broadcast may put a value now: every consumer has room,
    /// or waits for it.
    fn room_for_all(&self, state: &State) -> bool {
        state
            .consumers
            .values()
            .all(|c| c.queue.len() < self.capacity || (c.queue.is_empty() && c.waiter.is_some()))
    }

    /// Hands a value to every consumer of a broadcast, with a reference
    /// each; with none, it is released.
    fn broadcast(
        &self,
        state: &mut State,
        mut value: Value,
        heap: &mut Heap,
        types: &Types,
        wakes: &mut Wakes,
    ) {
        let n = state.consumers.len();
        if n == 0 {
            self.discard(heap, types, value);
            return;
        }
        for _ in 1..n {
            // SAFETY: the channel holds a reference to the value.
            unsafe { retain_value(value.as_mut_ptr().cast(), &self.layout) };
        }
        for consumer in state.consumers.values_mut() {
            match consumer.waiter.take() {
                Some(waiter) => self.hand(waiter, value, wakes),
                None => consumer.queue.push_back(value),
            }
        }
    }

    /// Lets in the waiting puts there is now room for.
    fn admit(&self, state: &mut State, heap: &mut Heap, types: &Types, wakes: &mut Wakes) {
        if self.kind == Kind::Broadcast {
            while !state.pending.is_empty() && self.room_for_all(state) {
                let p = state.pending.pop_front().expect("not empty");
                self.broadcast(state, p.value, heap, types, wakes);
                wakes.push((p.fiber, STREAM_OK));
            }
        } else {
            while state.queue.len() < self.capacity
                && let Some(p) = state.pending.pop_front()
            {
                state.queue.push_back(p.value);
                wakes.push((p.fiber, STREAM_OK));
            }
        }
    }

    /// What consumers read once the buffer is empty, if the producers are
    /// gone.
    fn ended(state: &State) -> Option<u64> {
        (state.sealed && state.producers == 0).then_some(if state.abandoned {
            STREAM_ABANDONED
        } else {
            STREAM_CLOSED
        })
    }

    /// Wakes the waiting consumers with the end, if the stream has ended.
    fn end_waiting(state: &mut State, wakes: &mut Wakes) {
        let Some(status) = Channel::ended(state) else {
            return;
        };
        state.waiting.clear();
        for consumer in state.consumers.values_mut() {
            if let Some(waiter) = consumer.waiter.take() {
                wakes.push((waiter.fiber, status));
            }
        }
    }

    /// No consumer will take a value any more: the buffer is released, and
    /// the waiting puts and later ones give `status`.
    fn orphan(
        &self,
        state: &mut State,
        status: u64,
        heap: &mut Heap,
        types: &Types,
        wakes: &mut Wakes,
    ) {
        state.orphaned = Some(status);
        for value in std::mem::take(&mut state.queue) {
            self.discard(heap, types, value);
        }
        for p in state.pending.drain(..) {
            wakes.push((p.fiber, status));
        }
    }

    /// An end leaves: deliberately when it was closed.
    fn leave(&self, role: &Role, deliberate: bool, heap: &mut Heap, types: &Types) {
        let mut wakes = Wakes::new();
        let mut state = self.state.lock().unwrap();
        match *role {
            Role::Producer => {
                state.producers -= 1;
                state.abandoned |= !deliberate;
                Channel::end_waiting(&mut state, &mut wakes);
            }
            Role::Consumer(id) => {
                let consumer = state.consumers.remove(&id).expect("a consumer");
                for value in consumer.queue {
                    self.discard(heap, types, value);
                }
                match self.kind {
                    Kind::Stream => {
                        let status = if deliberate {
                            STREAM_CLOSED
                        } else {
                            STREAM_ABANDONED
                        };
                        self.orphan(&mut state, status, heap, types, &mut wakes);
                    }
                    _ if state.consumers.is_empty() && !state.joinable => {
                        self.orphan(&mut state, STREAM_CLOSED, heap, types, &mut wakes);
                    }
                    // The slowest consumer of a broadcast may have gone.
                    Kind::Broadcast => self.admit(&mut state, heap, types, &mut wakes),
                    Kind::FanOut => {}
                }
            }
        }
        drop(state);
        wake_all(wakes);
    }

    /// Calls off the wait with `token`, giving its fiber back; none when it
    /// no longer waits.
    pub(crate) fn call_off(&self, token: u64) -> Option<FiberRef> {
        let mut state = self.state.lock().unwrap();
        if let Some(at) = state.pending.iter().position(|p| p.token == token) {
            return state.pending.remove(at).map(|p| p.fiber);
        }
        let (&id, consumer) = state
            .consumers
            .iter_mut()
            .find(|(_, c)| c.waiter.as_ref().is_some_and(|w| w.token == token))?;
        let waiter = consumer.waiter.take().expect("found");
        state.waiting.retain(|&w| w != id);
        Some(waiter.fiber)
    }
}

fn wake_all(wakes: Wakes) {
    for (fiber, status) in wakes {
        wake(fiber, [status, 0]);
    }
}

/// A new end, as the word generated code holds.
fn end(chan: Arc<Channel>, role: Role, closed: bool) -> u64 {
    Box::into_raw(Box::new(End { chan, role, closed })) as u64
}

system_stack_fn! {
    /// `rt_stream_new(ctx, capacity, list) -> (sink, source)`: see
    /// `crag_abi::RuntimeFn::StreamNew`.
    fn rt_stream_new(ctx: *const TaskContext, capacity: u64, list: u64) -> Words => new_entry
}

/// The Rust half of `rt_stream_new`.
///
/// # Safety
///
/// Called only by `rt_stream_new`.
unsafe extern "C" fn new_entry(ctx: *const TaskContext, capacity: u64, list: u64) -> Words {
    // SAFETY: as the caller promises.
    let (_, types) = unsafe { worker_of(ctx) };
    let chan = Arc::new(Channel::new(
        Kind::Stream,
        capacity as usize,
        types.element_of(list).clone(),
    ));
    {
        let mut state = chan.state.lock().unwrap();
        state.producers = 1;
        state.sealed = true;
        state.consumers.insert(
            0,
            Consumer {
                queue: VecDeque::new(),
                waiter: None,
            },
        );
        state.next_id = 1;
    }
    let sink = end(chan.clone(), Role::Producer, false);
    let source = end(chan, Role::Consumer(0), false);
    Words(sink, source)
}

/// Puts a value from the sink at `end`: its status, or none when the
/// fiber suspends with it.
///
/// # Safety
///
/// Called by the Rust half of a runtime function for the fiber of `ctx`,
/// with a sink that has not been disposed.
unsafe fn put(ctx: &TaskContext, end: *mut End, value: Value, wait: bool) -> Option<u64> {
    // SAFETY: as the caller promises.
    let (end, (heap, types)) = unsafe { (&*end, worker_of(ctx)) };
    if end.closed {
        return Some(STREAM_CLOSED);
    }
    let chan = &*end.chan;
    let mut wakes = Wakes::new();
    let mut state = chan.state.lock().unwrap();
    let status = 'put: {
        if let Some(status) = state.orphaned {
            break 'put Some(status);
        }
        if chan.kind == Kind::Broadcast {
            if chan.room_for_all(&state) {
                chan.broadcast(&mut state, value, heap, types, &mut wakes);
                break 'put Some(STREAM_OK);
            }
        } else if let Some(id) = state.waiting.pop_front() {
            let waiter = state
                .consumers
                .get_mut(&id)
                .and_then(|c| c.waiter.take())
                .expect("a waiting consumer");
            chan.hand(waiter, value, &mut wakes);
            break 'put Some(STREAM_OK);
        } else if state.queue.len() < chan.capacity {
            state.queue.push_back(value);
            break 'put Some(STREAM_OK);
        }
        if !wait {
            break 'put Some(STREAM_FULL);
        }
        // SAFETY: as the caller promises.
        if unsafe { scheduler_of(ctx) }.is_none() {
            raise(ctx, TrapKind::Unsupported, None);
            break 'put Some(STREAM_OK);
        }
        let token = state.next_id;
        state.next_id += 1;
        // SAFETY: as the caller promises.
        let fiber = unsafe { suspend(ctx, WaitReason::Stream) };
        state.pending.push_back(Pending {
            fiber,
            value,
            token,
        });
        drop(state);
        wake_all(wakes);
        wait_for(
            ctx,
            Waiting::Stream {
                chan: end.chan.clone(),
                token,
            },
        );
        return None;
    };
    drop(state);
    wake_all(wakes);
    status
}

suspending_fn! {
    /// `rt_stream_put(ctx, sink, w0, w1) -> status`: see
    /// `crag_abi::RuntimeFn::StreamPut`.
    fn rt_stream_put(ctx: *const TaskContext, end: *mut End, w0: u64, w1: u64) -> u64 => put_entry
}

/// The Rust half of `rt_stream_put`: suspends while there is no room.
///
/// # Safety
///
/// Called only by `rt_stream_put`, with a sink that has not been disposed.
unsafe extern "C" fn put_entry(ctx: *const TaskContext, end: *mut End, w0: u64, w1: u64) -> u64 {
    // SAFETY: as the caller promises.
    unsafe {
        let ctx = &*ctx;
        if stop_if_due(ctx) {
            return 0;
        }
        // The wake gives the status of a put that waits.
        put(ctx, end, [w0, w1], true).unwrap_or(0)
    }
}

system_stack_fn! {
    /// `rt_stream_try_put(ctx, sink, w0, w1) -> status`: see
    /// `crag_abi::RuntimeFn::StreamTryPut`.
    fn rt_stream_try_put(ctx: *const TaskContext, end: *mut End, w0: u64, w1: u64) -> u64 => try_put_entry
}

/// The Rust half of `rt_stream_try_put`.
///
/// # Safety
///
/// Called only by `rt_stream_try_put`, with a sink that has not been
/// disposed.
unsafe extern "C" fn try_put_entry(
    ctx: *const TaskContext,
    end: *mut End,
    w0: u64,
    w1: u64,
) -> u64 {
    // SAFETY: as the caller promises; a put that does not wait gives a
    // status.
    unsafe { put(&*ctx, end, [w0, w1], false).expect("a status") }
}

suspending_fn! {
    /// `rt_stream_next(ctx, source, out) -> status`: see
    /// `crag_abi::RuntimeFn::StreamNext`.
    fn rt_stream_next(ctx: *const TaskContext, end: *mut End, out: *mut u64) -> u64 => next_entry
}

/// The Rust half of `rt_stream_next`: suspends while there is no value.
///
/// # Safety
///
/// Called only by `rt_stream_next`, with a source that has not been
/// disposed and a place for a value at `out`.
unsafe extern "C" fn next_entry(ctx: *const TaskContext, end: *mut End, out: *mut u64) -> u64 {
    // SAFETY: as the caller promises.
    let (ctx, end, (heap, types)) = unsafe { (&*ctx, &*end, worker_of(ctx)) };
    if stop_if_due(ctx) {
        return 0;
    }
    if end.closed {
        return STREAM_CLOSED;
    }
    let Role::Consumer(id) = end.role else {
        die("took a value from a sink");
    };
    let chan = &*end.chan;
    let mut wakes = Wakes::new();
    let mut state = chan.state.lock().unwrap();
    let status = 'next: {
        let value = match chan.kind {
            Kind::Broadcast => state
                .consumers
                .get_mut(&id)
                .expect("a consumer")
                .queue
                .pop_front(),
            _ => state.queue.pop_front(),
        };
        if let Some(value) = value {
            chan.give(out, value);
            chan.admit(&mut state, heap, types, &mut wakes);
            break 'next Some(STREAM_OK);
        }
        if chan.kind != Kind::Broadcast
            && let Some(p) = state.pending.pop_front()
        {
            // A hand-off from a waiting put.
            chan.give(out, p.value);
            wakes.push((p.fiber, STREAM_OK));
            break 'next Some(STREAM_OK);
        }
        if chan.kind != Kind::Broadcast && state.released > 0 {
            state.released -= 1;
            break 'next Some(STREAM_CLOSED);
        }
        if let Some(status) = Channel::ended(&state) {
            break 'next Some(status);
        }
        // SAFETY: as the caller promises.
        if unsafe { scheduler_of(ctx) }.is_none() {
            raise(ctx, TrapKind::Unsupported, None);
            break 'next Some(0);
        }
        let token = state.next_id;
        state.next_id += 1;
        // SAFETY: as the caller promises.
        let fiber = unsafe { suspend(ctx, WaitReason::Stream) };
        state.consumers.get_mut(&id).expect("a consumer").waiter =
            Some(Waiter { fiber, out, token });
        if chan.kind == Kind::Broadcast {
            // Waiting may let a hand-off through.
            chan.admit(&mut state, heap, types, &mut wakes);
        } else {
            state.waiting.push_back(id);
        }
        drop(state);
        wake_all(wakes);
        wait_for(
            ctx,
            Waiting::Stream {
                chan: end.chan.clone(),
                token,
            },
        );
        return 0;
    };
    drop(state);
    wake_all(wakes);
    status.expect("a status")
}

system_stack_fn! {
    /// `rt_stream_close(ctx, end)`: see `crag_abi::RuntimeFn::StreamClose`.
    fn rt_stream_close(ctx: *const TaskContext, end: *mut End) => close_entry
}

/// The Rust half of `rt_stream_close`.
///
/// # Safety
///
/// Called only by `rt_stream_close`, with an end that has not been
/// disposed.
unsafe extern "C" fn close_entry(ctx: *const TaskContext, end: *mut End) {
    // SAFETY: as the caller promises.
    let (end, (heap, types)) = unsafe { (&mut *end, worker_of(ctx)) };
    if !end.closed {
        end.closed = true;
        end.chan.leave(&end.role, true, heap, types);
    }
}

system_stack_fn! {
    /// `rt_stream_dispose(ctx, end)`: see `crag_abi::RuntimeFn::StreamDispose`.
    fn rt_stream_dispose(ctx: *const TaskContext, end: *mut End) => dispose_entry
}

/// The Rust half of `rt_stream_dispose`.
///
/// # Safety
///
/// Called only by `rt_stream_dispose`, once for each end.
unsafe extern "C" fn dispose_entry(ctx: *const TaskContext, end: *mut End) {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        dispose(end as u64, heap, types);
    }
}

/// Disposes of an end, as `rt_stream_dispose` does: for the box of a
/// `RuntimeStream` being freed.
///
/// # Safety
///
/// `end` came from the runtime and is disposed of once.
pub(crate) unsafe fn dispose(end: u64, heap: &mut Heap, types: &Types) {
    // SAFETY: as the caller promises; the end's word ends here.
    let end = unsafe { Box::from_raw(end as *mut End) };
    if !end.closed {
        end.chan.leave(&end.role, false, heap, types);
    }
}

system_stack_fn! {
    /// `rt_hub_new(ctx, capacity, list, kind) -> hub`: see
    /// `crag_abi::RuntimeFn::HubNew`.
    fn rt_hub_new(ctx: *const TaskContext, capacity: u64, list: u64, kind: u64) -> u64 => hub_new_entry
}

/// The Rust half of `rt_hub_new`.
///
/// # Safety
///
/// Called only by `rt_hub_new`.
unsafe extern "C" fn hub_new_entry(
    ctx: *const TaskContext,
    capacity: u64,
    list: u64,
    kind: u64,
) -> u64 {
    // SAFETY: as the caller promises.
    let (_, types) = unsafe { worker_of(ctx) };
    let kind = if kind == HUB_BROADCAST {
        Kind::Broadcast
    } else {
        Kind::FanOut
    };
    let chan = Channel::new(kind, capacity as usize, types.element_of(list).clone());
    Arc::into_raw(Arc::new(chan)) as u64
}

/// The hub behind the word generated code holds.
///
/// # Safety
///
/// `hub` comes from `rt_hub_new` and has not been dropped.
unsafe fn hub<'a>(hub: *const Channel) -> &'a Channel {
    // SAFETY: as the caller promises.
    unsafe { &*hub }
}

/// The hub as a reference of its own, for an end.
///
/// # Safety
///
/// As for [`hub`].
unsafe fn hub_arc(hub: *const Channel) -> Arc<Channel> {
    // SAFETY: as the caller promises, the word holds a reference.
    unsafe {
        Arc::increment_strong_count(hub);
        Arc::from_raw(hub)
    }
}

system_stack_fn! {
    /// `rt_hub_sink(ctx, hub) -> sink`: see `crag_abi::RuntimeFn::HubSink`.
    fn rt_hub_sink(ctx: *const TaskContext, hub: *const Channel) -> u64 => hub_sink_entry
}

/// The Rust half of `rt_hub_sink`.
///
/// # Safety
///
/// Called only by `rt_hub_sink`, with a hub that has not been dropped.
unsafe extern "C" fn hub_sink_entry(_: *const TaskContext, ptr: *const Channel) -> u64 {
    // SAFETY: as the caller promises.
    let chan = unsafe { hub_arc(ptr) };
    let mut state = chan.state.lock().unwrap();
    let sealed = state.sealed;
    if !sealed {
        state.producers += 1;
    }
    drop(state);
    end(chan, Role::Producer, sealed)
}

system_stack_fn! {
    /// `rt_hub_source(ctx, hub) -> source`: see `crag_abi::RuntimeFn::HubSource`.
    fn rt_hub_source(ctx: *const TaskContext, hub: *const Channel) -> u64 => hub_source_entry
}

/// The Rust half of `rt_hub_source`.
///
/// # Safety
///
/// Called only by `rt_hub_source`, with a hub that has not been dropped.
unsafe extern "C" fn hub_source_entry(_: *const TaskContext, ptr: *const Channel) -> u64 {
    // SAFETY: as the caller promises.
    let chan = unsafe { hub_arc(ptr) };
    let mut state = chan.state.lock().unwrap();
    let id = state.next_id;
    state.next_id += 1;
    state.consumers.insert(
        id,
        Consumer {
            queue: VecDeque::new(),
            waiter: None,
        },
    );
    drop(state);
    end(chan, Role::Consumer(id), false)
}

/// Seals a hub, waking its waiting consumers if the producers are gone.
fn seal(state: &mut State, wakes: &mut Wakes) {
    state.sealed = true;
    Channel::end_waiting(state, wakes);
}

system_stack_fn! {
    /// `rt_hub_seal(ctx, hub)`: see `crag_abi::RuntimeFn::HubSeal`.
    fn rt_hub_seal(ctx: *const TaskContext, hub: *const Channel) => hub_seal_entry
}

/// The Rust half of `rt_hub_seal`.
///
/// # Safety
///
/// Called only by `rt_hub_seal`, with a hub that has not been dropped.
unsafe extern "C" fn hub_seal_entry(_: *const TaskContext, ptr: *const Channel) {
    // SAFETY: as the caller promises.
    let chan = unsafe { hub(ptr) };
    let mut wakes = Wakes::new();
    seal(&mut chan.state.lock().unwrap(), &mut wakes);
    wake_all(wakes);
}

system_stack_fn! {
    /// `rt_hub_release(ctx, hub, n)`: see `crag_abi::RuntimeFn::HubRelease`.
    fn rt_hub_release(ctx: *const TaskContext, hub: *const Channel, n: u64) => hub_release_entry
}

/// The Rust half of `rt_hub_release`.
///
/// # Safety
///
/// Called only by `rt_hub_release`, with a hub that has not been dropped.
unsafe extern "C" fn hub_release_entry(_: *const TaskContext, ptr: *const Channel, n: u64) {
    // SAFETY: as the caller promises.
    let chan = unsafe { hub(ptr) };
    let mut wakes = Wakes::new();
    let mut state = chan.state.lock().unwrap();
    let mut n = n as usize;
    while n > 0
        && let Some(id) = state.waiting.pop_front()
    {
        if let Some(waiter) = state.consumers.get_mut(&id).and_then(|c| c.waiter.take()) {
            wakes.push((waiter.fiber, STREAM_CLOSED));
            n -= 1;
        }
    }
    state.released += n;
    drop(state);
    wake_all(wakes);
}

system_stack_fn! {
    /// `rt_hub_drop(ctx, hub)`: see `crag_abi::RuntimeFn::HubDrop`.
    fn rt_hub_drop(ctx: *const TaskContext, hub: *const Channel) => hub_drop_entry
}

/// The Rust half of `rt_hub_drop`.
///
/// # Safety
///
/// Called only by `rt_hub_drop`, once for the word `rt_hub_new` gave.
unsafe extern "C" fn hub_drop_entry(ctx: *const TaskContext, ptr: *const Channel) {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, types) = worker_of(ctx);
        drop_hub(ptr as u64, heap, types);
    }
}

/// Gives up a hub's handle, as `rt_hub_drop` does: for the box of a
/// `RuntimeHub` being freed.
///
/// # Safety
///
/// `hub` came from `rt_hub_new` and is given up once.
pub(crate) unsafe fn drop_hub(hub: u64, heap: &mut Heap, types: &Types) {
    // SAFETY: as the caller promises; the hub's word ends here.
    let chan = unsafe { Arc::from_raw(hub as *const Channel) };
    let mut wakes = Wakes::new();
    let mut state = chan.state.lock().unwrap();
    state.joinable = false;
    seal(&mut state, &mut wakes);
    if state.consumers.is_empty() {
        chan.orphan(&mut state, STREAM_CLOSED, heap, types, &mut wakes);
    }
    drop(state);
    wake_all(wakes);
}
