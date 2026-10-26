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

//! The scheduler (Plan §11.7.1): fibers spread over worker threads.
//!
//! Each worker has a Chase–Lev deque of runnable fibers. It picks the next
//! fiber from its own deque, then from the global queue, where fibers come
//! from outside any worker, are woken, or gave up their turn, then by
//! stealing from another worker's deque, and parks its thread when there is
//! nothing to run. From the global queue it takes its share, up to
//! [`BATCH`] fibers, and keeps the rest on its deque, in the order they
//! came, where idle workers steal them. A deque holds at most a batch, so
//! it never keeps a worker from the global queue for long.
//!
//! A fiber runs until it finishes, traps, is paused, or suspends. A ticker
//! thread preempts a fiber that has run for a whole time slice, through the
//! sentinel (§11.3.4); the fiber then goes to the back of the global queue.
//!
//! A runtime function that waits suspends the fiber with [`suspend`] and
//! hands a [`FiberRef`] to whatever will [`wake`] it. Waking may come from
//! any thread, before the fiber has even left its worker: the fiber's
//! `park` word settles the race. `suspend` sets it to `SUSPENDING`; the
//! worker, once the fiber has switched out, moves it to `PARKED`, unless a
//! wake got there first and left `WOKEN`: then the resume ends `Runnable`,
//! as after a preemption, and the worker queues the fiber again. A wake of
//! a `PARKED` fiber clears the word and queues the fiber itself.

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering, fence};
use std::sync::{Arc, Condvar, Mutex, OnceLock};
use std::thread::{JoinHandle, Thread};
use std::time::Duration;

use crate::deque::{Deque, Steal, Stealer};
use crate::fiber::{Fiber, FiberState, TaskContext, Worker};
use crate::rc::Types;
use crate::reactor::Reactor;
use crate::sentinel::{StopHandle, StopReason};
use crate::unwind::CodeMap;

/// The fiber runs, or has never suspended.
pub(crate) const PARK_NONE: usize = 0;
/// The fiber asked to suspend and has not left its worker yet.
pub(crate) const PARK_SUSPENDING: usize = 1;
/// Woken while `SUSPENDING`: its worker queues it again.
pub(crate) const PARK_WOKEN: usize = 2;
/// Off its worker, waiting for a wake.
pub(crate) const PARK_PARKED: usize = 3;

/// What a suspended fiber waits for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WaitReason {
    /// Its turn again, after giving the other fibers theirs.
    Yield,
    /// A deadline.
    Sleep,
    /// An I/O operation that would have blocked.
    Io,
    /// A free place under the limit of a scope, to start a task (§11.7.3).
    Start,
    /// The next task of a scope to finish.
    Tasks,
    /// Room in a stream or a hub to put a value, or a value to take
    /// (§11.7.5).
    Stream,
    /// The lock of an `ext` (§11.7.9).
    Ext,
}

/// How a scheduler runs.
#[derive(Clone, Copy, Debug)]
pub struct SchedulerConfig {
    /// Worker threads, at least one.
    pub workers: usize,
    /// How long a fiber may run before it is preempted; none to never
    /// preempt.
    pub slice: Option<Duration>,
}

impl Default for SchedulerConfig {
    /// One worker per core, preempting after ten milliseconds.
    fn default() -> SchedulerConfig {
        SchedulerConfig {
            workers: std::thread::available_parallelism().map_or(1, |n| n.get()),
            slice: Some(Duration::from_millis(10)),
        }
    }
}

/// A fiber the scheduler owns, as a word in its queues.
type FiberPtr = usize;

/// The most fibers a worker takes from the global queue at once.
pub const BATCH: usize = 32;

/// What the workers share.
pub(crate) struct Shared {
    stealers: Vec<Stealer>,
    global: Mutex<VecDeque<FiberPtr>>,
    parkers: Vec<Parker>,
    /// For each worker, the fiber it runs, with the number of its resume,
    /// so that the ticker can tell a fiber that ran a whole slice.
    running: Vec<Mutex<Option<(u64, StopHandle)>>>,
    /// Fibers spawned and not yet stopped: queued, running or suspended.
    live: Mutex<usize>,
    idle: Condvar,
    /// Fibers that finished, trapped or were paused.
    stopped: Mutex<Vec<FiberPtr>>,
    shutdown: AtomicBool,
    stats: Vec<Counters>,
    /// Where fibers wait for time and I/O.
    pub(crate) reactor: Reactor,
}

// SAFETY: the fibers behind the words in the queues are owned by the
// scheduler and used by one worker at a time; handing one from a queue to a
// worker synchronizes through the queue.
unsafe impl Send for Shared {}
unsafe impl Sync for Shared {}

/// A worker thread's sleep.
struct Parker {
    thread: OnceLock<Thread>,
    parked: AtomicBool,
}

#[derive(Default)]
struct Counters {
    resumes: AtomicU64,
    steals: AtomicU64,
    parks: AtomicU64,
}

/// What one worker did, for tests and diagnostics.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkerStats {
    pub resumes: u64,
    pub steals: u64,
    pub parks: u64,
}

/// A worker's own part of the scheduler.
pub(crate) struct Local {
    shared: Arc<Shared>,
    index: usize,
    deque: Deque,
}

/// Worker threads running fibers until the scheduler is dropped.
pub struct Scheduler {
    shared: Arc<Shared>,
    threads: Vec<JoinHandle<()>>,
    ticker: Option<JoinHandle<()>>,
    reactor: Option<JoinHandle<()>>,
}

impl Scheduler {
    /// Starts the workers, which free boxes by `types` and unwind by
    /// `code`, the reactor, and the ticker if the configuration preempts.
    pub fn new(config: SchedulerConfig, types: Arc<Types>, code: Arc<CodeMap>) -> Scheduler {
        let n = config.workers.max(1);
        let (deques, stealers): (Vec<Deque>, Vec<Stealer>) = (0..n).map(|_| Deque::new()).unzip();
        let shared = Arc::new(Shared::new(stealers));
        let threads = deques
            .into_iter()
            .enumerate()
            .map(|(index, deque)| {
                let local = Local {
                    shared: shared.clone(),
                    index,
                    deque,
                };
                let (types, code) = (types.clone(), code.clone());
                std::thread::Builder::new()
                    .name(format!("crag-worker-{index}"))
                    .spawn(move || worker_main(local, types, code))
                    .expect("a worker thread starts")
            })
            .collect();
        let ticker = config.slice.map(|slice| {
            let shared = shared.clone();
            std::thread::Builder::new()
                .name("crag-ticker".into())
                .spawn(move || ticker_main(&shared, slice))
                .expect("the ticker starts")
        });
        let reactor = {
            let shared = shared.clone();
            std::thread::Builder::new()
                .name("crag-reactor".into())
                .spawn(move || shared.reactor.run())
                .expect("the reactor starts")
        };
        Scheduler {
            shared,
            threads,
            ticker,
            reactor: Some(reactor),
        }
    }

    /// Hands a runnable fiber to the workers.
    pub fn spawn(&self, fiber: Box<Fiber>) {
        self.spawn_all(vec![fiber]);
    }

    /// Hands runnable fibers to the workers at once, in their order.
    pub fn spawn_all(&self, fibers: Vec<Box<Fiber>>) {
        for fiber in &fibers {
            assert!(
                matches!(fiber.state(), FiberState::Runnable | FiberState::Paused),
                "spawned a fiber that is {:?}",
                fiber.state()
            );
            // A poll may borrow what only its own thread can use.
            assert!(
                fiber.metering.as_ref().is_none_or(|m| m.poll.is_none()),
                "spawned a fiber with a poll"
            );
        }
        *self.shared.live.lock().unwrap() += fibers.len();
        let mut global = self.shared.global.lock().unwrap();
        global.extend(fibers.into_iter().map(|f| Box::into_raw(f) as FiberPtr));
        drop(global);
        self.shared.notify();
    }

    /// Waits until no fiber is queued, running or suspended, and returns
    /// those that finished, trapped or were paused since the last call, in
    /// the order they stopped.
    pub fn wait(&self) -> Vec<Box<Fiber>> {
        let mut live = self.shared.live.lock().unwrap();
        while *live > 0 {
            live = self.shared.idle.wait(live).unwrap();
        }
        drop(live);
        let stopped = std::mem::take(&mut *self.shared.stopped.lock().unwrap());
        stopped
            .into_iter()
            // SAFETY: a stopped fiber's word came from `Box::into_raw` and
            // no worker uses it any more.
            .map(|p| unsafe { Box::from_raw(p as *mut Fiber) })
            .collect()
    }

    /// What each worker did so far.
    pub fn stats(&self) -> Vec<WorkerStats> {
        self.shared
            .stats
            .iter()
            .map(|c| WorkerStats {
                resumes: c.resumes.load(Ordering::Relaxed),
                steals: c.steals.load(Ordering::Relaxed),
                parks: c.parks.load(Ordering::Relaxed),
            })
            .collect()
    }
}

impl Drop for Scheduler {
    /// Stops the workers once they are between fibers. Fibers still queued
    /// or stopped are freed, and so are those waiting in the reactor; any
    /// other suspended fiber belongs to whoever would wake it.
    fn drop(&mut self) {
        self.shared.shutdown.store(true, Ordering::SeqCst);
        for parker in &self.shared.parkers {
            if let Some(thread) = parker.thread.get() {
                thread.unpark();
            }
        }
        if let Some(ticker) = self.ticker.take() {
            ticker.thread().unpark();
            let _ = ticker.join();
        }
        for thread in self.threads.drain(..) {
            let _ = thread.join();
        }
        self.shared.reactor.stop();
        if let Some(reactor) = self.reactor.take() {
            let _ = reactor.join();
        }
        // Woken, they go to the global queue, which no worker takes from
        // any more.
        for fiber in self.shared.reactor.drain() {
            wake(fiber, [0, 0]);
        }
        let mut left: Vec<FiberPtr> = self.shared.global.lock().unwrap().drain(..).collect();
        for stealer in &self.shared.stealers {
            loop {
                match stealer.steal() {
                    Steal::Taken(p) => left.push(p),
                    Steal::Retry => {}
                    Steal::Empty => break,
                }
            }
        }
        left.append(&mut self.shared.stopped.lock().unwrap());
        for p in left {
            // SAFETY: as in `wait`; the workers are gone.
            drop(unsafe { Box::from_raw(p as *mut Fiber) });
        }
    }
}

impl Shared {
    fn new(stealers: Vec<Stealer>) -> Shared {
        let n = stealers.len();
        Shared {
            stealers,
            global: Mutex::new(VecDeque::new()),
            parkers: (0..n)
                .map(|_| Parker {
                    thread: OnceLock::new(),
                    parked: AtomicBool::new(false),
                })
                .collect(),
            running: (0..n).map(|_| Mutex::new(None)).collect(),
            live: Mutex::new(0),
            idle: Condvar::new(),
            stopped: Mutex::new(Vec::new()),
            shutdown: AtomicBool::new(false),
            stats: (0..n).map(|_| Counters::default()).collect(),
            reactor: Reactor::new().expect("the poller starts"),
        }
    }

    /// Hands a new fiber, a task of a scope, to the workers: to the deque
    /// of `local`'s worker while it holds less than a batch, else to the
    /// global queue.
    pub(crate) fn launch(&self, fiber: Box<Fiber>, local: Option<&mut Local>) {
        *self.live.lock().unwrap() += 1;
        let ptr = Box::into_raw(fiber) as FiberPtr;
        match local {
            Some(local) if local.deque.len() < BATCH => {
                local.deque.push(ptr);
                self.notify();
            }
            _ => self.push_global(ptr),
        }
    }

    /// Counts off a fiber that stopped and that its scope took.
    pub(crate) fn retire(&self) {
        let mut live = self.live.lock().unwrap();
        *live -= 1;
        if *live == 0 {
            self.idle.notify_all();
        }
    }

    /// Queues a fiber on the global queue and wakes a parked worker.
    fn push_global(&self, fiber: FiberPtr) {
        self.global.lock().unwrap().push_back(fiber);
        self.notify();
    }

    /// Wakes one parked worker, if one is parked. Called after making work
    /// visible: the fence pairs with the one a worker passes between
    /// announcing that it parks and looking for work a last time.
    fn notify(&self) {
        fence(Ordering::SeqCst);
        for parker in &self.parkers {
            if parker.parked.swap(false, Ordering::SeqCst) {
                if let Some(thread) = parker.thread.get() {
                    thread.unpark();
                }
                return;
            }
        }
    }

    fn has_work(&self) -> bool {
        !self.global.lock().unwrap().is_empty() || self.stealers.iter().any(|s| !s.is_empty())
    }

    /// Records a fiber that finished, trapped or was paused.
    fn stop(&self, fiber: FiberPtr) {
        self.stopped.lock().unwrap().push(fiber);
        let mut live = self.live.lock().unwrap();
        *live -= 1;
        if *live == 0 {
            self.idle.notify_all();
        }
    }
}

impl Local {
    /// The next fiber to run, parking until there is one; none once the
    /// scheduler shuts down.
    fn next(&mut self) -> Option<FiberPtr> {
        loop {
            if self.shared.shutdown.load(Ordering::SeqCst) {
                return None;
            }
            if let Some(fiber) = self.find() {
                return Some(fiber);
            }
            let parker = &self.shared.parkers[self.index];
            parker.parked.store(true, Ordering::SeqCst);
            fence(Ordering::SeqCst);
            if self.shared.has_work() || self.shared.shutdown.load(Ordering::SeqCst) {
                parker.parked.store(false, Ordering::SeqCst);
                continue;
            }
            self.shared.stats[self.index]
                .parks
                .fetch_add(1, Ordering::Relaxed);
            // A notify clears the flag before it unparks; any other wake is
            // spurious.
            while parker.parked.load(Ordering::SeqCst)
                && !self.shared.shutdown.load(Ordering::SeqCst)
            {
                std::thread::park();
            }
        }
    }

    /// A fiber from the own deque, the global queue or another worker's
    /// deque, without waiting.
    fn find(&mut self) -> Option<FiberPtr> {
        if let Some(fiber) = self.deque.take() {
            return Some(fiber);
        }
        if let Some(fiber) = self.take_global() {
            return Some(fiber);
        }
        self.steal()
    }

    /// The first fiber of the global queue, with this worker's share of
    /// the rest moved to its deque.
    fn take_global(&mut self) -> Option<FiberPtr> {
        let mut global = self.shared.global.lock().unwrap();
        let first = global.pop_front()?;
        let share = (global.len() / self.shared.stealers.len()).min(BATCH - 1);
        let batch: Vec<FiberPtr> = global.drain(..share).collect();
        drop(global);
        // The deque gives back the last pushed first.
        for &fiber in batch.iter().rev() {
            self.deque.push(fiber);
        }
        if !batch.is_empty() {
            self.shared.notify();
        }
        Some(first)
    }

    /// A fiber from another worker's deque, trying each in turn, starting
    /// after this one, until all are empty.
    fn steal(&mut self) -> Option<FiberPtr> {
        let n = self.shared.stealers.len();
        loop {
            let mut retry = false;
            for k in 1..n {
                let other = (self.index + k) % n;
                match self.shared.stealers[other].steal() {
                    Steal::Taken(fiber) => {
                        self.shared.stats[self.index]
                            .steals
                            .fetch_add(1, Ordering::Relaxed);
                        return Some(fiber);
                    }
                    Steal::Retry => retry = true,
                    Steal::Empty => {}
                }
            }
            if !retry {
                return None;
            }
        }
    }
}

/// A worker thread: runs fibers as they come until the scheduler shuts down.
fn worker_main(mut local: Local, types: Arc<Types>, code: Arc<CodeMap>) {
    let shared = local.shared.clone();
    let index = local.index;
    shared.parkers[index]
        .thread
        .set(std::thread::current())
        .expect("set once");
    let mut worker = Worker::new();
    worker.set_types(types);
    worker.set_code_map(code);
    let mut resumes = 0u64;
    while let Some(ptr) = local.next() {
        // SAFETY: a fiber in a queue is owned by the scheduler, and only
        // the worker that took it uses it until it is queued again.
        let fiber = unsafe { &mut *(ptr as *mut Fiber) };
        resumes += 1;
        *shared.running[index].lock().unwrap() = Some((resumes, fiber.stop_handle()));
        worker.sched = Some(local);
        let state = worker.resume(fiber);
        local = worker.sched.take().expect("put back");
        *shared.running[index].lock().unwrap() = None;
        shared.stats[index].resumes.fetch_add(1, Ordering::Relaxed);
        match state {
            // Preempted, or woken while it suspended: the others first.
            FiberState::Runnable => shared.push_global(ptr),
            // Its wake queues it.
            FiberState::Waiting(_) => {}
            // A task goes to its scope.
            FiberState::Finished | FiberState::Trapped if fiber.task.is_some() => {
                // SAFETY: as above; no queue holds the fiber any more.
                let fiber = unsafe { Box::from_raw(ptr as *mut Fiber) };
                crate::scope::finished(fiber, &mut local);
                shared.retire();
            }
            FiberState::Finished | FiberState::Trapped | FiberState::Paused => shared.stop(ptr),
            FiberState::Running => unreachable!("a resume returns when the fiber stops"),
        }
    }
}

/// Settles the state of a fiber that suspended, once it has left its
/// worker, and gives it: waiting, and from now on a wake queues it, or
/// runnable when a wake came first. A waiting fiber belongs to its waker
/// from the moment it is parked, so the state is written before.
///
/// # Safety
///
/// `fiber` is the fiber of `ctx`, and only the worker it left uses it.
pub(crate) unsafe fn settle(ctx: &TaskContext, fiber: *mut Fiber) -> FiberState {
    // SAFETY: as the caller promises, until the fiber is parked.
    unsafe {
        let waiting = FiberState::Waiting((*fiber).wait);
        (*fiber).state = waiting;
        match ctx.park.compare_exchange(
            PARK_SUSPENDING,
            PARK_PARKED,
            Ordering::AcqRel,
            Ordering::Acquire,
        ) {
            Ok(_) => waiting,
            Err(_) => {
                ctx.park.store(PARK_NONE, Ordering::Release);
                (*fiber).state = FiberState::Runnable;
                FiberState::Runnable
            }
        }
    }
}

/// The ticker: every slice, preempts each fiber that has run since the
/// previous tick.
fn ticker_main(shared: &Shared, slice: Duration) {
    let mut last: Vec<Option<u64>> = vec![None; shared.running.len()];
    while !shared.shutdown.load(Ordering::SeqCst) {
        std::thread::park_timeout(slice);
        for (running, last) in shared.running.iter().zip(&mut last) {
            let running = running.lock().unwrap();
            match &*running {
                Some((resume, handle)) if *last == Some(*resume) => {
                    handle.request_stop(StopReason::Preempt);
                }
                _ => {}
            }
            *last = running.as_ref().map(|(resume, _)| *resume);
        }
    }
}

/// A suspended fiber, for the one thing that wakes it.
pub struct FiberRef {
    fiber: *mut Fiber,
    shared: Option<Arc<Shared>>,
}

// SAFETY: the fiber does not run while suspended, and a wake hands it to
// a queue, which synchronizes with the worker that takes it.
unsafe impl Send for FiberRef {}

/// Suspends the fiber running on `ctx` when the runtime function calling
/// this returns: the function must be defined with `suspending_fn!`. The
/// fiber's worker leaves it until it is woken. Gives the reference that
/// wakes it.
///
/// # Safety
///
/// Called on the system stack by the Rust half of a function
/// `suspending_fn!` defined, for the fiber it was called on.
pub(crate) unsafe fn suspend(ctx: &TaskContext, reason: WaitReason) -> FiberRef {
    // SAFETY: as the caller promises, a worker runs the fiber of `ctx`.
    unsafe {
        let fiber = ctx.fiber.load(Ordering::Relaxed);
        (*fiber).wait = reason;
        let worker = ctx.worker.load(Ordering::Relaxed);
        let shared = (*worker).sched.as_ref().map(|l| l.shared.clone());
        ctx.park.store(PARK_SUSPENDING, Ordering::SeqCst);
        FiberRef { fiber, shared }
    }
}

/// The part of the scheduler of the worker running the fiber of `ctx`,
/// none for a fiber a worker resumes by hand.
///
/// # Safety
///
/// Called on the system stack by the Rust half of a runtime function, for
/// the fiber it was called on; nothing else uses the part meanwhile.
pub(crate) unsafe fn local_of<'a>(ctx: &TaskContext) -> Option<&'a mut Local> {
    // SAFETY: as the caller promises, a worker runs the fiber of `ctx`.
    unsafe {
        let worker = ctx.worker.load(Ordering::Relaxed);
        (*worker).sched.as_mut()
    }
}

/// The scheduler of the fiber running on `ctx`, none for a fiber a worker
/// resumes by hand.
///
/// # Safety
///
/// Called on the system stack by the Rust half of a runtime function, for
/// the fiber it was called on.
pub(crate) unsafe fn scheduler_of(ctx: &TaskContext) -> Option<Arc<Shared>> {
    // SAFETY: as the caller promises, a worker runs the fiber of `ctx`.
    unsafe {
        let worker = ctx.worker.load(Ordering::Relaxed);
        (*worker).sched.as_ref().map(|l| l.shared.clone())
    }
}

/// Wakes a suspended fiber: its suspending function returns `words`. A
/// fiber of a scheduler goes to the global queue; one a worker resumes by
/// hand becomes runnable for the next resume.
pub fn wake(fiber: FiberRef, words: [u64; 2]) {
    // SAFETY: a fiber with a `FiberRef` stays allocated until it is woken,
    // and only the reference's holder wakes it.
    let f = unsafe { &mut *fiber.fiber };
    let ctx = f.ctx.clone();
    ctx.wake_words[0].store(words[0], Ordering::Relaxed);
    ctx.wake_words[1].store(words[1], Ordering::Relaxed);
    loop {
        match ctx.park.load(Ordering::Acquire) {
            PARK_SUSPENDING => {
                if ctx
                    .park
                    .compare_exchange(
                        PARK_SUSPENDING,
                        PARK_WOKEN,
                        Ordering::AcqRel,
                        Ordering::Acquire,
                    )
                    .is_ok()
                {
                    return;
                }
            }
            PARK_PARKED => {
                ctx.park.store(PARK_NONE, Ordering::Release);
                f.state = FiberState::Runnable;
                if let Some(shared) = fiber.shared {
                    shared.push_global(fiber.fiber as FiberPtr);
                }
                return;
            }
            _ => return,
        }
    }
}

suspending_fn! {
    /// `rt_yield(ctx)`: see `crag_abi::RuntimeFn::Yield`.
    fn rt_yield(ctx: *const TaskContext) => yield_entry
}

/// The Rust half of `rt_yield`: suspends and wakes at once, so that the
/// worker queues the fiber again.
///
/// # Safety
///
/// Called only by `rt_yield`.
unsafe extern "C" fn yield_entry(ctx: *const TaskContext) {
    // SAFETY: as the caller promises.
    unsafe {
        if crate::cancel::stop_if_due(&*ctx) {
            return;
        }
        let fiber = suspend(&*ctx, WaitReason::Yield);
        wake(fiber, [0, 0]);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fiber::FiberConfig;

    /// A fiber that is never resumed, for the handshake alone.
    fn fiber() -> Box<Fiber> {
        // SAFETY: the fiber never runs, so its entry is never called.
        unsafe { Fiber::new(0, 0, &[], FiberConfig::normal()).unwrap() }
    }

    fn reference(fiber: &mut Fiber, shared: Option<Arc<Shared>>) -> FiberRef {
        FiberRef {
            fiber: &raw mut *fiber,
            shared,
        }
    }

    #[test]
    fn a_wake_before_the_worker_settles_makes_the_fiber_runnable() {
        let mut f = fiber();
        f.ctx.park.store(PARK_SUSPENDING, Ordering::SeqCst);
        wake(reference(&mut f, None), [7, 8]);
        assert_eq!(f.ctx.park.load(Ordering::SeqCst), PARK_WOKEN);
        let ctx = f.ctx.clone();
        // SAFETY: the fiber is not running.
        assert_eq!(unsafe { settle(&ctx, &raw mut *f) }, FiberState::Runnable);
        assert_eq!(f.state, FiberState::Runnable);
        assert_eq!(f.ctx.park.load(Ordering::SeqCst), PARK_NONE);
        let words = f
            .ctx
            .wake_words
            .each_ref()
            .map(|w| w.load(Ordering::SeqCst));
        assert_eq!(words, [7, 8]);
    }

    #[test]
    fn a_wake_of_a_parked_fiber_queues_it() {
        let (_deque, stealer) = Deque::new();
        let shared = Arc::new(Shared::new(vec![stealer]));
        let mut f = fiber();
        f.ctx.park.store(PARK_SUSPENDING, Ordering::SeqCst);
        let ctx = f.ctx.clone();
        // SAFETY: the fiber is not running.
        let state = unsafe { settle(&ctx, &raw mut *f) };
        assert_eq!(state, FiberState::Waiting(WaitReason::Yield));
        assert_eq!(f.state, state);
        assert_eq!(f.ctx.park.load(Ordering::SeqCst), PARK_PARKED);
        let ptr: *mut Fiber = &raw mut *f;
        wake(reference(&mut f, Some(shared.clone())), [1, 2]);
        assert_eq!(f.state, FiberState::Runnable);
        assert_eq!(f.ctx.park.load(Ordering::SeqCst), PARK_NONE);
        assert_eq!(
            shared.global.lock().unwrap().pop_front(),
            Some(ptr as FiberPtr)
        );
        // A second wake finds it awake and does nothing.
        wake(reference(&mut f, Some(shared.clone())), [3, 4]);
        assert!(shared.global.lock().unwrap().is_empty());
    }

    #[test]
    fn wakes_racing_the_worker_lose_no_fiber() {
        // The waker and the worker race on the word; the fiber ends up
        // queued exactly once either way, and runnable.
        for _ in 0..10_000 {
            let (_deque, stealer) = Deque::new();
            let shared = Arc::new(Shared::new(vec![stealer]));
            let mut f = fiber();
            f.ctx.park.store(PARK_SUSPENDING, Ordering::SeqCst);
            let ptr: *mut Fiber = &raw mut *f;
            let r = reference(&mut f, Some(shared.clone()));
            let waker = std::thread::spawn(move || wake(r, [0, 0]));
            let ctx = f.ctx.clone();
            // SAFETY: the fiber is not running.
            let state = unsafe { settle(&ctx, ptr) };
            waker.join().unwrap();
            let queued = shared.global.lock().unwrap().len();
            match state {
                FiberState::Runnable => assert_eq!(queued, 0),
                _ => assert_eq!(queued, 1),
            }
            assert_eq!(f.ctx.park.load(Ordering::SeqCst), PARK_NONE);
            assert_eq!(f.state, FiberState::Runnable);
        }
    }
}
