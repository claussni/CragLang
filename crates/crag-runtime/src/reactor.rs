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

//! The reactor (Plan §11.7.2): a thread of the scheduler that wakes the
//! fibers waiting for time or for I/O.
//!
//! A fiber that sleeps leaves its [`FiberRef`] in the timer wheel. One whose
//! operation would block leaves it with the operation, an [`IoOp`], in the
//! list of waits of its file descriptor, which the poller watches for what
//! the waits need. When the descriptor becomes ready, the reactor tries
//! each operation that can go on again, and wakes the fibers whose
//! operations went through, with their results; an operation that would
//! still block keeps waiting. The fiber does not run meanwhile, so the
//! reactor may fill its buffer.
//!
//! The reactor thread waits on the poller until the wheel's next deadline.
//! A timer that comes before it notifies the poller, so the thread waits
//! anew.

use std::collections::HashMap;
use std::io;
use std::os::fd::RawFd;
use std::sync::Mutex;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

use crate::poll::{Event, Interest, Poller};
use crate::sched::{FiberRef, wake};
use crate::timer::TimerWheel;

/// An I/O operation a fiber waits to complete. Its result is two words,
/// what the operation gives and zero, or zero and the error number.
#[derive(Clone, Copy, Debug)]
pub(crate) enum IoOp {
    Read {
        fd: RawFd,
        buf: *mut u8,
        len: usize,
    },
    Write {
        fd: RawFd,
        buf: *const u8,
        len: usize,
    },
    Accept {
        fd: RawFd,
    },
    /// Waits for a connection under way to be made.
    Connect {
        fd: RawFd,
    },
}

// SAFETY: the buffer belongs to the fiber that waits, which does not run
// until the operation is done; the wake hands the result back.
unsafe impl Send for IoOp {}

/// The result of an operation that went through or failed.
pub(crate) type IoResult = [u64; 2];

fn errno() -> i32 {
    io::Error::last_os_error()
        .raw_os_error()
        .unwrap_or(libc::EIO)
}

/// The result of a system call that gives a count or -1, none when it
/// would block.
fn outcome(n: isize) -> Option<IoResult> {
    if n >= 0 {
        return Some([n as u64, 0]);
    }
    match errno() {
        libc::EAGAIN | libc::EINPROGRESS => None,
        e => Some([0, e as u64]),
    }
}

impl IoOp {
    pub(crate) fn fd(&self) -> RawFd {
        match *self {
            IoOp::Read { fd, .. }
            | IoOp::Write { fd, .. }
            | IoOp::Accept { fd }
            | IoOp::Connect { fd } => fd,
        }
    }

    pub(crate) fn interest(&self) -> Interest {
        match self {
            IoOp::Read { .. } | IoOp::Accept { .. } => Interest::READ,
            IoOp::Write { .. } | IoOp::Connect { .. } => Interest::WRITE,
        }
    }

    /// Tries the operation once: its result, or none when it would block.
    /// A signal that interrupts it makes it try again.
    pub(crate) fn attempt(&self) -> Option<IoResult> {
        loop {
            // SAFETY: the buffers are live for as long as the operation
            // waits, as its fiber promised.
            let n = unsafe {
                match *self {
                    IoOp::Read { fd, buf, len } => libc::read(fd, buf.cast(), len),
                    IoOp::Write { fd, buf, len } => libc::write(fd, buf.cast(), len),
                    IoOp::Accept { fd } => libc::accept4(
                        fd,
                        std::ptr::null_mut(),
                        std::ptr::null_mut(),
                        libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
                    ) as isize,
                    IoOp::Connect { fd } => return connected(fd),
                }
            };
            if n < 0 && errno() == libc::EINTR {
                continue;
            }
            return outcome(n);
        }
    }

    /// Waits on this thread until the operation is done: for a fiber that
    /// no scheduler runs, so that has no reactor to wait in.
    pub(crate) fn block(&self) -> IoResult {
        loop {
            if let Some(result) = self.attempt() {
                return result;
            }
            let interest = self.interest();
            let mut pollfd = libc::pollfd {
                fd: self.fd(),
                events: if interest.read {
                    libc::POLLIN
                } else {
                    libc::POLLOUT
                },
                revents: 0,
            };
            // SAFETY: polls one live pollfd. An error, a signal included,
            // makes the loop try the operation again, which reports it.
            unsafe { libc::poll(&mut pollfd, 1, -1) };
        }
    }
}

/// Whether the connection under way on `fd` is made: none while it is not
/// writable, then its outcome.
fn connected(fd: RawFd) -> Option<IoResult> {
    let mut pollfd = libc::pollfd {
        fd,
        events: libc::POLLOUT,
        revents: 0,
    };
    // SAFETY: polls one live pollfd without waiting.
    let ready = unsafe { libc::poll(&mut pollfd, 1, 0) };
    if ready < 0 {
        return Some([0, errno() as u64]);
    }
    if ready == 0 {
        return None;
    }
    let mut error: libc::c_int = 0;
    let mut len = std::mem::size_of::<libc::c_int>() as libc::socklen_t;
    // SAFETY: reads an int option into a live int.
    let r = unsafe {
        libc::getsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_ERROR,
            (&raw mut error).cast(),
            &mut len,
        )
    };
    Some(match (r, error) {
        (r, _) if r < 0 => [0, errno() as u64],
        (_, 0) => [0, 0],
        (_, e) => [0, e as u64],
    })
}

/// A fiber waiting for an operation.
struct Wait {
    op: IoOp,
    fiber: FiberRef,
}

struct State {
    timers: TimerWheel<FiberRef>,
    /// The waits of each registered file descriptor, oldest first.
    fds: HashMap<RawFd, Vec<Wait>>,
    /// The deadline the reactor thread waits until; none when it waits
    /// for I/O alone.
    waiting_until: Option<Instant>,
}

/// Timers and I/O waits, and the poller that watches the latter.
pub(crate) struct Reactor {
    poller: Poller,
    state: Mutex<State>,
    shutdown: AtomicBool,
}

impl Reactor {
    pub(crate) fn new() -> io::Result<Reactor> {
        Ok(Reactor {
            poller: Poller::new()?,
            state: Mutex::new(State {
                timers: TimerWheel::new(Instant::now()),
                fds: HashMap::new(),
                waiting_until: None,
            }),
            shutdown: AtomicBool::new(false),
        })
    }

    /// Wakes `fiber` once the time reaches `deadline`.
    pub(crate) fn sleep_until(&self, deadline: Instant, fiber: FiberRef) {
        let mut state = self.state.lock().unwrap();
        state.timers.add(deadline, fiber);
        if let Some(next) = state.timers.next_deadline()
            && state.waiting_until.is_none_or(|until| next < until)
        {
            // The thread waits anew.
            state.waiting_until = Some(next);
            self.poller.notify();
        }
    }

    /// Wakes `fiber` with the result of `op` once it goes through. Gives
    /// the fiber back with the error number when the poller refuses the
    /// file descriptor.
    pub(crate) fn wait_io(&self, op: IoOp, fiber: FiberRef) -> Result<(), (FiberRef, u64)> {
        let fd = op.fd();
        let mut state = self.state.lock().unwrap();
        let waits = state.fds.entry(fd).or_default();
        let registered = !waits.is_empty();
        let interest = waits
            .iter()
            .fold(op.interest(), |i, w| i.union(w.op.interest()));
        if let Err(error) = self.poller.set(fd, interest, registered) {
            if !registered {
                state.fds.remove(&fd);
            }
            let errno = error.raw_os_error().unwrap_or(libc::EIO);
            return Err((fiber, errno as u64));
        }
        state
            .fds
            .get_mut(&fd)
            .expect("entered")
            .push(Wait { op, fiber });
        Ok(())
    }

    /// The reactor thread: waits for the poller and the timers, and wakes
    /// the fibers whose time came or whose operations went through, until
    /// `stop`.
    pub(crate) fn run(&self) {
        let mut events = Vec::new();
        while !self.shutdown.load(Ordering::SeqCst) {
            let timeout = {
                let mut state = self.state.lock().unwrap();
                state.waiting_until = state.timers.next_deadline();
                state
                    .waiting_until
                    .map(|d| d.saturating_duration_since(Instant::now()))
            };
            if let Err(error) = self.poller.wait(timeout, &mut events) {
                crate::die(&format!("the poller failed: {error}"));
            }
            let mut woken = Vec::new();
            {
                let mut state = self.state.lock().unwrap();
                for event in &events {
                    self.ready(&mut state, *event, &mut woken);
                }
                let now = Instant::now();
                woken.extend(state.timers.advance(now).into_iter().map(|f| (f, [0, 0])));
            }
            for (fiber, words) in woken {
                wake(fiber, words);
            }
        }
    }

    /// Tries the waits on a file descriptor that became ready, in their
    /// order, and keeps the registration to what the rest need.
    fn ready(&self, state: &mut State, event: Event, woken: &mut Vec<(FiberRef, IoResult)>) {
        let Some(waits) = state.fds.get_mut(&event.fd) else {
            return;
        };
        let mut i = 0;
        while i < waits.len() {
            let interest = waits[i].op.interest();
            let ready =
                (interest.read && event.ready.read) || (interest.write && event.ready.write);
            match ready.then(|| waits[i].op.attempt()).flatten() {
                Some(result) => woken.push((waits.remove(i).fiber, result)),
                None => i += 1,
            }
        }
        let interest = waits
            .iter()
            .fold(Interest::default(), |i, w| i.union(w.op.interest()));
        if interest.is_empty() {
            state.fds.remove(&event.fd);
            self.poller.remove(event.fd);
        } else if let Err(error) = self.poller.set(event.fd, interest, true) {
            // Closed meanwhile: the waits learn it from their operations.
            let errno = error.raw_os_error().unwrap_or(libc::EIO) as u64;
            for wait in state.fds.remove(&event.fd).unwrap_or_default() {
                woken.push((wait.fiber, [0, errno]));
            }
        }
    }

    /// Ends the reactor thread's loop.
    pub(crate) fn stop(&self) {
        self.shutdown.store(true, Ordering::SeqCst);
        self.poller.notify();
    }

    /// Takes every fiber still waiting, once the thread has stopped.
    pub(crate) fn drain(&self) -> Vec<FiberRef> {
        let mut state = self.state.lock().unwrap();
        let mut fibers = state.timers.drain();
        for (fd, waits) in state.fds.drain() {
            self.poller.remove(fd);
            fibers.extend(waits.into_iter().map(|w| w.fiber));
        }
        fibers
    }
}
