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

//! The operating system's readiness interface (Plan §11.7.2): epoll on
//! Linux, the only target so far; kqueue and IOCP would take its place
//! behind the same functions.
//!
//! Registrations are level-triggered: a file descriptor is reported as
//! long as it is ready for what it is registered for, so its owner changes
//! or removes the registration once nobody waits on it. An eventfd, always
//! registered, lets another thread interrupt a wait.

use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::time::Duration;

/// What a registration waits for.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Interest {
    pub read: bool,
    pub write: bool,
}

impl Interest {
    pub const READ: Interest = Interest {
        read: true,
        write: false,
    };
    pub const WRITE: Interest = Interest {
        read: false,
        write: true,
    };

    pub fn union(self, other: Interest) -> Interest {
        Interest {
            read: self.read || other.read,
            write: self.write || other.write,
        }
    }

    pub fn is_empty(self) -> bool {
        !self.read && !self.write
    }
}

/// A file descriptor that became ready. An error or hang-up makes it
/// ready for both, so that the operation waiting on it finds out.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Event {
    pub fd: RawFd,
    pub ready: Interest,
}

/// An epoll instance with its eventfd.
pub struct Poller {
    epoll: OwnedFd,
    wakeup: OwnedFd,
}

/// The token of the eventfd; file descriptors are never negative.
const WAKEUP: u64 = u64::MAX;

const MAX_EVENTS: usize = 256;

fn check(result: libc::c_int) -> io::Result<libc::c_int> {
    if result < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(result)
    }
}

impl Poller {
    pub fn new() -> io::Result<Poller> {
        // SAFETY: plain system calls; each result is checked before it is
        // owned.
        unsafe {
            let epoll = OwnedFd::from_raw_fd(check(libc::epoll_create1(libc::EPOLL_CLOEXEC))?);
            let wakeup = OwnedFd::from_raw_fd(check(libc::eventfd(
                0,
                libc::EFD_CLOEXEC | libc::EFD_NONBLOCK,
            ))?);
            let poller = Poller { epoll, wakeup };
            let mut event = libc::epoll_event {
                events: libc::EPOLLIN as u32,
                u64: WAKEUP,
            };
            check(libc::epoll_ctl(
                poller.epoll.as_raw_fd(),
                libc::EPOLL_CTL_ADD,
                poller.wakeup.as_raw_fd(),
                &mut event,
            ))?;
            Ok(poller)
        }
    }

    /// Registers `fd` for `interest`, or changes its registration when
    /// `registered`.
    pub fn set(&self, fd: RawFd, interest: Interest, registered: bool) -> io::Result<()> {
        let mut events = 0;
        if interest.read {
            events |= libc::EPOLLIN | libc::EPOLLRDHUP;
        }
        if interest.write {
            events |= libc::EPOLLOUT;
        }
        let mut event = libc::epoll_event {
            events: events as u32,
            u64: fd as u64,
        };
        let op = if registered {
            libc::EPOLL_CTL_MOD
        } else {
            libc::EPOLL_CTL_ADD
        };
        // SAFETY: a system call on our epoll instance.
        check(unsafe { libc::epoll_ctl(self.epoll.as_raw_fd(), op, fd, &mut event) })?;
        Ok(())
    }

    /// Removes the registration of `fd`. A file descriptor closed since
    /// it was registered is no longer registered, which is not an error.
    pub fn remove(&self, fd: RawFd) {
        // SAFETY: as above; the event is ignored for a removal.
        unsafe {
            libc::epoll_ctl(
                self.epoll.as_raw_fd(),
                libc::EPOLL_CTL_DEL,
                fd,
                std::ptr::null_mut(),
            );
        }
    }

    /// Waits until a registered file descriptor is ready, `notify` is
    /// called or `timeout` passes, and puts what became ready into
    /// `events`; none to wait without end. A signal ends the wait early
    /// with no events.
    pub fn wait(&self, timeout: Option<Duration>, events: &mut Vec<Event>) -> io::Result<()> {
        events.clear();
        // Rounded up, so a timer is not reached early and waited for again.
        let ms = timeout.map_or(-1, |t| {
            t.as_nanos()
                .div_ceil(1_000_000)
                .min(libc::c_int::MAX as u128) as libc::c_int
        });
        let mut raw = [libc::epoll_event { events: 0, u64: 0 }; MAX_EVENTS];
        // SAFETY: the buffer holds `MAX_EVENTS` events.
        let n = unsafe {
            libc::epoll_wait(
                self.epoll.as_raw_fd(),
                raw.as_mut_ptr(),
                MAX_EVENTS as libc::c_int,
                ms,
            )
        };
        if n < 0 {
            let error = io::Error::last_os_error();
            return match error.kind() {
                io::ErrorKind::Interrupted => Ok(()),
                _ => Err(error),
            };
        }
        for event in &raw[..n as usize] {
            let token = event.u64;
            if token == WAKEUP {
                let mut count = 0u64;
                // SAFETY: reads the eventfd's eight-byte counter, which
                // resets it.
                unsafe {
                    libc::read(
                        self.wakeup.as_raw_fd(),
                        (&raw mut count).cast(),
                        std::mem::size_of::<u64>(),
                    );
                }
                continue;
            }
            let flags = event.events as libc::c_int;
            let failed = flags & (libc::EPOLLERR | libc::EPOLLHUP) != 0;
            events.push(Event {
                fd: token as RawFd,
                ready: Interest {
                    read: failed || flags & (libc::EPOLLIN | libc::EPOLLRDHUP) != 0,
                    write: failed || flags & libc::EPOLLOUT != 0,
                },
            });
        }
        Ok(())
    }

    /// Ends a wait of another thread at once, or the next one if none is
    /// under way.
    pub fn notify(&self) {
        let one = 1u64;
        // SAFETY: adds to the eventfd's counter. It fails only when the
        // counter is about to overflow, and then a wake is pending anyway.
        unsafe {
            libc::write(
                self.wakeup.as_raw_fd(),
                (&raw const one).cast(),
                std::mem::size_of::<u64>(),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    /// A non-blocking pipe: its read end and write end.
    pub(crate) fn pipe() -> (OwnedFd, OwnedFd) {
        let mut fds = [0; 2];
        // SAFETY: the call fills both descriptors, which are then owned.
        unsafe {
            check(libc::pipe2(
                fds.as_mut_ptr(),
                libc::O_NONBLOCK | libc::O_CLOEXEC,
            ))
            .unwrap();
            (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1]))
        }
    }

    fn write(fd: &OwnedFd, bytes: &[u8]) {
        // SAFETY: writes from a live buffer.
        let n = unsafe { libc::write(fd.as_raw_fd(), bytes.as_ptr().cast(), bytes.len()) };
        assert_eq!(n, bytes.len() as isize);
    }

    #[test]
    fn a_readable_pipe_is_reported_until_it_is_removed() {
        let poller = Poller::new().unwrap();
        let (r, w) = pipe();
        let mut events = Vec::new();
        poller.set(r.as_raw_fd(), Interest::READ, false).unwrap();
        poller
            .wait(Some(Duration::from_millis(1)), &mut events)
            .unwrap();
        assert!(events.is_empty());
        write(&w, b"x");
        poller.wait(None, &mut events).unwrap();
        assert_eq!(
            events,
            [Event {
                fd: r.as_raw_fd(),
                ready: Interest::READ
            }]
        );
        // Level-triggered: still ready.
        poller.wait(None, &mut events).unwrap();
        assert_eq!(events.len(), 1);
        poller.remove(r.as_raw_fd());
        poller
            .wait(Some(Duration::from_millis(1)), &mut events)
            .unwrap();
        assert!(events.is_empty());
    }

    #[test]
    fn a_changed_registration_reports_the_new_interest() {
        let poller = Poller::new().unwrap();
        let (r, w) = pipe();
        let mut events = Vec::new();
        poller.set(w.as_raw_fd(), Interest::READ, false).unwrap();
        poller
            .wait(Some(Duration::from_millis(1)), &mut events)
            .unwrap();
        assert!(events.is_empty());
        poller.set(w.as_raw_fd(), Interest::WRITE, true).unwrap();
        poller.wait(None, &mut events).unwrap();
        assert_eq!(events[0].fd, w.as_raw_fd());
        assert!(events[0].ready.write);
        // Adding a registered descriptor again is an error.
        assert!(poller.set(w.as_raw_fd(), Interest::WRITE, false).is_err());
        drop(r);
        // Its reader closed: an error, reported as ready for both.
        poller.wait(None, &mut events).unwrap();
        assert_eq!(events[0].ready, Interest::READ.union(Interest::WRITE));
    }

    #[test]
    fn notify_ends_a_wait_and_the_timeout_ends_it_too() {
        let poller = std::sync::Arc::new(Poller::new().unwrap());
        let other = poller.clone();
        let t = std::thread::spawn(move || {
            std::thread::sleep(Duration::from_millis(20));
            other.notify();
        });
        let start = Instant::now();
        let mut events = Vec::new();
        poller.wait(None, &mut events).unwrap();
        assert!(events.is_empty());
        t.join().unwrap();
        // The notification was consumed: the next wait times out.
        let start2 = Instant::now();
        poller
            .wait(Some(Duration::from_millis(15)), &mut events)
            .unwrap();
        assert!(start2.elapsed() >= Duration::from_millis(15));
        assert!(start.elapsed() >= Duration::from_millis(20));
        // A notification before the wait ends it at once.
        poller.notify();
        poller
            .wait(Some(Duration::from_secs(10)), &mut events)
            .unwrap();
        assert!(start2.elapsed() < Duration::from_secs(5));
    }
}
