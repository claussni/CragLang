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

//! The poller and the timers (Plan §11.7.2): fibers that sleep, read,
//! write, accept and connect without holding a worker.

use std::net::{Ipv4Addr, TcpListener};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::sync::Arc;
use std::time::{Duration, Instant};

mod common;

use common::{Image, r};
use crag_abi::RuntimeFn;
use crag_codegen::{BinOp, Block, BlockId, Cond, Inst, LirFunction, Term};
use crag_runtime::{Fiber, FiberConfig, FiberState, Scheduler, SchedulerConfig, Types, Worker};

/// A function of `params` parameters that calls runtime function `func`
/// with them and returns its `results` results.
fn calling(func: RuntimeFn, params: u32, results: u32) -> LirFunction {
    let args = (0..params).map(r).collect();
    let dsts: Vec<_> = (params..params + results).map(r).collect();
    LirFunction {
        params,
        returns: results,
        vregs: params + results,
        tracked: vec![],
        blocks: vec![Block {
            insts: vec![Inst::CallRuntime {
                func,
                args,
                dsts: dsts.clone(),
            }],
            term: Term::Return(dsts),
        }],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// `sleeper(nanos, id) = id`, after sleeping.
fn sleeper() -> LirFunction {
    LirFunction {
        params: 2,
        returns: 1,
        vregs: 2,
        tracked: vec![],
        blocks: vec![Block {
            insts: vec![Inst::CallRuntime {
                func: RuntimeFn::Sleep,
                args: vec![r(0)],
                dsts: vec![],
            }],
            term: Term::Return(vec![r(1)]),
        }],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

/// `count(n) = n`, counting down without waiting.
fn count() -> LirFunction {
    LirFunction {
        params: 1,
        returns: 1,
        vregs: 5, // n, left, zero, one, flag
        tracked: vec![],
        blocks: vec![
            Block {
                insts: vec![
                    Inst::Const {
                        dst: r(2),
                        value: 0,
                    },
                    Inst::Const {
                        dst: r(3),
                        value: 1,
                    },
                    Inst::Bin {
                        op: BinOp::Add,
                        dst: r(1),
                        a: r(0),
                        b: r(2),
                    },
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![Inst::Cmp {
                    cond: Cond::Gt,
                    dst: r(4),
                    a: r(1),
                    b: r(2),
                }],
                term: Term::Branch {
                    cond: r(4),
                    then: BlockId(2),
                    otherwise: BlockId(3),
                },
            },
            Block {
                insts: vec![
                    Inst::Bin {
                        op: BinOp::Sub,
                        dst: r(1),
                        a: r(1),
                        b: r(3),
                    },
                    Inst::Poll,
                ],
                term: Term::Jump(BlockId(1)),
            },
            Block {
                insts: vec![],
                term: Term::Return(vec![r(0)]),
            },
        ],
        data: Vec::new(),
        natives: Vec::new(),
    }
}

const SLEEP: usize = 0;
const READ: usize = 1;
const WRITE: usize = 2;
const ACCEPT: usize = 3;
const CONNECT: usize = 4;
const COUNT: usize = 5;

fn image() -> Image {
    Image::new(&[
        sleeper(),
        calling(RuntimeFn::IoRead, 3, 2),
        calling(RuntimeFn::IoWrite, 3, 2),
        calling(RuntimeFn::IoAccept, 1, 2),
        calling(RuntimeFn::IoConnect, 3, 2),
        count(),
    ])
}

fn scheduler(image: &mut Image, workers: usize) -> Scheduler {
    let code = Arc::new(std::mem::take(&mut image.code));
    Scheduler::new(
        SchedulerConfig {
            workers,
            slice: None,
        },
        Arc::new(Types::default()),
        code,
    )
}

fn ms(n: u64) -> Duration {
    Duration::from_millis(n)
}

fn sleeping(image: &mut Image, d: Duration, id: u64) -> Box<Fiber> {
    image.fiber(SLEEP, &[d.as_nanos() as u64, id], FiberConfig::default())
}

/// A fiber running an operation of two results on `fd` and a buffer.
fn on_buffer(image: &mut Image, func: usize, fd: RawFd, buf: *const u8, len: usize) -> Box<Fiber> {
    image.fiber_returning(
        func,
        &[fd as u64, buf as u64, len as u64],
        2,
        FiberConfig::default(),
    )
}

/// A non-blocking pipe: its read end and write end.
fn pipe() -> (OwnedFd, OwnedFd) {
    let mut fds = [0; 2];
    // SAFETY: the call fills both descriptors, which are then owned.
    unsafe {
        assert_eq!(
            libc::pipe2(fds.as_mut_ptr(), libc::O_NONBLOCK | libc::O_CLOEXEC),
            0
        );
        (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1]))
    }
}

fn write_all(fd: RawFd, bytes: &[u8]) {
    // SAFETY: writes from a live buffer.
    let n = unsafe { libc::write(fd, bytes.as_ptr().cast(), bytes.len()) };
    assert_eq!(n, bytes.len() as isize);
}

fn results(fibers: &[Box<Fiber>]) -> Vec<[u64; 2]> {
    fibers
        .iter()
        .map(|f| {
            assert_eq!(f.state(), FiberState::Finished);
            f.results().unwrap()
        })
        .collect()
}

#[test]
fn sleeping_fibers_do_not_hold_their_worker() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let start = Instant::now();
    let fibers = (0..50).map(|i| sleeping(&mut image, ms(100), i)).collect();
    scheduler.spawn_all(fibers);
    let stopped = scheduler.wait();
    assert_eq!(stopped.len(), 50);
    // Never early, and together, not one after the other.
    let elapsed = start.elapsed();
    assert!(elapsed >= ms(100), "{elapsed:?}");
    assert!(elapsed < ms(2000), "{elapsed:?}");
}

#[test]
fn sleepers_wake_in_the_order_of_their_deadlines() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let fibers = vec![
        sleeping(&mut image, ms(90), 90),
        sleeping(&mut image, ms(30), 30),
        sleeping(&mut image, ms(60), 60),
        // No time at all does not suspend.
        sleeping(&mut image, Duration::ZERO, 0),
    ];
    scheduler.spawn_all(fibers);
    let order: Vec<u64> = results(&scheduler.wait()).iter().map(|r| r[0]).collect();
    assert_eq!(order, [0, 30, 60, 90]);
}

#[test]
fn a_fiber_waiting_to_read_lets_another_run() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let (reader, writer) = pipe();
    let mut buf = vec![0u8; 16];
    scheduler.spawn(on_buffer(
        &mut image,
        READ,
        reader.as_raw_fd(),
        buf.as_mut_ptr(),
        buf.len(),
    ));
    scheduler.spawn(image.fiber(COUNT, &[1000], FiberConfig::default()));
    let w = writer.as_raw_fd();
    let t = std::thread::spawn(move || {
        std::thread::sleep(ms(50));
        write_all(w, b"hello");
    });
    let stopped = results(&scheduler.wait());
    t.join().unwrap();
    // The counter finished while the reader waited.
    assert_eq!(stopped, [[1000, 0], [5, 0]]);
    assert_eq!(&buf[..5], b"hello");
}

#[test]
fn the_end_of_the_input_reads_as_nothing() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let (reader, writer) = pipe();
    let mut buf = [0u8; 4];
    scheduler.spawn(on_buffer(
        &mut image,
        READ,
        reader.as_raw_fd(),
        buf.as_mut_ptr(),
        buf.len(),
    ));
    std::thread::sleep(ms(20));
    drop(writer);
    assert_eq!(results(&scheduler.wait()), [[0, 0]]);
}

#[test]
fn a_writer_to_a_full_pipe_waits_until_it_drains() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let (reader, writer) = pipe();
    let chunk = [7u8; 4096];
    // Fill the pipe.
    // SAFETY: writes from a live buffer.
    while unsafe { libc::write(writer.as_raw_fd(), chunk.as_ptr().cast(), chunk.len()) } > 0 {}
    scheduler.spawn(on_buffer(
        &mut image,
        WRITE,
        writer.as_raw_fd(),
        chunk.as_ptr(),
        chunk.len(),
    ));
    let r = reader.as_raw_fd();
    let t = std::thread::spawn(move || {
        std::thread::sleep(ms(30));
        let mut sink = vec![0u8; 1 << 20];
        // SAFETY: reads into a live buffer.
        let n = unsafe { libc::read(r, sink.as_mut_ptr().cast(), sink.len()) };
        assert!(n > 0);
    });
    let stopped = results(&scheduler.wait());
    t.join().unwrap();
    // At most a page goes into a pipe at once, and whole.
    assert_eq!(stopped, [[4096, 0]]);
}

#[test]
fn a_writer_to_a_full_pipe_learns_when_the_reader_goes() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let (reader, writer) = pipe();
    let chunk = [7u8; 4096];
    // Fill the pipe.
    // SAFETY: writes from a live buffer.
    while unsafe { libc::write(writer.as_raw_fd(), chunk.as_ptr().cast(), chunk.len()) } > 0 {}
    scheduler.spawn(on_buffer(
        &mut image,
        WRITE,
        writer.as_raw_fd(),
        chunk.as_ptr(),
        chunk.len(),
    ));
    let t = std::thread::spawn(move || {
        std::thread::sleep(ms(30));
        // The full pipe now reports only an error, never room to write.
        drop(reader);
    });
    let stopped = results(&scheduler.wait());
    t.join().unwrap();
    assert_eq!(stopped, [[0, libc::EPIPE as u64]]);
}

/// The bytes of a `sockaddr_in` for a port of the loopback address.
fn loopback(port: u16) -> Vec<u8> {
    let addr = libc::sockaddr_in {
        sin_family: libc::AF_INET as libc::sa_family_t,
        sin_port: port.to_be(),
        sin_addr: libc::in_addr {
            s_addr: u32::from(Ipv4Addr::LOCALHOST).to_be(),
        },
        sin_zero: [0; 8],
    };
    let size = std::mem::size_of::<libc::sockaddr_in>();
    // SAFETY: reads the plain struct's bytes.
    unsafe { std::slice::from_raw_parts((&raw const addr).cast::<u8>(), size).to_vec() }
}

fn socket() -> OwnedFd {
    // SAFETY: creates a socket, then owned.
    unsafe {
        let fd = libc::socket(
            libc::AF_INET,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        );
        assert!(fd >= 0);
        OwnedFd::from_raw_fd(fd)
    }
}

#[test]
fn accept_and_connect_wait_for_each_other() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let listener = TcpListener::bind((Ipv4Addr::LOCALHOST, 0)).unwrap();
    listener.set_nonblocking(true).unwrap();
    let port = listener.local_addr().unwrap().port();
    scheduler.spawn(image.fiber_returning(
        ACCEPT,
        &[listener.as_raw_fd() as u64],
        2,
        FiberConfig::default(),
    ));
    std::thread::sleep(ms(20));
    let client = socket();
    let addr = loopback(port);
    scheduler.spawn(on_buffer(
        &mut image,
        CONNECT,
        client.as_raw_fd(),
        addr.as_ptr(),
        addr.len(),
    ));
    let stopped = scheduler.wait();
    assert_eq!(stopped.len(), 2);
    let mut accepted = None;
    for [a, b] in results(&stopped) {
        assert_eq!(b, 0, "error {a} {b}");
        if a != 0 {
            accepted = Some(a as RawFd);
        }
    }
    // SAFETY: the accepted socket is ours to close.
    let accepted = unsafe { OwnedFd::from_raw_fd(accepted.expect("accepted")) };
    // It is non-blocking.
    // SAFETY: reads the descriptor's flags.
    let flags = unsafe { libc::fcntl(accepted.as_raw_fd(), libc::F_GETFL) };
    assert_ne!(flags & libc::O_NONBLOCK, 0);
}

#[test]
fn a_refused_connection_gives_its_error() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    // A port nobody listens on any more.
    let port = TcpListener::bind((Ipv4Addr::LOCALHOST, 0))
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    let client = socket();
    let addr = loopback(port);
    scheduler.spawn(on_buffer(
        &mut image,
        CONNECT,
        client.as_raw_fd(),
        addr.as_ptr(),
        addr.len(),
    ));
    assert_eq!(results(&scheduler.wait()), [[0, libc::ECONNREFUSED as u64]]);
}

#[test]
fn many_fibers_read_from_many_pipes_on_many_workers() {
    const PIPES: usize = 200;
    let mut image = image();
    let scheduler = scheduler(&mut image, 4);
    let pipes: Vec<(OwnedFd, OwnedFd)> = (0..PIPES).map(|_| pipe()).collect();
    let mut bufs = vec![[0u8; 8]; PIPES];
    let fibers = pipes
        .iter()
        .zip(&mut bufs)
        .map(|((reader, _), buf)| {
            on_buffer(
                &mut image,
                READ,
                reader.as_raw_fd(),
                buf.as_mut_ptr(),
                buf.len(),
            )
        })
        .collect();
    scheduler.spawn_all(fibers);
    let writers: Vec<RawFd> = pipes.iter().map(|(_, w)| w.as_raw_fd()).collect();
    let t = std::thread::spawn(move || {
        // In an order of their own, with pauses.
        for k in 0..PIPES {
            let i = (k * 37) % PIPES;
            write_all(writers[i], &(i as u64).to_le_bytes());
            if k % 50 == 0 {
                std::thread::sleep(ms(5));
            }
        }
    });
    let stopped = results(&scheduler.wait());
    t.join().unwrap();
    assert_eq!(stopped.len(), PIPES);
    assert!(stopped.iter().all(|r| *r == [8, 0]));
    for (i, buf) in bufs.iter().enumerate() {
        assert_eq!(u64::from_le_bytes(*buf), i as u64);
    }
}

#[test]
fn errors_come_back_at_once() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let mut buf = [0u8; 4];
    scheduler.spawn(on_buffer(&mut image, READ, -1, buf.as_mut_ptr(), 4));
    // A bad descriptor fails before anything waits.
    assert_eq!(results(&scheduler.wait()), [[0, libc::EBADF as u64]]);
}

#[test]
fn without_a_scheduler_a_fiber_blocks_its_thread() {
    let mut image = image();
    let mut worker = Worker::new();
    let start = Instant::now();
    let mut fiber = sleeping(&mut image, ms(30), 1);
    assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
    assert!(start.elapsed() >= ms(30));
    let (reader, writer) = pipe();
    let mut buf = [0u8; 4];
    let mut fiber = on_buffer(&mut image, READ, reader.as_raw_fd(), buf.as_mut_ptr(), 4);
    let w = writer.as_raw_fd();
    let t = std::thread::spawn(move || {
        std::thread::sleep(ms(20));
        write_all(w, b"ok");
    });
    assert_eq!(worker.resume(&mut fiber), FiberState::Finished);
    t.join().unwrap();
    assert_eq!(fiber.results(), Some([2, 0]));
    assert_eq!(&buf[..2], b"ok");
}

#[test]
fn dropping_the_scheduler_frees_the_fibers_that_wait() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 2);
    let (reader, _writer) = pipe();
    let mut buf = [0u8; 4];
    scheduler.spawn(sleeping(&mut image, Duration::from_secs(3600), 1));
    scheduler.spawn(on_buffer(
        &mut image,
        READ,
        reader.as_raw_fd(),
        buf.as_mut_ptr(),
        4,
    ));
    std::thread::sleep(ms(20));
    let start = Instant::now();
    drop(scheduler);
    assert!(start.elapsed() < Duration::from_secs(5));
}

#[test]
fn two_fibers_wait_on_one_descriptor_in_turn() {
    let mut image = image();
    let scheduler = scheduler(&mut image, 1);
    let (reader, writer) = pipe();
    let mut bufs = [[0u8; 1]; 2];
    let [a, b] = &mut bufs;
    let fibers = [a, b]
        .into_iter()
        .map(|buf| on_buffer(&mut image, READ, reader.as_raw_fd(), buf.as_mut_ptr(), 1))
        .collect();
    scheduler.spawn_all(fibers);
    let w = writer.as_raw_fd();
    let t = std::thread::spawn(move || {
        // Each byte goes to the one that waited longest.
        for byte in [b"x", b"y"] {
            std::thread::sleep(ms(20));
            write_all(w, byte);
        }
    });
    let stopped = results(&scheduler.wait());
    t.join().unwrap();
    assert_eq!(stopped, [[1, 0], [1, 0]]);
    assert_eq!(bufs, [*b"x", *b"y"]);
}
