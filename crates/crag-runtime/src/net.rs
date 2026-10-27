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

//! Sockets for `std.io` (Plan §11.7.14): listening and connecting on the
//! loopback interface, connecting to a host by name, and reading and
//! writing whole `Bytes` values over the suspending reads and writes of
//! `io`.
//!
//! A socket is a non-blocking descriptor in the box of a `RuntimeSocket`,
//! closed with the box. A read takes a buffer from `rt_io_buffer`, which
//! `rt_io_read` fills and `rt_io_bytes` turns into a value. A write that
//! must wait keeps the bytes of an inline value in the task context, since
//! the words it was given do not outlive the call.

use std::mem::size_of;

use crag_abi::{BUFFER_HEADER, COUNT_OFFSET, HEADER_SIZE, INLINE_TEXT_MAX, TYPE_INDEX_OFFSET};

use crate::cancel::stop_if_due;
use crate::fiber::TaskContext;
use crate::heap::Heap;
use crate::io::{Words, perform};
use crate::reactor::IoOp;
use crate::system::worker_of;
use crate::text::{bytes_of, in_buffer, make_text};

/// The error number of the last failed call.
fn errno() -> u64 {
    std::io::Error::last_os_error()
        .raw_os_error()
        .unwrap_or(libc::EIO) as u64
}

/// The loopback address with a port.
fn loopback(port: u64) -> libc::sockaddr_in {
    libc::sockaddr_in {
        sin_family: libc::AF_INET as libc::sa_family_t,
        sin_port: (port as u16).to_be(),
        sin_addr: libc::in_addr {
            s_addr: u32::from(std::net::Ipv4Addr::LOCALHOST).to_be(),
        },
        sin_zero: [0; 8],
    }
}

/// A new non-blocking TCP socket, closed on exec: its descriptor or the
/// error number.
fn socket() -> Result<i32, u64> {
    socket_of(libc::AF_INET)
}

fn socket_of(family: libc::c_int) -> Result<i32, u64> {
    // SAFETY: plain system calls.
    let fd = unsafe {
        libc::socket(
            family,
            libc::SOCK_STREAM | libc::SOCK_NONBLOCK | libc::SOCK_CLOEXEC,
            0,
        )
    };
    if fd < 0 { Err(errno()) } else { Ok(fd) }
}

system_stack_fn! {
    /// `rt_io_listen(ctx, port) -> (fd, errno)`: see
    /// `crag_abi::RuntimeFn::IoListen`.
    fn rt_io_listen(ctx: *const TaskContext, port: u64) -> Words => listen_entry
}

/// The Rust half of `rt_io_listen`.
///
/// # Safety
///
/// Called only by `rt_io_listen`.
unsafe extern "C" fn listen_entry(_ctx: *const TaskContext, port: u64) -> Words {
    let fd = match socket() {
        Ok(fd) => fd,
        Err(errno) => return Words(0, errno),
    };
    let address = loopback(port);
    let one: libc::c_int = 1;
    // SAFETY: plain system calls on the new socket, with values that live
    // across them.
    let failed = unsafe {
        libc::setsockopt(
            fd,
            libc::SOL_SOCKET,
            libc::SO_REUSEADDR,
            (&raw const one).cast(),
            size_of::<libc::c_int>() as libc::socklen_t,
        ) < 0
            || libc::bind(
                fd,
                (&raw const address).cast(),
                size_of::<libc::sockaddr_in>() as libc::socklen_t,
            ) < 0
            || libc::listen(fd, 1024) < 0
    };
    if failed {
        let errno = errno();
        // SAFETY: the socket is ours.
        unsafe { libc::close(fd) };
        return Words(0, errno);
    }
    Words(fd as u64, 0)
}

system_stack_fn! {
    /// `rt_io_port(ctx, fd) -> port`: see `crag_abi::RuntimeFn::IoPort`.
    fn rt_io_port(ctx: *const TaskContext, fd: u64) -> u64 => port_entry
}

/// The Rust half of `rt_io_port`.
///
/// # Safety
///
/// Called only by `rt_io_port`.
unsafe extern "C" fn port_entry(_ctx: *const TaskContext, fd: u64) -> u64 {
    let mut address = loopback(0);
    let mut len = size_of::<libc::sockaddr_in>() as libc::socklen_t;
    // SAFETY: the address has room for what the call writes.
    let found = unsafe { libc::getsockname(fd as i32, (&raw mut address).cast(), &mut len) };
    if found < 0 {
        return 0;
    }
    u64::from(u16::from_be(address.sin_port))
}

system_stack_fn! {
    /// `rt_io_socket(ctx) -> (fd, errno)`: see `crag_abi::RuntimeFn::IoSocket`.
    fn rt_io_socket(ctx: *const TaskContext) -> Words => socket_entry
}

/// The Rust half of `rt_io_socket`.
///
/// # Safety
///
/// Called only by `rt_io_socket`.
unsafe extern "C" fn socket_entry(_ctx: *const TaskContext) -> Words {
    match socket() {
        Ok(fd) => Words(fd as u64, 0),
        Err(errno) => Words(0, errno),
    }
}

suspending_fn! {
    /// `rt_io_connect_local(ctx, fd, port) -> (0, errno)`: see
    /// `crag_abi::RuntimeFn::IoConnectLocal`.
    fn rt_io_connect_local(ctx: *const TaskContext, fd: u64, port: u64) -> Words => connect_entry
}

/// The Rust half of `rt_io_connect_local`: starts the connection, then
/// waits until it is made.
///
/// # Safety
///
/// Called only by `rt_io_connect_local`.
unsafe extern "C" fn connect_entry(ctx: *const TaskContext, fd: u64, port: u64) -> Words {
    // SAFETY: as the caller promises.
    if stop_if_due(unsafe { &*ctx }) {
        return Words(0, 0);
    }
    let address = loopback(port);
    let fd = fd as i32;
    // SAFETY: the address lives across the call, which only reads it.
    let started = unsafe {
        libc::connect(
            fd,
            (&raw const address).cast(),
            size_of::<libc::sockaddr_in>() as libc::socklen_t,
        )
    };
    if started == 0 {
        return Words(0, 0);
    }
    let errno = errno();
    if errno != libc::EINPROGRESS as u64 && errno != libc::EINTR as u64 {
        return Words(0, errno);
    }
    // SAFETY: the operation has no buffer.
    unsafe { perform(ctx, IoOp::Connect { fd }) }
}

system_stack_fn! {
    /// `rt_io_buffer(ctx, len) -> buffer`: see
    /// `crag_abi::RuntimeFn::IoBuffer`.
    fn rt_io_buffer(ctx: *const TaskContext, len: u64) -> u64 => buffer_entry
}

/// The Rust half of `rt_io_buffer`.
///
/// # Safety
///
/// Called only by `rt_io_buffer`.
unsafe extern "C" fn buffer_entry(ctx: *const TaskContext, len: u64) -> u64 {
    // SAFETY: as the caller promises.
    let (heap, _) = unsafe { worker_of(ctx) };
    buffer(heap, len as usize) as u64
}

/// A buffer of a string or bytes with room for `len` bytes.
fn buffer(heap: &mut Heap, len: usize) -> *mut u8 {
    let ptr = heap.alloc(HEADER_SIZE as usize + len.max(1));
    // SAFETY: the block holds the header.
    unsafe {
        ptr.offset(COUNT_OFFSET as isize).cast::<u64>().write(1);
        ptr.offset(TYPE_INDEX_OFFSET as isize)
            .cast::<u64>()
            .write(BUFFER_HEADER);
    }
    ptr
}

system_stack_fn! {
    /// `rt_io_bytes(ctx, buffer, n) -> (w0, w1)`: see
    /// `crag_abi::RuntimeFn::IoBytes`.
    fn rt_io_bytes(ctx: *const TaskContext, buffer: *mut u8, n: u64) -> Words => bytes_entry
}

/// The Rust half of `rt_io_bytes`.
///
/// # Safety
///
/// Called only by `rt_io_bytes`, with a buffer from `rt_io_buffer` that
/// holds `n` bytes read, whose reference it takes.
unsafe extern "C" fn bytes_entry(ctx: *const TaskContext, buffer: *mut u8, n: u64) -> Words {
    // SAFETY: as the caller promises.
    let (heap, _) = unsafe { worker_of(ctx) };
    if n as usize > INLINE_TEXT_MAX {
        return Words(buffer as u64, n);
    }
    // SAFETY: as the caller promises, the buffer holds `n` bytes.
    let bytes = unsafe { std::slice::from_raw_parts(buffer.add(HEADER_SIZE as usize), n as usize) };
    let [w0, w1] = make_text(heap, &[bytes]);
    // SAFETY: the buffer was the caller's, and its bytes are copied.
    unsafe { heap.free(buffer) };
    Words(w0, w1)
}

suspending_fn! {
    /// `rt_io_write_bytes(ctx, fd, w0, w1, left) -> (left, errno)`: see
    /// `crag_abi::RuntimeFn::IoWriteBytes`.
    fn rt_io_write_bytes(ctx: *const TaskContext, fd: u64, w0: u64, w1: u64, left: u64) -> Words => write_entry
}

/// The Rust half of `rt_io_write_bytes`.
///
/// # Safety
///
/// Called only by `rt_io_write_bytes`, with a bytes value that the caller
/// holds until the call returns.
unsafe extern "C" fn write_entry(
    ctx: *const TaskContext,
    fd: u64,
    w0: u64,
    w1: u64,
    left: u64,
) -> Words {
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let bytes = unsafe { bytes_of(&words) };
    let start = match left {
        u64::MAX => 0,
        left => bytes.len() - (left as usize).min(bytes.len()),
    };
    let rest = &bytes[start..];
    let buf = match in_buffer(w0) {
        // The buffer stays with the caller.
        true => rest.as_ptr(),
        // The words do not outlive the call, but the task's hold does.
        false => {
            // SAFETY: as the caller promises.
            let mut hold = unsafe { &*ctx }.io_hold.lock().unwrap();
            hold.clear();
            hold.extend_from_slice(rest);
            hold.as_ptr()
        }
    };
    let op = IoOp::Write {
        fd: fd as i32,
        buf,
        len: rest.len(),
    };
    // SAFETY: the bytes stay where they are until the fiber continues.
    let Words(n, errno) = unsafe { perform(ctx, op) };
    if errno != 0 {
        return Words(0, errno);
    }
    Words((rest.len() as u64).saturating_sub(n), 0)
}

/// Closes the socket of a `RuntimeSocket` box being freed.
pub(crate) fn close(fd: u64) {
    // SAFETY: the socket is the box's, and no task uses it any more.
    unsafe { libc::close(fd as i32) };
}

system_stack_fn! {
    /// `rt_io_socket_any(ctx) -> (fd, errno)`: see
    /// `crag_abi::RuntimeFn::IoSocketAny`.
    fn rt_io_socket_any(ctx: *const TaskContext) -> Words => socket_any_entry
}

/// The Rust half of `rt_io_socket_any`: an IPv6 socket that also reaches
/// IPv4 addresses, as mapped ones, or an IPv4 socket where the system has
/// no IPv6.
///
/// # Safety
///
/// Called only by `rt_io_socket_any`.
unsafe extern "C" fn socket_any_entry(_ctx: *const TaskContext) -> Words {
    let fd = match socket_of(libc::AF_INET6) {
        Ok(fd) => fd,
        Err(e) if e == libc::EAFNOSUPPORT as u64 => match socket() {
            Ok(fd) => return Words(fd as u64, 0),
            Err(errno) => return Words(0, errno),
        },
        Err(errno) => return Words(0, errno),
    };
    let zero: libc::c_int = 0;
    // SAFETY: a plain system call on the new socket, with a value that
    // lives across it.
    let failed = unsafe {
        libc::setsockopt(
            fd,
            libc::IPPROTO_IPV6,
            libc::IPV6_V6ONLY,
            (&raw const zero).cast(),
            size_of::<libc::c_int>() as libc::socklen_t,
        ) < 0
    };
    if failed {
        let errno = errno();
        // SAFETY: the socket is ours.
        unsafe { libc::close(fd) };
        return Words(0, errno);
    }
    Words(fd as u64, 0)
}

/// The address family of a socket.
fn family(fd: i32) -> Result<libc::c_int, u64> {
    // SAFETY: the storage has room for any address the call writes.
    unsafe {
        let mut address: libc::sockaddr_storage = std::mem::zeroed();
        let mut len = size_of::<libc::sockaddr_storage>() as libc::socklen_t;
        if libc::getsockname(fd, (&raw mut address).cast(), &mut len) < 0 {
            return Err(errno());
        }
        Ok(libc::c_int::from(address.ss_family))
    }
}

/// The addresses of a host by name, IPv4 ones first, since a system
/// without an IPv6 route still often resolves IPv6 addresses.
fn resolve(host: &[u8], port: u16) -> Vec<std::net::SocketAddr> {
    use std::net::ToSocketAddrs;
    let Ok(host) = std::str::from_utf8(host) else {
        return Vec::new();
    };
    let mut addresses: Vec<_> = (host, port)
        .to_socket_addrs()
        .map(Iterator::collect)
        .unwrap_or_default();
    addresses.sort_by_key(|a| a.is_ipv6());
    addresses
}

suspending_fn! {
    /// `rt_io_connect_host(ctx, fd, w0, w1, port) -> (0, errno)`: see
    /// `crag_abi::RuntimeFn::IoConnectHost`.
    fn rt_io_connect_host(ctx: *const TaskContext, fd: u64, w0: u64, w1: u64, port: u64) -> Words
        => connect_host_entry
}

/// The Rust half of `rt_io_connect_host`: looks the host up, starts the
/// connection to its first address the socket can reach, then waits until
/// it is made. The lookup blocks the worker while the system resolves the
/// name.
///
/// # Safety
///
/// Called only by `rt_io_connect_host`, with a string the caller holds
/// until the call returns.
unsafe extern "C" fn connect_host_entry(
    ctx: *const TaskContext,
    fd: u64,
    w0: u64,
    w1: u64,
    port: u64,
) -> Words {
    use std::net::SocketAddr;
    // SAFETY: as the caller promises.
    if stop_if_due(unsafe { &*ctx }) {
        return Words(0, 0);
    }
    let Ok(port) = u16::try_from(port) else {
        return Words(0, libc::EINVAL as u64);
    };
    let fd = fd as i32;
    let six = match family(fd) {
        Ok(family) => family == libc::AF_INET6,
        Err(errno) => return Words(0, errno),
    };
    let words = [w0, w1];
    // SAFETY: as the caller promises.
    let addresses = resolve(unsafe { bytes_of(&words) }, port);
    if addresses.is_empty() {
        return Words(0, crag_abi::UNKNOWN_HOST);
    }
    let Some(address) = addresses.iter().find(|a| six || a.is_ipv4()) else {
        return Words(0, libc::EAFNOSUPPORT as u64);
    };
    let started = match (six, address) {
        (false, SocketAddr::V4(a)) => {
            let mut address = loopback(u64::from(a.port()));
            address.sin_addr.s_addr = u32::from(*a.ip()).to_be();
            // SAFETY: the address lives across the call, which only reads it.
            unsafe {
                libc::connect(
                    fd,
                    (&raw const address).cast(),
                    size_of::<libc::sockaddr_in>() as libc::socklen_t,
                )
            }
        }
        (_, a) => {
            let (ip, scope) = match a {
                SocketAddr::V4(a) => (a.ip().to_ipv6_mapped(), 0),
                SocketAddr::V6(a) => (*a.ip(), a.scope_id()),
            };
            // SAFETY: an all-zero address is a valid one to fill in.
            let mut address: libc::sockaddr_in6 = unsafe { std::mem::zeroed() };
            address.sin6_family = libc::AF_INET6 as libc::sa_family_t;
            address.sin6_port = a.port().to_be();
            address.sin6_addr.s6_addr = ip.octets();
            address.sin6_scope_id = scope;
            // SAFETY: the address lives across the call, which only reads it.
            unsafe {
                libc::connect(
                    fd,
                    (&raw const address).cast(),
                    size_of::<libc::sockaddr_in6>() as libc::socklen_t,
                )
            }
        }
    };
    if started == 0 {
        return Words(0, 0);
    }
    let errno = errno();
    if errno != libc::EINPROGRESS as u64 && errno != libc::EINTR as u64 {
        return Words(0, errno);
    }
    // SAFETY: the operation has no buffer.
    unsafe { perform(ctx, IoOp::Connect { fd }) }
}
