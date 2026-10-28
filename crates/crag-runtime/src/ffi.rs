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

//! Calls of C functions (Specification §16): the arguments from the words
//! generated code leaves, the C calling convention of x86-64 System V, the
//! library's thread safety, out parameters and `errno`.

use std::sync::mpsc;
use std::sync::{Mutex, PoisonError};

use crag_abi::{HEADER_SIZE, NativeJob, NativeLibrary, c_kind, threading};

use crate::fiber::TaskContext;
use crate::system::worker_of;
use crate::text::{TextWords, in_buffer, make_text};

/// The C result's word and the class of a float result, as `rt_c_call`
/// returns them.
#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CResult(pub u64, pub u64);

system_stack_fn! {
    /// `rt_c_call(ctx, library, func, desc, buf) -> (result, class)`: see
    /// `crag_abi::RuntimeFn::CCall`.
    fn rt_c_call(
        ctx: *const TaskContext,
        library: *const NativeLibrary,
        func: usize,
        desc: *const u8,
        buf: *mut u64
    ) -> CResult => call_entry
}

system_stack_fn! {
    /// `rt_c_str_of(ctx, address, nul) -> (w0, w1)`: see
    /// `crag_abi::RuntimeFn::CStrOf`.
    fn rt_c_str_of(ctx: *const TaskContext, address: u64, nul: u64) -> TextWords => str_of_entry
}

/// The registers and the stack words of a call: six integer registers,
/// then eight vector registers.
struct Args {
    regs: [u64; 14],
    stack: Vec<u64>,
}

/// What came back: rax, rdx and xmm0.
type Raw = [u64; 3];

/// The Rust half of `rt_c_call`, on the system stack.
///
/// # Safety
///
/// Called only by `rt_c_call`, with a loaded library, the address of a C
/// function of it whose parameters and result the descriptor describes,
/// and a buffer of a word per parameter and one more, whose `CStr`s are
/// live boxes.
unsafe extern "C" fn call_entry(
    _ctx: *const TaskContext,
    library: *const NativeLibrary,
    func: usize,
    desc: *const u8,
    buf: *mut u64,
) -> CResult {
    // SAFETY: as the caller promises.
    unsafe {
        let library = &*library;
        let count = *desc as usize;
        let result = *desc.add(1);
        let kinds = std::slice::from_raw_parts(desc.add(2), count);
        let args = arguments(kinds, buf);
        let call = move || {
            let mut raw: Raw = [0; 3];
            c_invoke(
                func,
                args.regs.as_ptr(),
                args.stack.as_ptr(),
                args.stack.len(),
                raw.as_mut_ptr(),
            );
            (raw, *libc::__errno_location())
        };
        let (raw, errno) = match library.threading {
            threading::SAFE => call(),
            threading::BOUND => on_own_thread(library, call),
            _ => {
                let _held = library.lock.lock().unwrap_or_else(PoisonError::into_inner);
                call()
            }
        };
        for (i, &kind) in kinds.iter().enumerate() {
            if kind & c_kind::OUT != 0 {
                let slot = buf.add(i);
                *slot = extend(kind & !c_kind::OUT, *slot);
            }
        }
        *buf.add(count) = errno as i64 as u64;
        match result {
            c_kind::VOID => CResult(0, 0),
            c_kind::F64 => CResult(raw[2], class(f64::from_bits(raw[2]))),
            c_kind::F32 => {
                let bits = raw[2] & 0xffff_ffff;
                CResult(bits, class(f32::from_bits(bits as u32).into()))
            }
            kind => CResult(extend(kind, raw[0]), 0),
        }
    }
}

/// Where the arguments go: integers and pointers in the six integer
/// registers, floats in the eight vector registers, the rest on the stack
/// in order.
///
/// # Safety
///
/// As for `call_entry`.
unsafe fn arguments(kinds: &[u8], buf: *mut u64) -> Args {
    let mut args = Args {
        regs: [0; 14],
        stack: Vec::new(),
    };
    let (mut ints, mut floats) = (0, 0);
    for (i, &kind) in kinds.iter().enumerate() {
        // SAFETY: the buffer has a word per parameter, and a `CStr`'s is a
        // live box.
        let word = unsafe {
            let slot = buf.add(i);
            match kind {
                _ if kind & c_kind::OUT != 0 => slot as u64,
                c_kind::CSTR => cstr_address(*slot),
                c_kind::OPT_CSTR if *slot == 0 => 0,
                c_kind::OPT_CSTR => cstr_address(*slot),
                _ => *slot,
            }
        };
        let float = matches!(kind, c_kind::F64 | c_kind::F32);
        if float && floats < 8 {
            args.regs[6 + floats] = word;
            floats += 1;
        } else if !float && ints < 6 {
            args.regs[ints] = word;
            ints += 1;
        } else {
            args.stack.push(word);
        }
    }
    args
}

/// The address of the NUL-terminated bytes of a `CStr`, from its box: in
/// the box itself when they are inline, else in their buffer.
///
/// # Safety
///
/// `cstr` is a live box of a `CStr`, whose bytes end in a NUL.
unsafe fn cstr_address(cstr: u64) -> u64 {
    let field = cstr + u64::from(HEADER_SIZE);
    // SAFETY: as the caller promises: the field holds the bytes' words.
    let (w0, w1) = unsafe { (*(field as *const u64), *((field + 8) as *const u64)) };
    if in_buffer(w0) {
        w0 + u64::from(HEADER_SIZE) + (w1 >> 32)
    } else {
        // The bytes follow the length byte.
        field + 1
    }
}

/// The class of a float: 0 finite, 1 NaN, 2 positive and 3 negative
/// infinity (Specification §3.1.4).
fn class(x: f64) -> u64 {
    match x {
        _ if x.is_nan() => 1,
        f64::INFINITY => 2,
        f64::NEG_INFINITY => 3,
        _ => 0,
    }
}

/// A C value of a kind, from a word whose upper bits may be anything,
/// extended to a word as Crag keeps it.
fn extend(kind: u8, word: u64) -> u64 {
    match kind {
        c_kind::I8 => word as i8 as i64 as u64,
        c_kind::I16 => word as i16 as i64 as u64,
        c_kind::I32 => word as i32 as i64 as u64,
        c_kind::U8 => word & 0xff,
        c_kind::U16 => word & 0xffff,
        c_kind::U32 | c_kind::F32 => word & 0xffff_ffff,
        _ => word,
    }
}

/// Runs a call on the library's own thread, started with its first call,
/// and waits for it (Specification §16.4).
fn on_own_thread<T: Send + 'static>(
    library: &NativeLibrary,
    call: impl FnOnce() -> T + Send + 'static,
) -> T {
    let sender = library.thread.get_or_init(|| {
        let (jobs, inbox) = mpsc::channel::<NativeJob>();
        std::thread::Builder::new()
            .name("crag-native".into())
            .spawn(move || {
                for job in inbox {
                    job();
                }
            })
            .unwrap_or_else(|e| crate::die(&format!("starting a native library's thread: {e}")));
        Mutex::new(jobs)
    });
    let (reply, answer) = mpsc::sync_channel(1);
    let job: NativeJob = Box::new(move || {
        let _ = reply.send(call());
    });
    let sent = sender
        .lock()
        .unwrap_or_else(PoisonError::into_inner)
        .send(job);
    match (sent, answer.recv()) {
        (Ok(()), Ok(value)) => value,
        _ => crate::die("a native library's thread ended"),
    }
}

/// Calls `func` with the registers and the stack words, and stores rax,
/// rdx and xmm0 in `out`.
///
/// # Safety
///
/// `func` is a C function that takes what the registers and stack words
/// hold, and `out` has room for three words.
#[unsafe(naked)]
unsafe extern "C" fn c_invoke(
    func: usize,
    regs: *const u64,
    stack: *const u64,
    count: usize,
    out: *mut u64,
) {
    std::arch::naked_asm!(
        "push rbp",
        "mov rbp, rsp",
        "push rbx",
        "push r12",
        "mov rbx, r8",
        "mov r10, rdi",
        "mov r11, rsi",
        // The stack words, last first, so that the call sees the stack
        // pointer aligned to 16 bytes.
        "test rcx, 1",
        "jz 2f",
        "sub rsp, 8",
        "2:",
        "test rcx, rcx",
        "jz 3f",
        "dec rcx",
        "push qword ptr [rdx + rcx * 8]",
        "jmp 2b",
        "3:",
        "movsd xmm0, qword ptr [r11 + 48]",
        "movsd xmm1, qword ptr [r11 + 56]",
        "movsd xmm2, qword ptr [r11 + 64]",
        "movsd xmm3, qword ptr [r11 + 72]",
        "movsd xmm4, qword ptr [r11 + 80]",
        "movsd xmm5, qword ptr [r11 + 88]",
        "movsd xmm6, qword ptr [r11 + 96]",
        "movsd xmm7, qword ptr [r11 + 104]",
        "mov rdi, [r11]",
        "mov rsi, [r11 + 8]",
        "mov rdx, [r11 + 16]",
        "mov rcx, [r11 + 24]",
        "mov r8, [r11 + 32]",
        "mov r9, [r11 + 40]",
        // A variadic function reads the number of vector registers used
        // from al; eight is an upper bound.
        "mov eax, 8",
        "call r10",
        "mov [rbx], rax",
        "mov [rbx + 8], rdx",
        "movsd qword ptr [rbx + 16], xmm0",
        "lea rsp, [rbp - 16]",
        "pop r12",
        "pop rbx",
        "pop rbp",
        "ret",
    )
}

/// The Rust half of `rt_c_str_of`, on the system stack.
///
/// # Safety
///
/// Called only by `rt_c_str_of`, with the address of NUL-terminated
/// bytes.
unsafe extern "C" fn str_of_entry(ctx: *const TaskContext, address: u64, nul: u64) -> TextWords {
    // SAFETY: as the caller promises.
    unsafe {
        let (heap, _) = worker_of(ctx);
        let c = std::ffi::CStr::from_ptr(address as *const libc::c_char);
        let bytes = match nul {
            0 => c.to_bytes(),
            _ => c.to_bytes_with_nul(),
        };
        let [w0, w1] = make_text(heap, &[bytes]);
        TextWords(w0, w1)
    }
}
