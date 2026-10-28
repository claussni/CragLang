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

//! Native libraries and the C functions of them that code calls
//! (Specification §16.1). A library is opened once per process, the first
//! of its files that loads, and stays open.

use std::ffi::{CStr, CString};
use std::sync::{Mutex, OnceLock};

use crag_abi::NativeLibrary;

use crate::LoadError;

/// The libraries opened so far, by the files they were looked up by.
static LIBRARIES: Mutex<Vec<(Vec<String>, &'static NativeLibrary)>> = Mutex::new(Vec::new());

/// The library the files name, opened by the first of them that loads.
pub fn library(files: &[String], threading: u8) -> Result<&'static NativeLibrary, LoadError> {
    let mut libraries = LIBRARIES.lock().unwrap_or_else(|e| e.into_inner());
    if let Some((_, library)) = libraries.iter().find(|(f, _)| f == files) {
        return Ok(library);
    }
    let mut why = String::new();
    for file in files {
        let Ok(name) = CString::new(file.as_str()) else {
            continue;
        };
        // SAFETY: the name is NUL-terminated. Opening runs the library's
        // initializers, which is what binding it asks for.
        let handle = unsafe { libc::dlopen(name.as_ptr(), libc::RTLD_NOW | libc::RTLD_LOCAL) };
        if handle.is_null() {
            why = last_error();
            continue;
        }
        let library: &'static NativeLibrary = Box::leak(Box::new(NativeLibrary {
            handle: handle as usize,
            threading,
            lock: Mutex::new(()),
            thread: OnceLock::new(),
        }));
        libraries.push((files.to_vec(), library));
        return Ok(library);
    }
    Err(LoadError::NativeLibrary {
        files: files.join(", "),
        why,
    })
}

/// The address of a C function of a library.
pub fn symbol(library: &NativeLibrary, files: &[String], name: &str) -> Result<usize, LoadError> {
    let missing = || LoadError::NativeSymbol {
        files: files.join(", "),
        symbol: name.to_string(),
    };
    let c_name = CString::new(name).map_err(|_| missing())?;
    // SAFETY: the handle is an open library's, which stays open, and the
    // name is NUL-terminated.
    let address = unsafe { libc::dlsym(library.handle as *mut libc::c_void, c_name.as_ptr()) };
    if address.is_null() {
        return Err(missing());
    }
    Ok(address as usize)
}

/// What `dlerror` says went wrong last.
fn last_error() -> String {
    // SAFETY: `dlerror` returns null or a NUL-terminated message that stays
    // valid until the next call of it on this thread.
    unsafe {
        let message = libc::dlerror();
        if message.is_null() {
            String::new()
        } else {
            CStr::from_ptr(message).to_string_lossy().into_owned()
        }
    }
}
