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

//! Runtime archives and linking (Implementation Plan §11.10.4, §11.10.5).
//!
//! The runtime archive is the crate `crag-rt` built as a static library
//! for the target, `libcrag_rt.a`. A toolchain ships it, with the linker
//! and the target's C library and start files, under `lib/crag` beside
//! its `bin`: `lib/crag/bin/ld.lld`, and `lib/crag/<target>/` with the
//! archive, `crt1.o`, `crti.o`, `crtbegin.o`, `crtend.o`, `crtn.o`,
//! `libc.a` and `libunwind.a`. `CRAG_TOOLCHAIN` names another such
//! `lib/crag`. A toolchain built from source with cargo finds the archive
//! in its target directory, `<target>/release/libcrag_rt.a`, built by
//! `cargo build -p crag-rt --release --target <target>`, and takes the
//! linker, `rust-lld`, and the musl target's start files and C library
//! from the Rust toolchain.
//!
//! The linker is lld, which links for every target from any host. It links
//! statically and without PIE, with the inputs in a fixed order and without
//! a build id, so the executable depends only on its inputs.

use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// A target release executables are built for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Target {
    /// x86-64 Linux, linked statically against musl.
    X86_64Linux,
}

impl Target {
    /// The target the toolchain runs on.
    pub fn host() -> Target {
        Target::X86_64Linux
    }

    /// The Rust target the runtime archive is built for.
    pub fn triple(self) -> &'static str {
        match self {
            Target::X86_64Linux => "x86_64-unknown-linux-musl",
        }
    }
}

/// The name of the runtime archive.
const ARCHIVE: &str = "libcrag_rt.a";

/// The start files linked before the objects, and after the libraries.
const START: [&str; 3] = ["crt1.o", "crti.o", "crtbegin.o"];
const END: [&str; 2] = ["crtend.o", "crtn.o"];

/// The libraries of the target linked after the runtime archive.
const LIBRARIES: [&str; 2] = ["libc.a", "libunwind.a"];

/// How long a link may take before it is stopped.
const LINK_LIMIT: Duration = Duration::from_secs(120);

/// Why an executable could not be linked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkError(pub String);

impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for LinkError {}

/// The linker and what it links every executable of a target with.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Toolchain {
    /// lld, and the arguments that come first: `rust-lld` needs its flavor.
    pub lld: PathBuf,
    pub lld_args: Vec<String>,
    /// The directory of the target's start files and C library.
    pub lib: PathBuf,
}

impl Toolchain {
    /// The toolchain for the target: the one `CRAG_TOOLCHAIN` names, the
    /// one shipped beside the running executable, or the Rust toolchain's.
    pub fn find(target: Target) -> Result<Toolchain, LinkError> {
        if let Some(dir) = shipped_dir() {
            return Ok(Toolchain {
                lld: dir.join("bin").join("ld.lld"),
                lld_args: Vec::new(),
                lib: dir.join(target.triple()),
            });
        }
        let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
        let out = Command::new(&rustc)
            .args(["--print", "sysroot"])
            .stderr(Stdio::null())
            .output()
            .map_err(|e| LinkError(format!("no toolchain to link with: {e}")))?;
        if !out.status.success() {
            return Err(LinkError("no toolchain to link with".into()));
        }
        let rustlib =
            PathBuf::from(String::from_utf8_lossy(&out.stdout).trim()).join("lib/rustlib");
        Ok(Toolchain {
            lld: rustlib.join("x86_64-unknown-linux-gnu/bin/rust-lld"),
            lld_args: vec!["-flavor".into(), "gnu".into()],
            lib: rustlib.join(target.triple()).join("lib/self-contained"),
        })
    }
}

/// The `lib/crag` of a shipped toolchain: `CRAG_TOOLCHAIN`, or beside the
/// running executable's directory.
fn shipped_dir() -> Option<PathBuf> {
    if let Some(dir) = std::env::var_os("CRAG_TOOLCHAIN") {
        return Some(dir.into());
    }
    let exe = std::env::current_exe().ok()?;
    let dir = exe.parent()?.parent()?.join("lib/crag");
    dir.join("bin/ld.lld").is_file().then_some(dir)
}

/// The runtime archive for the target: the shipped one, or the one cargo
/// built into the target directory the running executable is in.
pub fn runtime_archive(target: Target) -> Result<PathBuf, LinkError> {
    let triple = target.triple();
    if let Some(dir) = shipped_dir() {
        let archive = dir.join(triple).join(ARCHIVE);
        if archive.is_file() {
            return Ok(archive);
        }
    }
    let exe = std::env::current_exe().map_err(|e| LinkError(e.to_string()))?;
    // `target/<profile>/crag`, or a test's `target/<profile>/deps/`.
    exe.ancestors()
        .skip(1)
        .take(3)
        .map(|dir| dir.join(triple).join("release").join(ARCHIVE))
        .find(|archive| archive.is_file())
        .ok_or_else(|| {
            LinkError(format!(
                "no runtime archive for {triple}; build it with \
                 `cargo build -p crag-rt --release --target {triple}`"
            ))
        })
}

/// Links the objects and archives into the executable `out` for the target,
/// with the toolchain's start files and C library.
pub fn link(
    objects: &[PathBuf],
    archives: &[PathBuf],
    target: Target,
    out: &Path,
) -> Result<(), LinkError> {
    let toolchain = Toolchain::find(target)?;
    link_with(&toolchain, objects, archives, out)
}

/// Links as `link` does, with the toolchain given.
pub fn link_with(
    toolchain: &Toolchain,
    objects: &[PathBuf],
    archives: &[PathBuf],
    out: &Path,
) -> Result<(), LinkError> {
    let lib = |name: &str| toolchain.lib.join(name);
    let mut command = Command::new(&toolchain.lld);
    command
        .args(&toolchain.lld_args)
        .args(["-static", "-no-pie", "-nostdlib", "--build-id=none"])
        .args(["-z", "noexecstack", "--gc-sections"])
        .arg("-o")
        .arg(out)
        .args(START.map(lib))
        .args(objects)
        .args(archives)
        .arg("--start-group")
        .args(LIBRARIES.map(lib))
        .arg("--end-group")
        .args(END.map(lib));
    run(command, LINK_LIMIT).map_err(|e| LinkError(format!("cannot link {}: {e}", out.display())))
}

/// Runs a command to its end within `limit`: what it wrote to standard
/// error when it failed.
fn run(mut command: Command, limit: Duration) -> Result<(), String> {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("{}: {e}", command.get_program().to_string_lossy()))?;
    // Read while it runs, so a full pipe cannot stop it.
    let mut stderr = child.stderr.take().expect("piped");
    let reader = std::thread::spawn(move || {
        let mut text = String::new();
        let _ = stderr.read_to_string(&mut text);
        text
    });
    let start = Instant::now();
    let status = loop {
        match child.try_wait().map_err(|e| e.to_string())? {
            Some(status) => break status,
            None if start.elapsed() > limit => {
                let _ = child.kill();
                let _ = child.wait();
                return Err(format!("the linker ran longer than {limit:?}"));
            }
            None => std::thread::sleep(Duration::from_millis(10)),
        }
    };
    let text = reader.join().unwrap_or_default();
    match status.success() {
        true => Ok(()),
        false => Err(format!("{status}\n{text}")),
    }
}
