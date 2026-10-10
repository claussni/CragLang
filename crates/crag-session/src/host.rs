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

//! The host's side: starting images, talking to them and starting a fresh
//! one when one dies (Implementation Plan §11.6.1).
//!
//! The host binds a socket in a directory only its user can enter, starts
//! the image with the socket's path and accepts its connection; the image
//! then says `Hello`. An image that exits before it connects, or does not
//! connect in time, fails the start. A broken stream means the image died
//! or misbehaved: the session reaps it, tells how it ended and starts
//! another of its kind.
//!
//! The host remembers what each image has loaded (§11.6.3): functions by
//! id and the hash of their code, entry stubs by their words, and type
//! descriptors by index. A shipment sends only what the image lacks, so a
//! fresh image after a crash gets everything again.

use std::collections::{HashMap, HashSet};
use std::ffi::OsString;
use std::fmt;
use std::io;
use std::os::unix::fs::DirBuilderExt;
use std::os::unix::net::{UnixListener, UnixStream};
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::{Child, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

use crag_abi::{FuncId, SlotKey, TypeDescriptor};
use crag_runtime::Trap;

use crate::protocol::{
    Message, PROTOCOL_VERSION, ShippedFunction, Stub, read_message, write_message,
};

/// How long an image may take to connect and say `Hello`.
pub const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);

/// How long an image whose stream ended may take to exit before it is
/// killed.
pub const EXIT_GRACE: Duration = Duration::from_secs(1);

/// The command line argument that makes `crag` an image; the kind and the
/// socket's path follow it.
pub const IMAGE_ARG: &str = "__image";

/// What an image is for (Specification §20.1). The app image comes with
/// hot reload.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImageKind {
    Scratch,
}

impl ImageKind {
    pub fn name(self) -> &'static str {
        match self {
            ImageKind::Scratch => "scratch",
        }
    }

    pub fn from_name(name: &str) -> Option<ImageKind> {
        match name {
            "scratch" => Some(ImageKind::Scratch),
            _ => None,
        }
    }
}

/// How to start an image: a program and its first arguments, to which the
/// kind and the socket's path are added.
#[derive(Clone, Debug)]
pub struct ImageCommand {
    pub program: PathBuf,
    pub args: Vec<OsString>,
}

impl ImageCommand {
    /// The running executable as an image: `crag __image`.
    pub fn current() -> io::Result<ImageCommand> {
        Ok(ImageCommand {
            program: std::env::current_exe()?,
            args: vec![IMAGE_ARG.into()],
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImageState {
    Running,
    Exited(ExitStatus),
}

/// A running image process and the stream to it.
pub struct ImageHandle {
    kind: ImageKind,
    pid: u32,
    child: Child,
    stream: UnixStream,
    state: ImageState,
    /// What the image has loaded: functions with the hash of their code,
    /// stubs by their words, and type indices.
    functions: HashMap<FuncId, blake3::Hash>,
    stubs: HashSet<(u32, u32)>,
    types: HashSet<u32>,
}

impl ImageHandle {
    pub fn kind(&self) -> ImageKind {
        self.kind
    }

    pub fn pid(&self) -> u32 {
        self.pid
    }

    pub fn state(&self) -> ImageState {
        self.state
    }

    /// Whether the image has loaded the function.
    pub fn has(&self, func: FuncId) -> bool {
        self.functions.contains_key(&func)
    }

    /// Waits for the image to exit, killing it if it does not within
    /// `grace`, and returns how it ended.
    fn reap(&mut self, grace: Duration) -> io::Result<ExitStatus> {
        if let ImageState::Exited(status) = self.state {
            return Ok(status);
        }
        let deadline = Instant::now() + grace;
        let status = loop {
            if let Some(status) = self.child.try_wait()? {
                break status;
            }
            if Instant::now() >= deadline {
                // It may exit between the test and the kill; either way it
                // ends, and `wait` reports how.
                let _ = self.child.kill();
                break self.child.wait()?;
            }
            std::thread::sleep(Duration::from_millis(2));
        };
        self.state = ImageState::Exited(status);
        Ok(status)
    }
}

impl Drop for ImageHandle {
    /// Asks a running image to shut down, and kills it if it does not.
    fn drop(&mut self) {
        if self.state == ImageState::Running {
            let _ = write_message(&mut self.stream, &Message::Shutdown);
            let _ = self.reap(EXIT_GRACE);
        }
    }
}

/// A directory for one socket, readable only by this user, removed with
/// what it holds when dropped.
struct SocketDir(PathBuf);

impl SocketDir {
    fn new() -> io::Result<SocketDir> {
        static NEXT: AtomicU32 = AtomicU32::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!("crag-{}-{n}", std::process::id()));
        std::fs::DirBuilder::new().mode(0o700).create(&path)?;
        Ok(SocketDir(path))
    }
}

impl Drop for SocketDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Starts an image and waits for its `Hello`.
pub fn spawn_image(command: &ImageCommand, kind: ImageKind) -> io::Result<ImageHandle> {
    let dir = SocketDir::new()?;
    let path = dir.0.join("image.sock");
    let listener = UnixListener::bind(&path)?;
    listener.set_nonblocking(true)?;
    let mut child = Command::new(&command.program)
        .args(&command.args)
        .arg(kind.name())
        .arg(&path)
        .stdin(Stdio::null())
        .spawn()?;
    let pid = child.id();
    match connect(&listener, &mut child) {
        Ok(stream) => Ok(ImageHandle {
            kind,
            pid,
            child,
            stream,
            state: ImageState::Running,
            functions: HashMap::new(),
            stubs: HashSet::new(),
            types: HashSet::new(),
        }),
        Err(e) => {
            let _ = child.kill();
            let _ = child.wait();
            Err(e)
        }
    }
}

/// Accepts the image's connection and checks its `Hello`.
fn connect(listener: &UnixListener, child: &mut Child) -> io::Result<UnixStream> {
    let deadline = Instant::now() + CONNECT_TIMEOUT;
    let mut stream = loop {
        match listener.accept() {
            Ok((stream, _)) => break stream,
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {
                if let Some(status) = child.try_wait()? {
                    return Err(io::Error::other(format!(
                        "the image {} before it connected",
                        describe(status)
                    )));
                }
                if Instant::now() >= deadline {
                    return Err(timed_out());
                }
                std::thread::sleep(Duration::from_millis(2));
            }
            Err(e) => return Err(e),
        }
    };
    stream.set_nonblocking(false)?;
    stream.set_read_timeout(Some(deadline.saturating_duration_since(Instant::now())))?;
    let hello = read_message(&mut stream).map_err(|e| match e.kind() {
        io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut => timed_out(),
        _ => e,
    })?;
    stream.set_read_timeout(None)?;
    match hello {
        Message::Hello { version, .. } if version != PROTOCOL_VERSION => Err(io::Error::other(
            format!("the image speaks protocol version {version}, the host {PROTOCOL_VERSION}"),
        )),
        Message::Hello { pid, .. } if pid != child.id() => Err(io::Error::other(format!(
            "process {pid} connected in place of the image"
        ))),
        Message::Hello { .. } => Ok(stream),
        other => Err(io::Error::other(format!(
            "the image began with {other:?} in place of Hello"
        ))),
    }
}

fn timed_out() -> io::Error {
    io::Error::new(
        io::ErrorKind::TimedOut,
        format!(
            "the image did not connect within {} seconds",
            CONNECT_TIMEOUT.as_secs()
        ),
    )
}

/// Sends a message to the image.
pub fn send(image: &mut ImageHandle, message: &Message) -> io::Result<()> {
    write_message(&mut image.stream, message)
}

/// Receives the image's next message.
pub fn receive(image: &mut ImageHandle) -> io::Result<Message> {
    read_message(&mut image.stream)
}

/// How a process ended, as a phrase: "exited with status 3", "was killed
/// by signal 11 (SIGSEGV)".
pub fn describe(status: ExitStatus) -> String {
    match (status.code(), status.signal()) {
        (Some(0), _) => "exited".into(),
        (Some(code), _) => format!("exited with status {code}"),
        (None, Some(signal)) => match signal_name(signal) {
            Some(name) => format!("was killed by signal {signal} ({name})"),
            None => format!("was killed by signal {signal}"),
        },
        (None, None) => "ended".into(),
    }
}

fn signal_name(signal: i32) -> Option<&'static str> {
    Some(match signal {
        1 => "SIGHUP",
        2 => "SIGINT",
        3 => "SIGQUIT",
        4 => "SIGILL",
        5 => "SIGTRAP",
        6 => "SIGABRT",
        7 => "SIGBUS",
        8 => "SIGFPE",
        9 => "SIGKILL",
        11 => "SIGSEGV",
        13 => "SIGPIPE",
        15 => "SIGTERM",
        _ => return None,
    })
}

/// An image that ended, as the session reports it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImageExit {
    pub kind: ImageKind,
    pub pid: u32,
    pub status: ExitStatus,
}

impl fmt::Display for ImageExit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the {} image (process {}) {}",
            self.kind.name(),
            self.pid,
            describe(self.status)
        )
    }
}

#[derive(Debug)]
pub enum SessionError {
    /// The image died; a fresh one runs in its place.
    Exited(ImageExit),
    /// The image died or misbehaved, and no fresh one could be started.
    Io(io::Error),
    /// The image could not do what it was asked, and why; it runs on.
    Refused(String),
}

impl fmt::Display for SessionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SessionError::Exited(exit) => write!(f, "{exit}; a fresh one has started"),
            SessionError::Io(e) => write!(f, "the image cannot be started: {e}"),
            SessionError::Refused(why) => write!(f, "the image refused: {why}"),
        }
    }
}

impl std::error::Error for SessionError {}

impl From<io::Error> for SessionError {
    fn from(e: io::Error) -> SessionError {
        SessionError::Io(e)
    }
}

/// The images of a session and how to start them. M3 has the scratch
/// image, which evaluates REPL input.
pub struct Session {
    command: ImageCommand,
    scratch: ImageHandle,
}

impl Session {
    pub fn start(command: ImageCommand) -> io::Result<Session> {
        let scratch = spawn_image(&command, ImageKind::Scratch)?;
        Ok(Session { command, scratch })
    }

    pub fn scratch(&self) -> &ImageHandle {
        &self.scratch
    }

    /// Sends a message to the scratch image and returns its reply. If the
    /// image dies on the way, or breaks the protocol, it is reaped and
    /// replaced, and the error tells how it ended.
    pub fn request(&mut self, message: &Message) -> Result<Message, SessionError> {
        if self.scratch.state != ImageState::Running {
            // A restart failed before; try again.
            self.scratch = spawn_image(&self.command, ImageKind::Scratch)?;
        }
        let image = &mut self.scratch;
        let error = match send(image, message).and_then(|()| receive(image)) {
            Ok(reply) => return Ok(reply),
            Err(e) => e,
        };
        // A stream that ended belongs to an image that is exiting; any
        // other failure to one that must be stopped.
        let grace = match error.kind() {
            io::ErrorKind::UnexpectedEof
            | io::ErrorKind::BrokenPipe
            | io::ErrorKind::ConnectionReset => EXIT_GRACE,
            _ => Duration::ZERO,
        };
        let status = self.scratch.reap(grace)?;
        Err(SessionError::Exited(self.on_image_exit(status)?))
    }

    /// Ships code to the scratch image: the functions, stubs and type
    /// descriptors it lacks, loaded together, and then empties the cells
    /// of the values in `reset`. Returns how many functions were sent. A
    /// function that comes again with the code it has is not sent; one that
    /// comes with other code is, and replaces the old code in the image.
    pub fn ship(
        &mut self,
        types: &[(u32, TypeDescriptor)],
        stubs: &[Stub],
        functions: &[ShippedFunction],
        reset: &[SlotKey],
    ) -> Result<usize, SessionError> {
        let image = &self.scratch;
        let mut hashes = HashMap::new();
        let mut new_functions = Vec::new();
        for f in functions {
            let hash = blake3::hash(&f.encode());
            let known = image.functions.get(&f.id).or(hashes.get(&f.id));
            if known == Some(&hash) {
                continue;
            }
            // New, or changed: the image replaces the code it has. A
            // function that comes twice with different code is sent twice,
            // and the image refuses the shipment.
            hashes.insert(f.id, hash);
            new_functions.push(f.clone());
        }
        let mut shapes = HashSet::new();
        let new_stubs: Vec<Stub> = stubs
            .iter()
            .filter(|s| {
                let shape = (s.params, s.returns);
                !image.stubs.contains(&shape) && shapes.insert(shape)
            })
            .cloned()
            .collect();
        let mut indices = HashSet::new();
        let new_types: Vec<(u32, TypeDescriptor)> = types
            .iter()
            .filter(|(index, _)| !image.types.contains(index) && indices.insert(*index))
            .cloned()
            .collect();
        let sent = new_functions.len();
        if sent == 0 && new_stubs.is_empty() && new_types.is_empty() && reset.is_empty() {
            return Ok(0);
        }
        let load = Message::Load {
            types: new_types,
            stubs: new_stubs,
            functions: new_functions,
            reset: reset.to_vec(),
        };
        match self.request(&load)? {
            Message::Loaded => {
                let image = &mut self.scratch;
                image.functions.extend(hashes);
                image.stubs.extend(shapes);
                image.types.extend(indices);
                Ok(sent)
            }
            Message::Failed(why) => Err(SessionError::Refused(why)),
            other => Err(SessionError::Refused(format!(
                "the image answered {other:?} to Load"
            ))),
        }
    }

    /// Runs a loaded function without parameters in the scratch image.
    pub fn run(&mut self, func: FuncId) -> Result<RunResult, SessionError> {
        match self.request(&Message::Run(func))? {
            Message::Finished(words) => Ok(RunResult::Finished(words)),
            Message::Trapped {
                kind,
                position,
                stack,
            } => Ok(RunResult::Trapped(Trap {
                kind,
                position,
                stack,
            })),
            Message::Failed(why) => Err(SessionError::Refused(why)),
            other => Err(SessionError::Refused(format!(
                "the image answered {other:?} to Run"
            ))),
        }
    }

    /// Kills the scratch image, for one that runs away, and starts a fresh
    /// one; how the old one ended.
    pub fn restart(&mut self) -> Result<ImageExit, SessionError> {
        let status = self.scratch.reap(Duration::ZERO)?;
        Ok(self.on_image_exit(status)?)
    }

    /// Reports how the scratch image ended and starts a fresh one.
    fn on_image_exit(&mut self, status: ExitStatus) -> io::Result<ImageExit> {
        let exit = ImageExit {
            kind: self.scratch.kind,
            pid: self.scratch.pid,
            status,
        };
        self.scratch = spawn_image(&self.command, exit.kind)?;
        Ok(exit)
    }
}

/// How a run in an image ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult {
    /// The result words. Words that are references point into the image.
    Finished(Vec<u64>),
    Trapped(Trap),
}
