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
use std::process::{Child, ChildStdout, Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU32, Ordering};
use std::time::{Duration, Instant};

use crag_abi::{FuncId, Shapes, SlotKey, TypeDescriptor};
use crag_runtime::Trap;

use crate::protocol::{
    Fill, Message, PROTOCOL_VERSION, PausedTask, ShippedFunction, Stub, read_message, write_message,
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
    App,
}

impl ImageKind {
    pub fn name(self) -> &'static str {
        match self {
            ImageKind::Scratch => "scratch",
            ImageKind::App => "app",
        }
    }

    pub fn from_name(name: &str) -> Option<ImageKind> {
        match name {
            "scratch" => Some(ImageKind::Scratch),
            "app" => Some(ImageKind::App),
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
    /// The image's standard output, while it is open, and what it printed
    /// that was not taken yet.
    stdout: Option<ChildStdout>,
    printed: Vec<u8>,
    /// What the image has loaded: functions with the hash of their code,
    /// stubs by their words, and type descriptors by index.
    functions: HashMap<FuncId, blake3::Hash>,
    stubs: HashSet<(u32, u32)>,
    descriptors: HashMap<u32, blake3::Hash>,
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

    /// What the image printed since the last call.
    pub fn take_output(&mut self) -> Vec<u8> {
        self.drain();
        std::mem::take(&mut self.printed)
    }

    /// Keeps what the image printed and the pipe holds, without waiting.
    fn drain(&mut self) {
        use std::io::Read;
        let Some(stdout) = &mut self.stdout else {
            return;
        };
        let mut buf = [0; 8192];
        loop {
            match stdout.read(&mut buf) {
                Ok(0) => {
                    self.stdout = None;
                    return;
                }
                Ok(n) => self.printed.extend_from_slice(&buf[..n]),
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) if e.kind() == io::ErrorKind::WouldBlock => return,
                Err(_) => {
                    self.stdout = None;
                    return;
                }
            }
        }
    }

    /// Waits until the stream has something to read, keeping what the
    /// image prints meanwhile, so an image that prints much never waits on
    /// a full pipe while the host waits on it.
    fn wait_for_message(&mut self) -> io::Result<()> {
        use std::os::fd::AsRawFd;
        loop {
            self.drain();
            let mut fds = [
                libc::pollfd {
                    fd: self.stream.as_raw_fd(),
                    events: libc::POLLIN,
                    revents: 0,
                },
                libc::pollfd {
                    fd: self.stdout.as_ref().map_or(-1, |s| s.as_raw_fd()),
                    events: libc::POLLIN,
                    revents: 0,
                },
            ];
            // SAFETY: the array outlives the call, and a negative
            // descriptor is skipped.
            let ready = unsafe { libc::poll(fds.as_mut_ptr(), 2, -1) };
            if ready < 0 {
                let e = io::Error::last_os_error();
                if e.kind() == io::ErrorKind::Interrupted {
                    continue;
                }
                return Err(e);
            }
            if fds[0].revents != 0 {
                return Ok(());
            }
        }
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
        .stdout(Stdio::piped())
        .spawn()?;
    let pid = child.id();
    let stdout = child.stdout.take();
    if let Some(stdout) = &stdout {
        use std::os::fd::AsRawFd;
        // SAFETY: plain system calls on the pipe's descriptor.
        unsafe {
            let fd = stdout.as_raw_fd();
            let flags = libc::fcntl(fd, libc::F_GETFL);
            libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK);
        }
    }
    match connect(&listener, &mut child) {
        Ok(stream) => Ok(ImageHandle {
            kind,
            pid,
            child,
            stream,
            state: ImageState::Running,
            stdout,
            printed: Vec::new(),
            functions: HashMap::new(),
            stubs: HashSet::new(),
            descriptors: HashMap::new(),
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

/// Receives the image's next message. What the image printed before it
/// sent the message is kept by then, for `take_output`.
pub fn receive(image: &mut ImageHandle) -> io::Result<Message> {
    image.wait_for_message()?;
    let message = read_message(&mut image.stream);
    image.drain();
    message
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
    /// The app image died, and with it the app; it is not restarted.
    AppExited(ImageExit),
    /// There is no app image to ask.
    NoApp,
    /// The image died or misbehaved, and no fresh one could be started.
    Io(io::Error),
    /// The image could not do what it was asked, and why; it runs on.
    Refused(String),
}

impl fmt::Display for SessionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SessionError::Exited(exit) => write!(f, "{exit}; a fresh one has started"),
            SessionError::AppExited(exit) => write!(f, "{exit}"),
            SessionError::NoApp => write!(f, "no app runs"),
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

/// The images of a session and how to start them: the scratch image,
/// which evaluates REPL input and is restarted when it dies, and the app
/// image while the app runs (Specification §20.1).
pub struct Session {
    command: ImageCommand,
    scratch: ImageHandle,
    app: Option<ImageHandle>,
    /// What images that are gone printed and was not taken yet.
    printed: Vec<u8>,
}

/// How long the app image may take to shut down before it is killed.
const APP_EXIT_GRACE: Duration = Duration::from_secs(2);

impl Session {
    pub fn start(command: ImageCommand) -> io::Result<Session> {
        let scratch = spawn_image(&command, ImageKind::Scratch)?;
        Ok(Session {
            command,
            scratch,
            app: None,
            printed: Vec::new(),
        })
    }

    pub fn scratch(&self) -> &ImageHandle {
        &self.scratch
    }

    /// How the session starts its images.
    pub fn command(&self) -> &ImageCommand {
        &self.command
    }

    /// The app image, while there is one.
    pub fn app(&self) -> Option<&ImageHandle> {
        self.app.as_ref()
    }

    /// What the images printed since the last call: the scratch image's,
    /// then the app's.
    pub fn take_output(&mut self) -> Vec<u8> {
        let mut out = std::mem::take(&mut self.printed);
        out.extend(self.scratch.take_output());
        if let Some(app) = &mut self.app {
            out.extend(app.take_output());
        }
        out
    }

    /// Keeps what an image that is going away printed.
    fn keep_output(&mut self, kind: ImageKind) {
        let out = match kind {
            ImageKind::Scratch => self.scratch.take_output(),
            ImageKind::App => self
                .app
                .as_mut()
                .map(ImageHandle::take_output)
                .unwrap_or_default(),
        };
        self.printed.extend(out);
    }

    /// Starts an app image, which code is then shipped to and started in;
    /// one that runs already is shut down first.
    pub fn start_app_image(&mut self) -> io::Result<()> {
        self.keep_output(ImageKind::App);
        self.app = None;
        self.app = Some(spawn_image(&self.command, ImageKind::App)?);
        Ok(())
    }

    /// Sends a message to the scratch image and returns its reply. If the
    /// image dies on the way, or breaks the protocol, it is reaped and
    /// replaced, and the error tells how it ended.
    pub fn request(&mut self, message: &Message) -> Result<Message, SessionError> {
        self.request_to(ImageKind::Scratch, message)
    }

    /// Sends a message to an image and returns its reply. A scratch image
    /// that dies is replaced; an app image that dies is gone, with the app.
    pub fn request_to(
        &mut self,
        kind: ImageKind,
        message: &Message,
    ) -> Result<Message, SessionError> {
        if kind == ImageKind::Scratch && self.scratch.state != ImageState::Running {
            // A restart failed before; try again.
            self.keep_output(ImageKind::Scratch);
            self.scratch = spawn_image(&self.command, ImageKind::Scratch)?;
        }
        let image = match kind {
            ImageKind::Scratch => &mut self.scratch,
            ImageKind::App => self.app.as_mut().ok_or(SessionError::NoApp)?,
        };
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
        let status = image.reap(grace)?;
        match kind {
            ImageKind::Scratch => Err(SessionError::Exited(self.on_image_exit(status)?)),
            ImageKind::App => {
                self.keep_output(ImageKind::App);
                let app = self.app.take().expect("an app image");
                Err(SessionError::AppExited(ImageExit {
                    kind,
                    pid: app.pid,
                    status,
                }))
            }
        }
    }

    /// Ships code to the scratch image: the functions, stubs and type
    /// descriptors it lacks, loaded together, and then empties the cells
    /// of the values in `reset` and fills those in `fills`. Returns how many
    /// functions were sent. A
    /// function that comes again with the code it has is not sent; one that
    /// comes with other code is, and replaces the old code in the image.
    pub fn ship(
        &mut self,
        types: &[(u32, TypeDescriptor)],
        stubs: &[Stub],
        functions: &[ShippedFunction],
        reset: &[SlotKey],
        fills: &[Fill],
    ) -> Result<usize, SessionError> {
        self.ship_to(ImageKind::Scratch, types, stubs, functions, reset, fills)
    }

    /// The functions among `functions` that an image lacks, or has with
    /// other code: what `ship_to` would send.
    pub fn changed(&self, kind: ImageKind, functions: &[ShippedFunction]) -> Vec<FuncId> {
        let Some(image) = self.image(kind) else {
            return functions.iter().map(|f| f.id).collect();
        };
        functions
            .iter()
            .filter(|f| image.functions.get(&f.id) != Some(&blake3::hash(&f.encode())))
            .map(|f| f.id)
            .collect()
    }

    /// The type descriptors an image holds, by index.
    pub fn descriptors(&self, kind: ImageKind) -> Option<&HashMap<u32, blake3::Hash>> {
        self.image(kind).map(|i| &i.descriptors)
    }

    fn image(&self, kind: ImageKind) -> Option<&ImageHandle> {
        match kind {
            ImageKind::Scratch => Some(&self.scratch),
            ImageKind::App => self.app.as_ref(),
        }
    }

    /// Ships code to an image, as `ship` does to the scratch image.
    pub fn ship_to(
        &mut self,
        kind: ImageKind,
        types: &[(u32, TypeDescriptor)],
        stubs: &[Stub],
        functions: &[ShippedFunction],
        reset: &[SlotKey],
        fills: &[Fill],
    ) -> Result<usize, SessionError> {
        let image = self.image(kind).ok_or(SessionError::NoApp)?;
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
        let mut indices = HashMap::new();
        let new_types: Vec<(u32, TypeDescriptor)> = types
            .iter()
            .filter(|(index, d)| {
                !image.descriptors.contains_key(index)
                    && indices.insert(*index, descriptor_hash(d)).is_none()
            })
            .cloned()
            .collect();
        let sent = new_functions.len();
        if sent == 0
            && new_stubs.is_empty()
            && new_types.is_empty()
            && reset.is_empty()
            && fills.is_empty()
        {
            return Ok(0);
        }
        let load = Message::Load {
            types: new_types,
            stubs: new_stubs,
            functions: new_functions,
            reset: reset.to_vec(),
            fills: fills.to_vec(),
        };
        match self.request_to(kind, &load)? {
            Message::Loaded => {
                let image = match kind {
                    ImageKind::Scratch => &mut self.scratch,
                    ImageKind::App => self.app.as_mut().expect("answered"),
                };
                image.functions.extend(hashes);
                image.stubs.extend(shapes);
                image.descriptors.extend(indices);
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
            Message::Interrupted => Ok(RunResult::Interrupted),
            Message::Trapped {
                kind,
                position,
                stack,
                detail,
            } => Ok(RunResult::Trapped(Trap {
                kind,
                position,
                stack,
                detail,
            })),
            Message::Failed(why) => Err(SessionError::Refused(why)),
            other => Err(SessionError::Refused(format!(
                "the image answered {other:?} to Run"
            ))),
        }
    }

    /// Starts a loaded function as the app in the app image.
    pub fn start_app(&mut self, func: FuncId) -> Result<(), SessionError> {
        match self.request_to(ImageKind::App, &Message::Start(func))? {
            Message::Started => Ok(()),
            Message::Failed(why) => Err(SessionError::Refused(why)),
            other => Err(SessionError::Refused(format!(
                "the image answered {other:?} to Start"
            ))),
        }
    }

    /// How the app is doing: running, or how it ended.
    pub fn app_status(&mut self) -> Result<AppStatus, SessionError> {
        Ok(match self.request_to(ImageKind::App, &Message::Status)? {
            Message::Running => AppStatus::Running,
            Message::Stopped => AppStatus::Stopped,
            Message::Finished(words) => AppStatus::Ended(RunResult::Finished(words)),
            Message::Trapped {
                kind,
                position,
                stack,
                detail,
            } => AppStatus::Ended(RunResult::Trapped(Trap {
                kind,
                position,
                stack,
                detail,
            })),
            Message::Failed(why) => return Err(SessionError::Refused(why)),
            other => {
                return Err(SessionError::Refused(format!(
                    "the image answered {other:?} to Status"
                )));
            }
        })
    }

    /// Sets the app's breakpoints: steps by function and index.
    pub fn set_breaks(&mut self, breaks: Vec<(FuncId, u32)>) -> Result<(), SessionError> {
        self.done(Message::Breaks(breaks))
    }

    /// The app's tasks stopped at steps.
    pub fn pauses(&mut self) -> Result<Vec<PausedTask>, SessionError> {
        match self.request_to(ImageKind::App, &Message::Pauses)? {
            Message::Paused(tasks) => Ok(tasks),
            other => Err(unexpected(other, "Pauses")),
        }
    }

    /// Resumes a stopped task of the app: continuing (0), or stepping into
    /// (1), over (2) or out (3).
    pub fn resume(&mut self, task: u64, how: u8) -> Result<(), SessionError> {
        self.done(Message::Resume { task, how })
    }

    /// The values of a stopped task's locals, as text.
    pub fn locals(
        &mut self,
        task: u64,
        locals: Vec<(Shapes, u32)>,
    ) -> Result<Vec<String>, SessionError> {
        match self.request_to(ImageKind::App, &Message::Locals { task, locals })? {
            Message::Texts(texts) => Ok(texts),
            other => Err(unexpected(other, "Locals")),
        }
    }

    fn done(&mut self, message: Message) -> Result<(), SessionError> {
        match self.request_to(ImageKind::App, &message)? {
            Message::Done => Ok(()),
            other => Err(unexpected(other, "a debugger request")),
        }
    }

    /// Stops the app and ends its image, killing it if the app does not
    /// stop in time.
    pub fn stop_app(&mut self) -> Result<(), SessionError> {
        if self.app.is_none() {
            return Ok(());
        }
        let stopped = matches!(
            self.request_to(ImageKind::App, &Message::Stop),
            Ok(Message::Stopped)
        );
        self.keep_output(ImageKind::App);
        if let Some(mut app) = self.app.take() {
            if stopped {
                let _ = send(&mut app, &Message::Shutdown);
                let _ = app.reap(APP_EXIT_GRACE);
            } else {
                let _ = app.reap(Duration::ZERO);
            }
        }
        Ok(())
    }

    /// Runs a loaded function as `run` does, and has the image show its
    /// result, of the shape `root` of `shapes`, and release it; with
    /// `text`, a `Str` as it is.
    pub fn show(
        &mut self,
        func: FuncId,
        shapes: &Shapes,
        root: u32,
        text: bool,
    ) -> Result<RunResult, SessionError> {
        let show = Message::Show {
            func,
            shapes: shapes.clone(),
            root,
            text,
        };
        match self.request(&show)? {
            Message::Shown(text) => Ok(RunResult::Shown(text)),
            Message::Trapped {
                kind,
                position,
                stack,
                detail,
            } => Ok(RunResult::Trapped(Trap {
                kind,
                position,
                stack,
                detail,
            })),
            Message::Interrupted => Ok(RunResult::Interrupted),
            Message::Failed(why) => Err(SessionError::Refused(why)),
            other => Err(SessionError::Refused(format!(
                "the image answered {other:?} to Show"
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
        self.keep_output(ImageKind::Scratch);
        self.scratch = spawn_image(&self.command, exit.kind)?;
        Ok(exit)
    }
}

/// The error for an answer that does not fit the request.
fn unexpected(answer: Message, request: &str) -> SessionError {
    match answer {
        Message::Failed(why) => SessionError::Refused(why),
        other => SessionError::Refused(format!("the image answered {other:?} to {request}")),
    }
}

/// A hash of a type descriptor, to tell whether an image holds the same.
pub fn descriptor_hash(descriptor: &TypeDescriptor) -> blake3::Hash {
    blake3::hash(format!("{descriptor:?}").as_bytes())
}

/// How the app is doing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AppStatus {
    Running,
    /// It ended, as the result tells; this is said once.
    Ended(RunResult),
    /// It was stopped, or its end was told already.
    Stopped,
}

/// How a run in an image ended.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RunResult {
    /// The result words. Words that are references point into the image.
    Finished(Vec<u64>),
    Trapped(Trap),
    /// SIGINT stopped it.
    Interrupted,
    /// The result as the image shows it.
    Shown(String),
}
