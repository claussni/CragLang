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

//! The host's side against images that misbehave. The images are this
//! test binary run again: `fake_image` connects and does what its `fake:`
//! argument says.

use std::io::Write;
use std::os::unix::net::UnixStream;
use std::time::{Duration, Instant};

use crag_session::{
    ImageCommand, ImageKind, Message, PROTOCOL_VERSION, Session, SessionError, describe,
    read_message, spawn_image, write_message,
};

fn fake(behaviour: &str) -> ImageCommand {
    ImageCommand {
        program: std::env::current_exe().unwrap(),
        args: [
            "fake_image",
            "--exact",
            "--ignored",
            "--quiet",
            &format!("fake:{behaviour}"),
        ]
        .iter()
        .map(Into::into)
        .collect(),
    }
}

#[test]
#[ignore = "an image for the other tests, which start it"]
fn fake_image() {
    let args: Vec<String> = std::env::args().collect();
    let Some(behaviour) = args.iter().find_map(|a| a.strip_prefix("fake:")) else {
        return;
    };
    let mut stream = UnixStream::connect(args.last().unwrap()).unwrap();
    let pid = std::process::id();
    let hello = Message::Hello {
        version: PROTOCOL_VERSION,
        pid,
    };
    match behaviour {
        "old" => {
            let hello = Message::Hello {
                version: PROTOCOL_VERSION + 1,
                pid,
            };
            write_message(&mut stream, &hello).unwrap();
        }
        "rude" => write_message(&mut stream, &Message::Pong(0)).unwrap(),
        "imposter" => {
            let hello = Message::Hello {
                version: PROTOCOL_VERSION,
                pid: pid + 1,
            };
            write_message(&mut stream, &hello).unwrap();
        }
        // Answers its first message with garbage and then hangs, so only
        // a kill ends it.
        "garbage" => {
            write_message(&mut stream, &hello).unwrap();
            read_message(&mut stream).unwrap();
            stream.write_all(&[1, 0, 0, 0, 99]).unwrap();
            loop {
                std::thread::sleep(Duration::from_secs(60));
            }
        }
        // Answers one ping, then exits.
        "once" => {
            write_message(&mut stream, &hello).unwrap();
            if let Message::Ping(n) = read_message(&mut stream).unwrap() {
                write_message(&mut stream, &Message::Pong(n)).unwrap();
            }
            std::process::exit(3);
        }
        _ => panic!("no fake image behaves `{behaviour}`"),
    }
    // Waits for the host to hang up.
    let _ = read_message(&mut stream);
}

fn start_error(command: &ImageCommand) -> String {
    match spawn_image(command, ImageKind::Scratch) {
        Ok(_) => panic!("the image started"),
        Err(e) => e.to_string(),
    }
}

#[test]
fn an_image_that_exits_at_once_fails_the_start() {
    let command = ImageCommand {
        program: "/bin/sh".into(),
        args: vec!["-c".into(), "exit 3".into(), "sh".into()],
    };
    let start = Instant::now();
    assert_eq!(
        start_error(&command),
        "the image exited with status 3 before it connected"
    );
    assert!(start.elapsed() < Duration::from_secs(5));
}

#[test]
fn an_image_must_say_hello_in_the_host_s_version() {
    assert_eq!(
        start_error(&fake("old")),
        format!(
            "the image speaks protocol version {}, the host {PROTOCOL_VERSION}",
            PROTOCOL_VERSION + 1
        )
    );
    assert_eq!(
        start_error(&fake("rude")),
        "the image began with Pong(0) in place of Hello"
    );
    assert!(start_error(&fake("imposter")).ends_with("connected in place of the image"));
}

#[test]
fn an_image_that_breaks_the_protocol_is_killed_at_once() {
    let mut session = Session::start(fake("garbage")).unwrap();
    let old = session.scratch().pid();
    let start = Instant::now();
    let Err(SessionError::Exited(exit)) = session.request(&Message::Ping(1)) else {
        panic!("garbage was a reply");
    };
    assert_eq!(exit.pid, old);
    assert_eq!(describe(exit.status), "was killed by signal 9 (SIGKILL)");
    assert!(start.elapsed() < Duration::from_secs(1));
    assert_ne!(session.scratch().pid(), old);
}

#[test]
fn an_image_that_exits_is_replaced() {
    let mut session = Session::start(fake("once")).unwrap();
    let old = session.scratch().pid();
    assert_eq!(
        session.request(&Message::Ping(5)).unwrap(),
        Message::Pong(5)
    );
    let Err(SessionError::Exited(exit)) = session.request(&Message::Ping(6)) else {
        panic!("the image answered twice");
    };
    assert_eq!(exit.pid, old);
    assert_eq!(describe(exit.status), "exited with status 3");
    assert_eq!(
        session.request(&Message::Ping(7)).unwrap(),
        Message::Pong(7)
    );
}
