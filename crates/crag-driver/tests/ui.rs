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

//! The built-in editor (Specification §20.8), driven by its commands and
//! drawn on a test terminal.

use std::fs;
use std::path::PathBuf;

use crag_driver::ui::buffer::Cursor;
use crag_driver::ui::keys::Command;
use crag_driver::ui::state::{Focus, Overlay};
use crag_driver::ui::{Colours, Theme, Ui, draw};
use crag_driver::{Project, Repl, Scratch};
use crag_session::ImageCommand;
use ratatui::Terminal;
use ratatui::backend::TestBackend;

const SHAPE: &str = "pub type Point(x: Int, y: Int)\n\n// The area of the rectangle.\npub fn area(p: Point) -> Int { p.x * p.y }\n";

const APP: &str =
    "import demo.geo.shape\n\nfn main() -> Int {\n  let p = Point(x: 2, y: 3)\n  area(p)\n}\n";

fn project(name: &str) -> PathBuf {
    let root = std::env::temp_dir().join(format!("crag-ui-{name}-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("geo")).unwrap();
    fs::write(
        root.join("package.crag"),
        "package demo 0.1\nruntime 0.0\nmain demo.app\n",
    )
    .unwrap();
    fs::write(root.join("geo/shape.crag"), SHAPE).unwrap();
    fs::write(root.join("app.crag"), APP).unwrap();
    root
}

fn ui(root: &std::path::Path) -> Ui {
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    Ui::new(Repl::new(Project::load(root).unwrap(), scratch))
}

/// The screen as text, one string per row.
fn screen(ui: &mut Ui, width: u16, height: u16) -> Vec<String> {
    let mut terminal = Terminal::new(TestBackend::new(width, height)).unwrap();
    let theme = Theme::new(Colours::None);
    terminal.draw(|frame| draw(frame, ui, &theme)).unwrap();
    let buffer = terminal.backend().buffer().clone();
    (0..height)
        .map(|y| {
            (0..width)
                .map(|x| buffer[(x, y)].symbol().to_string())
                .collect()
        })
        .collect()
}

fn shows(screen: &[String], text: &str) -> bool {
    screen.iter().any(|row| row.contains(text))
}

fn typing(ui: &mut Ui, text: &str) {
    for c in text.chars() {
        ui.command(Command::Char(c));
    }
}

#[test]
fn the_layout_shows_editor_repl_panels_and_status() {
    let root = project("layout");
    let mut ui = ui(&root);
    let s = screen(&mut ui, 120, 40);
    for text in [
        " Buffers ",
        " Files ",
        " app.crag ",
        " REPL ",
        "scratch> ",
        " Problems ",
        "fn main() -> Int {",
    ] {
        assert!(shows(&s, text), "{text} missing:\n{}", s.join("\n"));
    }
    assert!(
        shows(&s, " demo │ app.crag │ Editor │ Edit"),
        "{}",
        s.join("\n")
    );
    assert!(shows(&s, "▾ demo"), "{}", s.join("\n"));
    assert!(shows(&s, "app.crag"));
    // Narrow: the side panels make room, until they have the focus.
    let s = screen(&mut ui, 80, 30);
    assert!(!shows(&s, " Buffers "));
    ui.command(Command::FocusLeft);
    let s = screen(&mut ui, 80, 30);
    assert!(shows(&s, " Buffers "));
    // Short: the editor and the REPL take turns.
    ui.command(Command::FocusRepl);
    let s = screen(&mut ui, 120, 15);
    assert!(
        shows(&s, "┌ REPL ") && !shows(&s, "┌ app.crag "),
        "{}",
        s.join("\n")
    );
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn editing_undo_and_saving() {
    let root = project("edit");
    let mut ui = ui(&root);
    ui.command(Command::Down { select: false });
    ui.command(Command::Down { select: false });
    ui.command(Command::End { select: false });
    ui.command(Command::Enter);
    typing(&mut ui, "let q = 1");
    assert_eq!(ui.buffer().line_text(3), "  let q = 1");
    let s = screen(&mut ui, 120, 40);
    assert!(
        shows(&s, "│● app ") && shows(&s, "┌ app.crag ● "),
        "{}",
        s.join("\n")
    );
    ui.command(Command::Undo);
    assert_eq!(ui.buffer().line_text(3), "  ");
    ui.command(Command::Undo);
    assert_eq!(ui.buffer().text(), APP);
    ui.command(Command::Redo);
    ui.command(Command::Redo);
    ui.command(Command::Save);
    assert_eq!(
        fs::read_to_string(root.join("app.crag"))
            .unwrap()
            .lines()
            .nth(3),
        Some("  let q = 1")
    );
    assert!(!ui.buffer().dirty());
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn problems_appear_as_one_types_and_lead_to_their_place() {
    let root = project("problems");
    let mut ui = ui(&root);
    assert!(ui.problems.is_empty());
    // `area(p)` becomes `area(q)`.
    for _ in 0..4 {
        ui.command(Command::Down { select: false });
    }
    ui.command(Command::End { select: false });
    ui.command(Command::Left {
        select: false,
        word: false,
    });
    ui.command(Command::Backspace { word: false });
    typing(&mut ui, "q");
    ui.push();
    assert_eq!(ui.problems.len(), 1, "{:?}", ui.problems);
    assert!(ui.problems[0].message.contains('q'));
    let s = screen(&mut ui, 120, 40);
    assert!(shows(&s, "! 5 │   area(q)"), "{}", s.join("\n"));
    assert!(shows(&s, "! app.crag:5"));
    ui.command(Command::Home { select: false });
    ui.command(Command::NextProblem);
    assert_eq!(ui.buffer().line_col(ui.buffer().cursor.pos), (4, 7));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn code_commands_go_to_definitions_references_and_information() {
    let root = project("code");
    let mut ui = ui(&root);
    // On `area` of `area(p)`.
    for _ in 0..4 {
        ui.command(Command::Down { select: false });
    }
    ui.command(Command::Home { select: false });
    ui.command(Command::Right {
        select: false,
        word: false,
    });
    ui.command(Command::Info);
    match &ui.overlay {
        Some(Overlay::Info(text)) => {
            assert!(text.contains("pub fn area(p: Point) -> Int"), "{text}")
        }
        other => panic!("{other:?}"),
    }
    ui.command(Command::Escape);
    ui.command(Command::Definition);
    assert_eq!(ui.buffer().name, "geo/shape.crag");
    assert_eq!(ui.buffer().line_col(ui.buffer().cursor.pos), (3, 7));
    // Back where it came from.
    ui.command(Command::Back);
    assert_eq!(ui.buffer().name, "app.crag");
    ui.command(Command::Forward);
    assert_eq!(ui.buffer().name, "geo/shape.crag");
    ui.command(Command::References);
    match &ui.overlay {
        Some(Overlay::Pick(picker)) => {
            let labels: Vec<&str> = picker.items.iter().map(|i| i.label.as_str()).collect();
            assert!(labels.contains(&"app.crag:5:3"), "{labels:?}");
            assert!(labels.contains(&"geo/shape.crag:4:8"), "{labels:?}");
        }
        other => panic!("{other:?}"),
    }
    ui.command(Command::Escape);
    // Completion after `p.` in the app.
    ui.command(Command::QuickSwitch);
    typing(&mut ui, "app");
    ui.command(Command::Enter);
    assert_eq!(ui.buffer().name, "app.crag");
    // At the end of `let p = …`, a new line.
    let end = APP.find("y: 3)").unwrap() + 5;
    ui.buffer_mut().cursor = Cursor::at(end);
    ui.command(Command::Enter);
    typing(&mut ui, "p.");
    ui.command(Command::Complete);
    match &ui.overlay {
        Some(Overlay::Completion { items, .. }) => {
            let labels: Vec<&str> = items.iter().map(|c| c.label.as_str()).collect();
            assert!(
                labels.contains(&"x") && labels.contains(&"area"),
                "{labels:?}"
            );
        }
        other => panic!("{other:?}"),
    }
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_repl_runs_input_and_ctrl_e_shows_results_inline() {
    let root = project("repl");
    let mut ui = ui(&root);
    ui.command(Command::FocusRepl);
    assert_eq!(ui.focus, Focus::Repl);
    // The session imports as a module does.
    typing(&mut ui, "import demo.geo.shape");
    ui.command(Command::Enter);
    typing(&mut ui, "area(Point(x: 4, y: 5))");
    ui.command(Command::Enter);
    let s = screen(&mut ui, 120, 40);
    assert!(
        shows(&s, "scratch> area(Point(x: 4, y: 5))"),
        "{}",
        s.join("\n")
    );
    assert!(shows(&s, "│20 : Int "), "{}", s.join("\n"));
    // An incomplete input goes on on the next line.
    typing(&mut ui, "if 1 < 2 {");
    ui.command(Command::Enter);
    assert_eq!(ui.input.text(), "if 1 < 2 {\n");
    ui.command(Command::Escape);
    // Ctrl+E on a line of the editor: `let p = Point(…)` shows its value,
    // in the scope of its file.
    ui.buffer_mut().cursor = Cursor::at(APP.find("let p").unwrap());
    ui.command(Command::Evaluate);
    let s = screen(&mut ui, 120, 40);
    assert!(shows(&s, "⇒ Point(x: 2, y: 3)"), "{}", s.join("\n"));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn quitting_with_unsaved_changes_asks_first() {
    let root = project("quit");
    let mut ui = ui(&root);
    typing(&mut ui, "x");
    ui.command(Command::Quit);
    assert!(!ui.quit);
    let s = screen(&mut ui, 120, 40);
    assert!(
        shows(
            &s,
            "1 buffer has unsaved changes, which are lost. Quit? [y|N]"
        ),
        "{}",
        s.join("\n")
    );
    // Enter means no.
    ui.command(Command::Enter);
    assert!(!ui.quit);
    ui.command(Command::Quit);
    ui.command(Command::Char('y'));
    assert!(ui.quit);
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_hint_line_and_the_palette_tell_the_keys() {
    let root = project("hints");
    let mut ui = ui(&root);
    let s = screen(&mut ui, 160, 40);
    let last = s.last().unwrap();
    for text in [
        "Ctrl+S Save",
        "F12 Definition",
        "Ctrl+K Commands",
        "Ctrl+Q Quit",
    ] {
        assert!(last.contains(text), "{text} missing:\n{}", s.join("\n"));
    }
    // The hints follow the focus.
    ui.command(Command::FocusRepl);
    let s = screen(&mut ui, 160, 40);
    assert!(s.last().unwrap().contains("Enter Run"), "{}", s.join("\n"));
    // A narrow screen keeps what fits, and always the way to quit.
    ui.command(Command::FocusEditor);
    let s = screen(&mut ui, 50, 30);
    let last = s.last().unwrap();
    assert!(
        last.contains("Ctrl+S Save") && last.trim_end().ends_with("Ctrl+Q Quit"),
        "{}",
        s.join("\n")
    );
    // The palette names each command's key and runs it.
    ui.command(Command::Palette);
    typing(&mut ui, "definition");
    let s = screen(&mut ui, 160, 40);
    assert!(
        s.iter()
            .any(|row| row.contains("Go to the definition") && row.contains(" F12 │")),
        "{}",
        s.join("\n")
    );
    assert!(s.last().unwrap().contains("Enter Take"), "{}", s.join("\n"));
    ui.command(Command::Escape);
    ui.command(Command::Palette);
    typing(&mut ui, "key hints");
    ui.command(Command::Enter);
    assert!(!ui.hints);
    let s = screen(&mut ui, 160, 40);
    assert!(!shows(&s, "Ctrl+Q Quit"), "{}", s.join("\n"));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn an_empty_editor_shows_the_keys_to_begin_with() {
    let root = project("welcome");
    fs::write(root.join("app.crag"), "").unwrap();
    let mut ui = ui(&root);
    let s = screen(&mut ui, 120, 40);
    for text in [
        "Ctrl+P  Open a file",
        "Ctrl+K  Every command",
        "Ctrl+Q  Quit",
        "F1      Tell about the name at the cursor",
    ] {
        assert!(shows(&s, text), "{text} missing:\n{}", s.join("\n"));
    }
    typing(&mut ui, "x");
    let s = screen(&mut ui, 120, 40);
    assert!(!shows(&s, "Open a file"), "{}", s.join("\n"));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn the_editor_colours_code_by_its_tokens() {
    let root = project("colours");
    let mut ui = ui(&root);
    let mut terminal = Terminal::new(TestBackend::new(120, 40)).unwrap();
    let theme = Theme::new(Colours::Sixteen);
    terminal.draw(|frame| draw(frame, &mut ui, &theme)).unwrap();
    let buffer = terminal.backend().buffer().clone();
    // The colour of the first cell showing `word` on a row with `line`.
    let colour = |line: &str, word: &str| {
        (0..40)
            .find_map(|y| {
                let row: String = (0..120)
                    .map(|x| buffer[(x, y)].symbol().to_string())
                    .collect();
                if !row.contains(line) {
                    return None;
                }
                let x = row.chars().collect::<Vec<_>>();
                let at =
                    (0..x.len()).find(|&i| x[i..].iter().collect::<String>().starts_with(word))?;
                Some(buffer[(at as u16, y)].fg)
            })
            .unwrap()
    };
    use ratatui::style::Color;
    assert_eq!(colour("fn main()", "fn"), Color::Magenta);
    assert_eq!(colour("fn main()", "main"), Color::Blue);
    assert_eq!(colour("fn main()", "Int"), Color::Yellow);
    assert_eq!(colour("let p = Point", "2"), Color::Cyan);
    assert_eq!(colour("let p = Point", "p ="), Color::Reset);
    let _ = fs::remove_dir_all(&root);
}

const SERVER: &str = r#"import std.io

fn reply(c: Connection, n: Int) -> () {
  case c.read() {
    bytes: Bytes -> {
      let doubled = n * 2
      let written = c.write(b"done")
    }
    _ -> ()
  }
}

fn serve(l: Listener, n: Int) -> () {
  case l.accept() {
    c: Connection -> {
      reply(c, n)
      serve(l, n + 1)
    }
    _ -> ()
  }
}

fn main() -> () {
  case listen(PORT) {
    l: Listener -> serve(l, 1)
    _ -> ()
  }
}
"#;

/// Whether the tests compile in the optimizing tier, which inlines small
/// functions and reports them as inlined frames.
fn optimizing() -> bool {
    crag_mir::Tier::compiled() == crag_mir::Tier::Optimizing
}

#[test]
fn a_breakpoint_takes_the_ui_to_the_stopped_line() {
    use std::io::{Read, Write};
    use std::time::{Duration, Instant};

    let root = project("debug");
    let port = std::net::TcpListener::bind("127.0.0.1:0")
        .unwrap()
        .local_addr()
        .unwrap()
        .port();
    fs::write(
        root.join("app.crag"),
        SERVER.replace("PORT", &port.to_string()),
    )
    .unwrap();
    let mut ui = ui(&root);
    let line = SERVER
        .lines()
        .position(|l| l.contains("let doubled"))
        .unwrap();
    ui.buffer_mut().cursor = Cursor::at(ui.buffer().line_to_offset(line));
    ui.command(Command::Breakpoint);
    assert!(ui.has_breakpoint("app.crag", line as u32 + 1));
    ui.palette(crag_driver::ui::state::PaletteCommand::StartApp);
    let s = screen(&mut ui, 120, 40);
    assert!(shows(&s, "│ Run "), "{}", s.join("\n"));
    assert!(shows(&s, &format!("● {} │", line + 1)), "{}", s.join("\n"));
    let client = std::thread::spawn(move || {
        let mut stream = std::net::TcpStream::connect(("127.0.0.1", port)).unwrap();
        stream
            .set_read_timeout(Some(Duration::from_secs(20)))
            .unwrap();
        stream.write_all(b"hi").unwrap();
        let mut answer = String::new();
        stream.read_to_string(&mut answer).unwrap();
        answer
    });
    let deadline = Instant::now() + Duration::from_secs(20);
    while ui.pauses.is_empty() {
        assert!(Instant::now() < deadline, "no task stopped");
        std::thread::sleep(Duration::from_millis(10));
        ui.tick(Instant::now());
    }
    let s = screen(&mut ui, 120, 40);
    assert!(shows(&s, "Debug: 1 paused"), "{}", s.join("\n"));
    assert!(shows(&s, " Tasks "), "{}", s.join("\n"));
    // Inlined, the name says so, and the line no longer fits.
    let reply = match optimizing() {
        true => "reply (inlined)",
        false => "reply",
    };
    let stopped = match optimizing() {
        true => "⏸ reply (inlined) app.crag".to_string(),
        false => format!("⏸ reply app.crag:{}", line + 1),
    };
    assert!(shows(&s, &stopped), "{}", s.join("\n"));
    assert!(shows(&s, "n = 1"), "{}", s.join("\n"));
    assert!(
        shows(&s, &format!("▶{:>2} │", line + 1)),
        "{}",
        s.join("\n")
    );
    assert!(
        shows(&s, &format!("scratch [{reply} app.crag:{}]> ", line + 1)),
        "{}",
        s.join("\n")
    );
    // F10, then F5 with the breakpoint gone.
    ui.command(Command::StepOver);
    let deadline = Instant::now() + Duration::from_secs(20);
    while ui.pauses.is_empty() {
        assert!(Instant::now() < deadline, "the step did not stop");
        std::thread::sleep(Duration::from_millis(10));
        ui.tick(Instant::now());
    }
    assert_eq!(ui.pauses[0].line as usize, line + 2);
    ui.repl.set_breakpoints(&[]).unwrap();
    ui.command(Command::Continue);
    assert_eq!(client.join().unwrap(), "done");
    ui.palette(crag_driver::ui::state::PaletteCommand::StopApp);
    ui.tick(Instant::now());
    let s = screen(&mut ui, 120, 40);
    assert!(shows(&s, "│ Edit "), "{}", s.join("\n"));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn cd_opens_the_project_in_another_directory() {
    let root = project("cd-from");
    let other = std::env::temp_dir().join(format!("crag-ui-cd-to-{}", std::process::id()));
    let _ = fs::remove_dir_all(&other);
    fs::create_dir_all(&other).unwrap();
    fs::write(
        other.join("package.crag"),
        "package other 0.1\nruntime 0.0\nmain other.start\n",
    )
    .unwrap();
    fs::write(
        other.join("start.crag"),
        "pub fn twice(n: Int) -> Int { n * 2 }\n",
    )
    .unwrap();
    let mut ui = ui(&root);
    assert_eq!(ui.buffer().name, "app.crag");
    // An edit of the project left behind is saved.
    ui.buffer_mut().set_text("// edited\n");
    ui.run_repl(&format!(":cd {}", other.display()));
    assert_eq!(
        fs::read_to_string(root.join("app.crag")).unwrap(),
        "// edited\n"
    );
    assert_eq!(ui.buffer().name, "start.crag");
    assert_eq!(ui.project_files(), ["start.crag"]);
    ui.run_repl("import other.start");
    ui.run_repl("twice(21)");
    let shown = screen(&mut ui, 100, 30);
    assert!(shows(&shown, "42"), "{}", shown.join("\n"));
    let _ = fs::remove_dir_all(&root);
    let _ = fs::remove_dir_all(&other);
}
