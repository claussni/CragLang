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

//! The terminal UI (Specification §20.8): the built-in editor and the REPL,
//! over the project's queries in the same process.
//!
//! `state` holds what the UI shows and does, `keys` maps keys to commands,
//! `view` draws, and `run` is the terminal's event loop, which puts the
//! terminal back as it was when it ends, also on a panic.

pub mod buffer;
pub mod keys;
pub mod state;
pub mod view;

use std::io;
use std::time::{Duration, Instant};

use crossterm::event::{
    self, Event, KeyboardEnhancementFlags, PopKeyboardEnhancementFlags,
    PushKeyboardEnhancementFlags,
};
use crossterm::execute;
use crossterm::terminal::{
    EnterAlternateScreen, LeaveAlternateScreen, disable_raw_mode, enable_raw_mode,
    supports_keyboard_enhancement,
};
use ratatui::Terminal;
use ratatui::backend::CrosstermBackend;

pub use state::Ui;
pub use view::{Colours, Theme, draw};

/// How often the loop wakes without input, for the clock of `Ui::tick`.
const TICK: Duration = Duration::from_millis(50);

/// Puts the terminal back as it was.
fn restore(enhanced: bool) {
    let mut out = io::stdout();
    if enhanced {
        let _ = execute!(out, PopKeyboardEnhancementFlags);
    }
    let _ = execute!(out, LeaveAlternateScreen, crossterm::cursor::Show);
    let _ = disable_raw_mode();
}

/// Runs the UI on the terminal until it quits; the exit status.
pub fn run(mut ui: Ui) -> io::Result<u8> {
    enable_raw_mode()?;
    let mut out = io::stdout();
    execute!(out, EnterAlternateScreen)?;
    // Every modifier combination, where the terminal can tell them apart.
    let enhanced = supports_keyboard_enhancement().unwrap_or(false);
    if enhanced {
        execute!(
            out,
            PushKeyboardEnhancementFlags(KeyboardEnhancementFlags::DISAMBIGUATE_ESCAPE_CODES)
        )?;
    }
    let hook = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        restore(enhanced);
        hook(info);
    }));
    let result = event_loop(&mut ui);
    restore(enhanced);
    result
}

fn event_loop(ui: &mut Ui) -> io::Result<u8> {
    let mut terminal = Terminal::new(CrosstermBackend::new(io::stdout()))?;
    let theme = Theme::new(Colours::detect());
    loop {
        terminal.draw(|frame| draw(frame, ui, &theme))?;
        if ui.quit {
            return Ok(0);
        }
        if event::poll(TICK)? {
            match event::read()? {
                Event::Key(key) => {
                    if let Some(command) = keys::command(key) {
                        ui.command(command);
                    }
                }
                Event::Paste(text) => {
                    for c in text.chars() {
                        ui.command(keys::Command::Char(c));
                    }
                }
                _ => {}
            }
        }
        ui.tick(Instant::now());
    }
}
