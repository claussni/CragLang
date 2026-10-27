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

//! The key map (Specification §20.8.2): keys to commands. Every key works
//! without the extended keyboard protocol, which only adds combinations;
//! where terminals send a key in several ways, each is accepted.

use crossterm::event::{KeyCode, KeyEvent, KeyEventKind, KeyModifiers};

/// What a key asks for. Which part of the screen has the focus decides
/// what some of them do.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Command {
    QuickSwitch,
    Palette,
    CycleFocus,
    FocusLeft,
    FocusEditor,
    FocusRepl,
    FocusRight,
    ToggleLeft,
    ToggleRight,
    Escape,
    Quit,
    /// Moves; `select` extends the selection, `word` moves by words.
    Left {
        select: bool,
        word: bool,
    },
    Right {
        select: bool,
        word: bool,
    },
    Up {
        select: bool,
    },
    Down {
        select: bool,
    },
    Home {
        select: bool,
    },
    End {
        select: bool,
    },
    PageUp,
    PageDown,
    Char(char),
    Enter,
    /// A line break where Enter would evaluate.
    LineBreak,
    Backspace {
        word: bool,
    },
    Delete {
        word: bool,
    },
    Indent,
    Dedent,
    Save,
    Undo,
    Redo,
    Cut,
    /// Copies when text is selected, else interrupts (§20.8.2).
    CopyOrInterrupt,
    Paste,
    SelectAll,
    Find,
    ToggleComment,
    Complete,
    Info,
    Definition,
    References,
    Back,
    Forward,
    NextProblem,
    Evaluate,
    Reload,
    HistorySearch,
    ClearRepl,
    Breakpoint,
    Continue,
    Pause,
    StepOver,
    StepInto,
    StepOut,
}

/// The command of a key, if it has one.
pub fn command(key: KeyEvent) -> Option<Command> {
    use Command as C;
    if key.kind == KeyEventKind::Release {
        return None;
    }
    let m = key.modifiers;
    let ctrl = m.contains(KeyModifiers::CONTROL);
    let alt = m.contains(KeyModifiers::ALT);
    let shift = m.contains(KeyModifiers::SHIFT);
    // Ctrl moves by words; so does Alt, as on macOS.
    let word = ctrl || alt;
    Some(match key.code {
        KeyCode::Char(c) if ctrl && !alt => match c.to_ascii_lowercase() {
            'p' => C::QuickSwitch,
            'k' => C::Palette,
            'b' => C::ToggleLeft,
            'q' => C::Quit,
            's' => C::Save,
            'z' => C::Undo,
            'y' => C::Redo,
            'x' => C::Cut,
            'c' => C::CopyOrInterrupt,
            'v' => C::Paste,
            'a' => C::SelectAll,
            'f' => C::Find,
            'e' => C::Evaluate,
            'r' => C::HistorySearch,
            'l' => C::ClearRepl,
            // Terminals send Ctrl+/ as Ctrl+_ or Ctrl+7.
            '/' | '_' | '7' => C::ToggleComment,
            ' ' => C::Complete,
            'h' => C::Backspace { word: false },
            _ => return None,
        },
        KeyCode::Char(c) if alt && !ctrl => match c {
            '1' => C::FocusLeft,
            '2' => C::FocusEditor,
            '3' => C::FocusRepl,
            '4' => C::FocusRight,
            'b' => C::ToggleRight,
            'r' => C::Reload,
            ',' => C::Back,
            '.' => C::Forward,
            _ => return None,
        },
        KeyCode::Char(c) => C::Char(c),
        KeyCode::Enter if alt => C::LineBreak,
        KeyCode::Enter => C::Enter,
        KeyCode::Tab => C::Indent,
        KeyCode::BackTab => C::Dedent,
        KeyCode::Backspace => C::Backspace { word },
        KeyCode::Delete => C::Delete { word },
        KeyCode::Esc => C::Escape,
        KeyCode::Left => C::Left {
            select: shift,
            word,
        },
        KeyCode::Right => C::Right {
            select: shift,
            word,
        },
        KeyCode::Up => C::Up { select: shift },
        KeyCode::Down => C::Down { select: shift },
        KeyCode::Home => C::Home { select: shift },
        KeyCode::End => C::End { select: shift },
        KeyCode::PageUp => C::PageUp,
        KeyCode::PageDown => C::PageDown,
        KeyCode::F(1) => C::Info,
        KeyCode::F(5) if shift => C::Pause,
        KeyCode::F(5) => C::Continue,
        KeyCode::F(6) => C::CycleFocus,
        KeyCode::F(8) => C::NextProblem,
        KeyCode::F(9) => C::Breakpoint,
        KeyCode::F(10) => C::StepOver,
        KeyCode::F(11) if shift => C::StepOut,
        KeyCode::F(11) => C::StepInto,
        KeyCode::F(12) if shift => C::References,
        KeyCode::F(12) => C::Definition,
        _ => return None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(code: KeyCode, modifiers: KeyModifiers) -> Option<Command> {
        command(KeyEvent::new(code, modifiers))
    }

    #[test]
    fn the_map_follows_the_specification() {
        let ctrl = KeyModifiers::CONTROL;
        let alt = KeyModifiers::ALT;
        let shift = KeyModifiers::SHIFT;
        assert_eq!(key(KeyCode::Char('p'), ctrl), Some(Command::QuickSwitch));
        assert_eq!(key(KeyCode::Char('3'), alt), Some(Command::FocusRepl));
        assert_eq!(key(KeyCode::Char(' '), ctrl), Some(Command::Complete));
        assert_eq!(key(KeyCode::Char('_'), ctrl), Some(Command::ToggleComment));
        assert_eq!(key(KeyCode::F(12), shift), Some(Command::References));
        assert_eq!(key(KeyCode::F(11), shift), Some(Command::StepOut));
        assert_eq!(key(KeyCode::Enter, alt), Some(Command::LineBreak));
        assert_eq!(
            key(KeyCode::Left, ctrl | shift),
            Some(Command::Left {
                select: true,
                word: true
            })
        );
        assert_eq!(
            key(KeyCode::Char('x'), KeyModifiers::NONE),
            Some(Command::Char('x'))
        );
        assert_eq!(key(KeyCode::Char('j'), ctrl), None);
    }
}
