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

/// The key of a command, as the hint line and the command palette name
/// it; none for commands whose key depends on where the focus is.
pub fn key_name(command: Command) -> Option<&'static str> {
    use Command as C;
    Some(match command {
        C::QuickSwitch => "Ctrl+P",
        C::Palette => "Ctrl+K",
        C::CycleFocus => "F6",
        C::FocusLeft => "Alt+1",
        C::FocusEditor => "Alt+2",
        C::FocusRepl => "Alt+3",
        C::FocusRight => "Alt+4",
        C::ToggleLeft => "Ctrl+B",
        C::ToggleRight => "Alt+B",
        C::Escape => "Esc",
        C::Quit => "Ctrl+Q",
        C::Enter => "Enter",
        C::LineBreak => "Alt+Enter",
        C::Indent => "Tab",
        C::Save => "Ctrl+S",
        C::Undo => "Ctrl+Z",
        C::Redo => "Ctrl+Y",
        C::Cut => "Ctrl+X",
        C::CopyOrInterrupt => "Ctrl+C",
        C::Paste => "Ctrl+V",
        C::SelectAll => "Ctrl+A",
        C::Find => "Ctrl+F",
        C::ToggleComment => "Ctrl+/",
        C::Complete => "Ctrl+Space",
        C::Info => "F1",
        C::Definition => "F12",
        C::References => "Shift+F12",
        C::Back => "Alt+,",
        C::Forward => "Alt+.",
        C::NextProblem => "F8",
        C::Evaluate => "Ctrl+E",
        C::Reload => "Alt+R",
        C::HistorySearch => "Ctrl+R",
        C::ClearRepl => "Ctrl+L",
        C::Breakpoint => "F9",
        C::Continue => "F5",
        C::Pause => "Shift+F5",
        C::StepOver => "F10",
        C::StepInto => "F11",
        C::StepOut => "Shift+F11",
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

    /// The key a name spells.
    fn parse(name: &str) -> KeyEvent {
        let mut modifiers = KeyModifiers::NONE;
        let mut rest = name;
        for (prefix, m) in [
            ("Ctrl+", KeyModifiers::CONTROL),
            ("Alt+", KeyModifiers::ALT),
            ("Shift+", KeyModifiers::SHIFT),
        ] {
            if let Some(r) = rest.strip_prefix(prefix) {
                modifiers |= m;
                rest = r;
            }
        }
        let code = match rest {
            "Esc" => KeyCode::Esc,
            "Enter" => KeyCode::Enter,
            "Tab" => KeyCode::Tab,
            "Space" => KeyCode::Char(' '),
            f if f.len() > 1 && f.starts_with('F') => KeyCode::F(f[1..].parse().unwrap()),
            c => KeyCode::Char(c.chars().next().unwrap().to_ascii_lowercase()),
        };
        KeyEvent::new(code, modifiers)
    }

    #[test]
    fn the_named_keys_are_the_keys_of_their_commands() {
        use Command as C;
        for command in [
            C::QuickSwitch,
            C::Palette,
            C::CycleFocus,
            C::FocusLeft,
            C::FocusEditor,
            C::FocusRepl,
            C::FocusRight,
            C::ToggleLeft,
            C::ToggleRight,
            C::Escape,
            C::Quit,
            C::Enter,
            C::LineBreak,
            C::Indent,
            C::Save,
            C::Undo,
            C::Redo,
            C::Cut,
            C::CopyOrInterrupt,
            C::Paste,
            C::SelectAll,
            C::Find,
            C::ToggleComment,
            C::Complete,
            C::Info,
            C::Definition,
            C::References,
            C::Back,
            C::Forward,
            C::NextProblem,
            C::Evaluate,
            C::Reload,
            C::HistorySearch,
            C::ClearRepl,
            C::Breakpoint,
            C::Continue,
            C::Pause,
            C::StepOver,
            C::StepInto,
            C::StepOut,
        ] {
            let name = key_name(command).unwrap();
            assert_eq!(command_of(name), Some(command), "{name}");
        }
    }

    fn command_of(name: &str) -> Option<Command> {
        command(parse(name))
    }
}
