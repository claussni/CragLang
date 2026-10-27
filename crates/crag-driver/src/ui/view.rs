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

//! Drawing the UI (Specification §20.8.1): the editor over the REPL in the
//! centre, Buffers and Files on the left, the runtime's view on the right,
//! and the status bar. On a narrow screen the side panels lie over the
//! code while they have the focus; on a short one the editor and the REPL
//! take the centre in turn.
//!
//! Colours degrade from truecolor to 256 and 16 colours, and without
//! colour, or with `NO_COLOR`, bold and reverse video stand in. Every state
//! also has a symbol or a word.

use ratatui::Frame;
use ratatui::layout::{Constraint, Direction, Layout, Position, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::{Block, Borders, Clear, Paragraph};

use super::state::{Focus, Hint, Mode, OutKind, Overlay, RightView, Ui};

/// Below these the screen is narrow or short.
const NARROW: u16 = 100;
const SHORT: u16 = 20;
const LEFT: u16 = 20;
const RIGHT: u16 = 28;

/// How many colours the terminal shows.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Colours {
    None,
    Sixteen,
    Indexed,
    True,
}

impl Colours {
    /// From the environment: `NO_COLOR`, `COLORTERM` and `TERM`.
    pub fn detect() -> Colours {
        let var = |name| std::env::var(name).unwrap_or_default();
        if std::env::var_os("NO_COLOR").is_some_and(|v| !v.is_empty()) || var("TERM") == "dumb" {
            Colours::None
        } else if matches!(var("COLORTERM").as_str(), "truecolor" | "24bit") {
            Colours::True
        } else if var("TERM").contains("256color") {
            Colours::Indexed
        } else {
            Colours::Sixteen
        }
    }
}

/// The styles of the UI in the colours there are.
pub struct Theme {
    colours: Colours,
}

impl Theme {
    pub fn new(colours: Colours) -> Theme {
        Theme { colours }
    }

    fn colour(&self, true_colour: (u8, u8, u8), indexed: u8, basic: Color) -> Option<Color> {
        match self.colours {
            Colours::None => None,
            Colours::Sixteen => Some(basic),
            Colours::Indexed => Some(Color::Indexed(indexed)),
            Colours::True => Some(Color::Rgb(true_colour.0, true_colour.1, true_colour.2)),
        }
    }

    fn fg(&self, c: Option<Color>, fallback: Modifier) -> Style {
        match c {
            Some(c) => Style::default().fg(c),
            None => Style::default().add_modifier(fallback),
        }
    }

    fn dim(&self) -> Style {
        self.fg(
            self.colour((128, 128, 128), 244, Color::DarkGray),
            Modifier::DIM,
        )
    }

    fn error(&self) -> Style {
        self.fg(self.colour((220, 80, 80), 167, Color::Red), Modifier::BOLD)
    }

    fn accent(&self) -> Style {
        self.fg(self.colour((97, 175, 239), 75, Color::Cyan), Modifier::BOLD)
    }

    fn selected(&self) -> Style {
        Style::default().add_modifier(Modifier::REVERSED)
    }

    fn border(&self, focused: bool) -> Style {
        match focused {
            true => self.accent(),
            false => self.dim(),
        }
    }

    fn problem(&self) -> Style {
        self.error().add_modifier(Modifier::UNDERLINED)
    }
}

fn block<'a>(title: &'a str, focused: bool, theme: &Theme) -> Block<'a> {
    Block::default()
        .borders(Borders::ALL)
        .border_style(theme.border(focused))
        .title(Span::styled(format!(" {title} "), theme.border(focused)))
}

/// Draws the whole UI.
pub fn draw(frame: &mut Frame, ui: &mut Ui, theme: &Theme) {
    let area = frame.area();
    let hints = u16::from(ui.hints);
    let rows = Layout::default()
        .direction(Direction::Vertical)
        .constraints([
            Constraint::Min(1),
            Constraint::Length(1),
            Constraint::Length(hints),
        ])
        .split(area);
    let (body, status) = (rows[0], rows[1]);
    let narrow = area.width < NARROW;
    let short = area.height < SHORT;
    let left = ui.left_open && !narrow;
    let right = ui.right_open && !narrow;
    let mut constraints = Vec::new();
    if left {
        constraints.push(Constraint::Length(LEFT));
    }
    constraints.push(Constraint::Min(10));
    if right {
        constraints.push(Constraint::Length(RIGHT));
    }
    let columns = Layout::default()
        .direction(Direction::Horizontal)
        .constraints(constraints)
        .split(body);
    let mut c = 0;
    if left {
        draw_left(frame, ui, theme, columns[c]);
        c += 1;
    }
    let centre = columns[c];
    if right {
        draw_right(frame, ui, theme, columns[c + 1]);
    }
    if short {
        // The editor and the REPL take the centre in turn.
        match ui.focus {
            Focus::Repl => draw_repl(frame, ui, theme, centre),
            _ => draw_editor(frame, ui, theme, centre),
        }
    } else {
        let repl_height = (centre.height / 3).max(5);
        let parts = Layout::default()
            .direction(Direction::Vertical)
            .constraints([Constraint::Min(3), Constraint::Length(repl_height)])
            .split(centre);
        draw_editor(frame, ui, theme, parts[0]);
        draw_repl(frame, ui, theme, parts[1]);
    }
    if narrow {
        // The side panels lie over the code while they have the focus.
        if matches!(ui.focus, Focus::Buffers | Focus::Files) {
            let over = Rect {
                width: LEFT.min(body.width),
                ..body
            };
            frame.render_widget(Clear, over);
            draw_left(frame, ui, theme, over);
        }
        if ui.focus == Focus::Right {
            let width = RIGHT.min(body.width);
            let over = Rect {
                x: body.x + body.width - width,
                width,
                ..body
            };
            frame.render_widget(Clear, over);
            draw_right(frame, ui, theme, over);
        }
    }
    draw_status(frame, ui, theme, status);
    if ui.hints {
        draw_hints(frame, ui, theme, rows[2]);
    }
    draw_overlay(frame, ui, theme, body);
}

fn draw_left(frame: &mut Frame, ui: &Ui, theme: &Theme, area: Rect) {
    let parts = Layout::default()
        .direction(Direction::Vertical)
        .constraints([Constraint::Percentage(40), Constraint::Percentage(60)])
        .split(area);
    let lines: Vec<Line> = ui
        .buffers
        .iter()
        .enumerate()
        .map(|(i, b)| {
            let mark = if b.dirty() {
                "● "
            } else if ui.differs_from_app(b) {
                "◆ "
            } else if b.readonly {
                "· "
            } else {
                "  "
            };
            let name = b
                .name
                .trim_end_matches(".crag")
                .trim_end_matches(" (bundled)");
            let mut style = Style::default();
            if i == ui.current {
                style = style.add_modifier(Modifier::BOLD);
            }
            if ui.focus == Focus::Buffers && i == ui.buffer_selected {
                style = theme.selected();
            }
            Line::styled(format!("{mark}{name}"), style)
        })
        .collect();
    frame.render_widget(
        Paragraph::new(lines).block(block("Buffers", ui.focus == Focus::Buffers, theme)),
        parts[0],
    );
    let lines: Vec<Line> = ui
        .file_tree()
        .into_iter()
        .enumerate()
        .map(|(i, item)| {
            let marker = match (&item.dir, item.open) {
                (Some(_), true) => "▾ ",
                (Some(_), false) => "▸ ",
                (None, _) => "  ",
            };
            let text = format!("{}{marker}{}", " ".repeat(item.depth), item.label);
            let style = match ui.focus == Focus::Files && i == ui.file_selected {
                true => theme.selected(),
                false => Style::default(),
            };
            Line::styled(text, style)
        })
        .collect();
    frame.render_widget(
        Paragraph::new(lines).block(block("Files", ui.focus == Focus::Files, theme)),
        parts[1],
    );
}

fn draw_editor(frame: &mut Frame, ui: &mut Ui, theme: &Theme, area: Rect) {
    let focused = ui.focus == Focus::Editor;
    let title = {
        let b = ui.buffer();
        let mark = if b.dirty() {
            " ●"
        } else if b.readonly {
            " (read-only)"
        } else {
            ""
        };
        format!("{}{mark}", b.name)
    };
    let outer = block(&title, focused, theme);
    let inner = outer.inner(area);
    frame.render_widget(outer, area);
    let height = inner.height as usize;
    ui.page = height.max(1);
    let name = ui.buffer().name.clone();
    let problems: Vec<_> = ui
        .problems
        .iter()
        .filter(|p| p.file == name)
        .cloned()
        .collect();
    let b = ui.buffer();
    let (cursor_line, cursor_col) = b.line_col(b.cursor.pos);
    let digits = b.lines().to_string().len().max(2);
    let gutter = digits + 4;
    let width = (inner.width as usize).saturating_sub(gutter).max(1);
    // Lines scroll sideways to keep the cursor in view.
    let hscroll = cursor_col.saturating_sub(width - 1);
    let selection = b.cursor.selection();
    let mut lines = Vec::new();
    for line in b.scroll..(b.scroll + height).min(b.lines()) {
        let number = line + 1;
        let breakpoint = ui.has_breakpoint(&name, number as u32);
        let problem = problems.iter().any(|p| p.line == number);
        let stopped = ui
            .pauses
            .iter()
            .any(|p| p.file == name && p.line as usize == number);
        let mark = if stopped {
            "▶"
        } else if breakpoint {
            "●"
        } else if problem {
            "!"
        } else {
            " "
        };
        let mark_style = if problem && !breakpoint && !stopped {
            theme.error()
        } else {
            theme.accent()
        };
        let mut spans = vec![
            Span::styled(mark, mark_style),
            Span::styled(format!("{number:>digits$} │ "), theme.dim()),
        ];
        let start = b.line_to_offset(line);
        let text: Vec<char> = b.line_text(line).chars().collect();
        for (col, &ch) in text.iter().enumerate().skip(hscroll).take(width) {
            let pos = start + col;
            let byte = b.byte_of(pos);
            let mut style = Style::default();
            if problems
                .iter()
                .any(|p| p.start <= byte && byte < p.end.max(p.start + 1))
            {
                style = theme.problem();
            }
            if selection.as_ref().is_some_and(|r| r.contains(&pos)) {
                style = theme.selected();
            }
            spans.push(Span::styled(ch.to_string(), style));
        }
        if let Some((_, _, result)) = ui.inline.iter().find(|(n, l, _)| *n == name && *l == line) {
            spans.push(Span::styled(format!("  ⇒ {result}"), theme.dim()));
        }
        lines.push(Line::from(spans));
    }
    frame.render_widget(Paragraph::new(lines), inner);
    if b.is_empty() {
        draw_welcome(frame, theme, inner);
    }
    if focused && ui.overlay.is_none() && cursor_line >= b.scroll && cursor_line < b.scroll + height
    {
        let x = inner.x + (gutter + cursor_col - hscroll) as u16;
        let y = inner.y + (cursor_line - b.scroll) as u16;
        frame.set_cursor_position(Position::new(x.min(inner.right().saturating_sub(1)), y));
    }
}

fn draw_repl(frame: &mut Frame, ui: &Ui, theme: &Theme, area: Rect) {
    let focused = ui.focus == Focus::Repl;
    let outer = block("REPL", focused, theme);
    let inner = outer.inner(area);
    frame.render_widget(outer, area);
    let prompt = ui.prompt();
    let input_lines: Vec<String> = ui.input.text().split('\n').map(str::to_string).collect();
    let height = inner.height as usize;
    let room = height.saturating_sub(input_lines.len());
    // A type joins the line of its value.
    let mut rows: Vec<Line> = Vec::new();
    for out in &ui.output {
        let style = match out.kind {
            OutKind::Input => Style::default().add_modifier(Modifier::BOLD),
            OutKind::Value => Style::default(),
            OutKind::Type | OutKind::Info => theme.dim(),
            OutKind::Error => theme.error(),
        };
        match (out.kind, rows.last_mut()) {
            (OutKind::Type, Some(last)) => last.spans.push(Span::styled(out.text.clone(), style)),
            _ => rows.push(Line::styled(out.text.clone(), style)),
        }
    }
    let skip = rows.len().saturating_sub(room);
    let shown = rows.len() - skip;
    let mut lines: Vec<Line> = rows.into_iter().skip(skip).collect();
    for (i, text) in input_lines.iter().enumerate() {
        let lead = if i == 0 {
            prompt.clone()
        } else {
            " ".repeat(prompt.chars().count())
        };
        lines.push(Line::from(vec![
            Span::styled(lead, theme.accent()),
            Span::raw(text.clone()),
        ]));
    }
    frame.render_widget(Paragraph::new(lines), inner);
    if focused && ui.overlay.is_none() {
        let (line, col) = ui.input.line_col(ui.input.cursor.pos);
        let top = inner.y + (height.min(shown + input_lines.len()) - input_lines.len()) as u16;
        let x = inner.x + (prompt.chars().count() + col) as u16;
        let y = top + line as u16;
        if y < inner.bottom() {
            frame.set_cursor_position(Position::new(x.min(inner.right().saturating_sub(1)), y));
        }
    }
}

fn draw_right(frame: &mut Frame, ui: &mut Ui, theme: &Theme, area: Rect) {
    let focused = ui.focus == Focus::Right;
    let mut lines: Vec<Line> = Vec::new();
    let selected = |i: usize| match focused {
        true if i == ui.right_selected => theme.selected(),
        _ => Style::default(),
    };
    match ui.right_view {
        RightView::Problems => {
            if ui.problems.is_empty() {
                lines.push(Line::styled("no problems", theme.dim()));
            }
            for (i, p) in ui.problems.iter().enumerate() {
                lines.push(Line::styled(
                    format!("! {}:{}", p.file, p.line),
                    selected(i).patch(theme.error()),
                ));
                lines.push(Line::styled(format!("  {}", p.message), selected(i)));
            }
        }
        RightView::Tasks => {
            if ui.pauses.is_empty() {
                let text = if ui.repl.app_runs() {
                    "no task is stopped"
                } else {
                    "no app runs"
                };
                lines.push(Line::styled(text, theme.dim()));
            }
            for (i, p) in ui.pauses.iter().enumerate() {
                lines.push(Line::styled(
                    format!("⏸ {} {}:{}", p.function, p.file, p.line),
                    selected(i),
                ));
                for caller in &p.callers {
                    lines.push(Line::styled(format!("   {caller}"), theme.dim()));
                }
            }
            if !ui.pauses.is_empty() {
                lines.push(Line::raw(""));
                for (name, value) in ui.chosen_locals() {
                    lines.push(Line::raw(format!("{name} = {value}")));
                }
            }
        }
        RightView::Watches => lines.push(Line::styled("no watches", theme.dim())),
        RightView::Tests => lines.push(Line::styled("no tests have run", theme.dim())),
    }
    let title = ui.right_view.name();
    frame.render_widget(
        Paragraph::new(lines).block(block(title, focused, theme)),
        area,
    );
}

fn draw_status(frame: &mut Frame, ui: &Ui, theme: &Theme, area: Rect) {
    let project = ui.repl.project().package.clone();
    let project = if project.is_empty() {
        "no project".to_string()
    } else {
        project
    };
    let mode = match ui.mode() {
        Mode::Edit => "Edit".to_string(),
        Mode::Run => "Run".to_string(),
        Mode::Debug(n) => format!("Debug: {n} paused"),
    };
    let mut spans = vec![
        Span::styled(format!(" {project} "), theme.accent()),
        Span::styled("│", theme.dim()),
        Span::raw(format!(" {} ", ui.buffer().name)),
        Span::styled("│", theme.dim()),
        Span::raw(format!(" {} ", ui.focus.name())),
        Span::styled("│", theme.dim()),
        Span::styled(
            format!(" {mode} "),
            Style::default().add_modifier(Modifier::BOLD),
        ),
    ];
    if let Some(message) = &ui.message {
        spans.push(Span::styled("│ ", theme.dim()));
        spans.push(Span::raw(message.clone()));
    }
    frame.render_widget(Paragraph::new(Line::from(spans)), area);
}

/// The hint line: the keys that always work on the right, and as many of
/// those that matter now as fit before them.
fn draw_hints(frame: &mut Frame, ui: &Ui, theme: &Theme, area: Rect) {
    let (now, always) = ui.hints();
    let width = |(key, what): &Hint| key.chars().count() + what.chars().count() + 3;
    let room = area.width as usize;
    let right: usize = always.iter().map(width).sum();
    let spans_of = |hints: &[Hint], room: usize| {
        let mut spans = Vec::new();
        let mut used = 0;
        for hint in hints {
            if used + width(hint) > room {
                break;
            }
            used += width(hint);
            spans.push(Span::styled(
                format!(" {}", hint.0),
                theme.accent().add_modifier(Modifier::BOLD),
            ));
            spans.push(Span::styled(format!(" {} ", hint.1), theme.dim()));
        }
        (spans, used)
    };
    let (mut spans, used) = spans_of(&now, room.saturating_sub(right));
    let (end, end_used) = spans_of(&always, room - used);
    spans.push(Span::raw(" ".repeat(room - used - end_used)));
    spans.extend(end);
    frame.render_widget(Paragraph::new(Line::from(spans)), area);
}

/// What an empty editor shows: the keys to begin with.
const WELCOME: [(&str, &str); 6] = [
    ("Ctrl+P", "Open a file"),
    ("Ctrl+K", "Every command, with its key"),
    ("Ctrl+E", "Evaluate the line in the REPL"),
    ("F6", "Move to the next panel"),
    ("F1", "Tell about the name at the cursor"),
    ("Ctrl+Q", "Quit"),
];

/// The column the welcome's explanations start at.
const KEY: usize = 8;

fn draw_welcome(frame: &mut Frame, theme: &Theme, area: Rect) {
    let width = WELCOME
        .iter()
        .map(|(k, w)| k.len().max(KEY) + w.len())
        .max()
        .unwrap_or(0) as u16;
    let height = WELCOME.len() as u16 + 2;
    if area.width < width || area.height < height + 2 {
        return;
    }
    let mut lines = vec![
        Line::styled("Crag", theme.accent().add_modifier(Modifier::BOLD)),
        Line::raw(""),
    ];
    for (key, what) in WELCOME {
        lines.push(Line::from(vec![
            Span::styled(format!("{key:<KEY$}"), theme.accent()),
            Span::styled(what, theme.dim()),
        ]));
    }
    frame.render_widget(Paragraph::new(lines), centred(area, width, height));
}

fn centred(area: Rect, width: u16, height: u16) -> Rect {
    let width = width.min(area.width);
    let height = height.min(area.height);
    Rect {
        x: area.x + (area.width - width) / 2,
        y: area.y + (area.height - height) / 3,
        width,
        height,
    }
}

fn draw_overlay(frame: &mut Frame, ui: &Ui, theme: &Theme, area: Rect) {
    let Some(overlay) = &ui.overlay else {
        return;
    };
    match overlay {
        Overlay::Pick(picker) => {
            let preview = picker.title == "Open";
            let width = if preview {
                area.width * 4 / 5
            } else {
                area.width * 3 / 5
            };
            let over = centred(area, width.max(30), area.height * 3 / 4);
            frame.render_widget(Clear, over);
            let outer = block(&picker.title, true, theme);
            let inner = outer.inner(over);
            frame.render_widget(outer, over);
            let columns = Layout::default()
                .direction(Direction::Horizontal)
                .constraints(match preview {
                    true => vec![Constraint::Percentage(45), Constraint::Percentage(55)],
                    false => vec![Constraint::Percentage(100)],
                })
                .split(inner);
            let mut lines = vec![Line::from(vec![
                Span::styled("> ", theme.accent()),
                Span::raw(picker.query.clone()),
            ])];
            let room = (columns[0].height as usize).saturating_sub(1);
            let first = picker.selected.saturating_sub(room.saturating_sub(1));
            for (k, &i) in picker.shown.iter().enumerate().skip(first).take(room) {
                let item = &picker.items[i];
                let style = if k == picker.selected {
                    theme.selected()
                } else {
                    Style::default()
                };
                let mut spans = vec![Span::styled(item.label.clone(), style)];
                if !item.detail.is_empty() {
                    // Details stand at the right, where they line up.
                    let gap = (columns[0].width as usize - 1)
                        .saturating_sub(item.label.chars().count() + item.detail.chars().count())
                        .max(2);
                    spans.push(Span::raw(" ".repeat(gap)));
                    spans.push(Span::styled(item.detail.clone(), theme.dim()));
                }
                lines.push(Line::from(spans));
            }
            frame.render_widget(Paragraph::new(lines), columns[0]);
            if preview
                && let Some(super::state::Target::File(file, _)) =
                    picker.current().map(|i| &i.target)
            {
                let project = ui.repl.project();
                let text = project
                    .files
                    .iter()
                    .find(|f| &f.shown == file)
                    .map(|f| project.source(f.module).to_string())
                    .unwrap_or_default();
                let lines: Vec<Line> = text
                    .lines()
                    .take(columns[1].height as usize)
                    .map(|l| Line::styled(l.to_string(), theme.dim()))
                    .collect();
                frame.render_widget(
                    Paragraph::new(lines).block(
                        Block::default()
                            .borders(Borders::LEFT)
                            .border_style(theme.dim()),
                    ),
                    columns[1],
                );
            }
            frame.set_cursor_position(Position::new(
                columns[0].x + 2 + picker.query.chars().count() as u16,
                columns[0].y,
            ));
        }
        Overlay::Find {
            query,
            replace,
            replacing,
        } => {
            let over = Rect {
                x: area.x + area.width / 4,
                y: area.y + 1,
                width: area.width / 2,
                height: 3,
            };
            frame.render_widget(Clear, over);
            let mut spans = vec![
                Span::styled("Find: ", theme.accent()),
                Span::raw(query.clone()),
            ];
            if let Some(replace) = replace {
                spans.push(Span::styled("  Replace: ", theme.accent()));
                spans.push(Span::raw(replace.clone()));
            }
            frame.render_widget(
                Paragraph::new(Line::from(spans)).block(block("Find", true, theme)),
                over,
            );
            let x = match (replacing, replace) {
                (true, Some(r)) => {
                    over.x + 1 + 6 + query.chars().count() as u16 + 11 + r.chars().count() as u16
                }
                _ => over.x + 1 + 6 + query.chars().count() as u16,
            };
            frame.set_cursor_position(Position::new(x.min(over.right() - 2), over.y + 1));
        }
        Overlay::Info(text) => {
            let lines: Vec<Line> = text.lines().map(|l| Line::raw(l.to_string())).collect();
            let width = text.lines().map(|l| l.chars().count()).max().unwrap_or(10) as u16 + 4;
            let over = centred(area, width.max(20), lines.len() as u16 + 2);
            frame.render_widget(Clear, over);
            frame.render_widget(
                Paragraph::new(lines).block(block("Information", true, theme)),
                over,
            );
        }
        Overlay::Completion {
            items, selected, ..
        } => {
            let height = (items.len().min(10) + 2) as u16;
            let over = centred(area, area.width / 2, height);
            frame.render_widget(Clear, over);
            let first = selected.saturating_sub(9);
            let lines: Vec<Line> = items
                .iter()
                .enumerate()
                .skip(first)
                .take(10)
                .map(|(i, c)| {
                    let style = if i == *selected {
                        theme.selected()
                    } else {
                        Style::default()
                    };
                    Line::from(vec![
                        Span::styled(c.label.clone(), style),
                        Span::styled(format!("  {}", c.detail), theme.dim()),
                    ])
                })
                .collect();
            frame.render_widget(
                Paragraph::new(lines).block(block("Complete", true, theme)),
                over,
            );
        }
        Overlay::Confirm { question, .. } => {
            let text = format!("{question} [y|N]");
            let over = centred(area, text.chars().count() as u16 + 4, 3);
            frame.render_widget(Clear, over);
            frame.render_widget(
                Paragraph::new(text).block(block("Confirm", true, theme)),
                over,
            );
        }
    }
}
