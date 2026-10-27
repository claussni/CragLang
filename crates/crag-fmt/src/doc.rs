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

//! Documents and their layout (Implementation Plan §11.8.3), after
//! Wadler's "A prettier printer": a document is text with possible line
//! breaks, and a group either fits on the rest of its line, with every
//! break of its own laid out flat, or breaks them all.

/// A document.
#[derive(Clone, Debug)]
pub enum Doc {
    Nil,
    Text(Box<str>),
    /// A space when its group is flat, a line break when it breaks.
    Line,
    /// Nothing when its group is flat, a line break when it breaks.
    SoftLine,
    /// A line break that breaks every group around it.
    HardLine,
    /// A line break with an empty line after it, if text follows; repeated
    /// ones still leave only one empty line.
    BlankLine,
    /// A line break unless the line holds nothing yet; it breaks the
    /// groups around it like a `HardLine`.
    FreshLine,
    /// Text put at the end of the line, just before its line break: a
    /// trailing comment. A group holding one fits only if nothing of the
    /// group follows it on the line.
    LineSuffix(Box<str>),
    Concat(Vec<Doc>),
    /// Lines inside start one level deeper.
    Indent(Box<Doc>),
    /// The document, and whether something in it forces it to break.
    Group(Box<Doc>, bool),
    /// The first document when the enclosing group breaks, else the second.
    IfBreak(Box<Doc>, Box<Doc>),
    /// A document that never breaks but at its hard line breaks: a string
    /// with interpolations.
    Flat(Box<Doc>),
}

/// The width of one level of indentation.
const INDENT: usize = 2;

pub fn text(text: impl Into<Box<str>>) -> Doc {
    Doc::Text(text.into())
}

pub fn concat(docs: impl IntoIterator<Item = Doc>) -> Doc {
    Doc::Concat(docs.into_iter().collect())
}

pub fn indent(doc: Doc) -> Doc {
    Doc::Indent(Box::new(doc))
}

pub fn group(doc: Doc) -> Doc {
    let hard = doc.is_hard();
    Doc::Group(Box::new(doc), hard)
}

pub fn flat(doc: Doc) -> Doc {
    Doc::Flat(Box::new(doc))
}

pub fn if_break(broken: Doc, flat: Doc) -> Doc {
    Doc::IfBreak(Box::new(broken), Box::new(flat))
}

impl Doc {
    /// Whether the document holds a forced break, which breaks every group
    /// it is in.
    fn is_hard(&self) -> bool {
        match self {
            Doc::HardLine | Doc::BlankLine | Doc::FreshLine => true,
            Doc::Concat(docs) => docs.iter().any(Doc::is_hard),
            Doc::Indent(doc) | Doc::Flat(doc) => doc.is_hard(),
            Doc::Group(_, hard) => *hard,
            Doc::IfBreak(broken, flat) => broken.is_hard() || flat.is_hard(),
            Doc::Nil | Doc::Text(_) | Doc::Line | Doc::SoftLine | Doc::LineSuffix(_) => false,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    Flat,
    Break,
}

/// Lays `doc` out in lines of at most `width` columns where it can. The
/// result ends in a line break.
pub fn layout(doc: &Doc, width: usize) -> String {
    let mut out = Output::default();
    let mut stack: Vec<(usize, Mode, &Doc)> = vec![(0, Mode::Break, doc)];
    while let Some((level, mode, doc)) = stack.pop() {
        match doc {
            Doc::Nil => {}
            Doc::Text(s) => out.text(s, level),
            Doc::Line | Doc::SoftLine if mode == Mode::Flat => {
                if matches!(doc, Doc::Line) {
                    out.text(" ", level);
                }
            }
            Doc::Line | Doc::SoftLine | Doc::HardLine => out.newline(level, 1),
            Doc::BlankLine => out.newline(level, 2),
            Doc::FreshLine => {
                if !out.at_line_start() {
                    out.newline(level, 1);
                }
            }
            Doc::LineSuffix(s) => out.suffixes.push(s.to_string()),
            Doc::Concat(docs) => stack.extend(docs.iter().rev().map(|d| (level, mode, d))),
            Doc::Indent(doc) => stack.push((level + INDENT, mode, doc)),
            Doc::Flat(doc) => stack.push((level, Mode::Flat, doc)),
            Doc::Group(doc, hard) => {
                let flat = mode == Mode::Flat || (!hard && fits(&out, width, (level, doc), &stack));
                let mode = if flat { Mode::Flat } else { Mode::Break };
                stack.push((level, mode, doc));
            }
            Doc::IfBreak(broken, flat) => {
                stack.push((level, mode, if mode == Mode::Break { broken } else { flat }));
            }
        }
    }
    out.finish()
}

/// Whether `group` fits flat on the rest of the line, together with what
/// follows it up to the next line break.
fn fits(out: &Output, width: usize, group: (usize, &Doc), rest: &[(usize, Mode, &Doc)]) -> bool {
    let mut left = width as isize - out.column() as isize;
    let mut stack = vec![(Mode::Flat, group.1)];
    let mut rest = rest.iter().rev();
    // A trailing comment in the group, which must end its line.
    let mut suffix = false;
    loop {
        let in_group = !stack.is_empty();
        let Some((mode, doc)) = stack.pop().or_else(|| rest.next().map(|&(_, m, d)| (m, d))) else {
            return true;
        };
        match doc {
            Doc::Nil => {}
            Doc::LineSuffix(_) => suffix |= in_group,
            Doc::Text(_) if suffix && in_group => return false,
            Doc::Text(s) => match s.split_once('\n') {
                Some((first, _)) => return left >= first.chars().count() as isize,
                None => left -= s.chars().count() as isize,
            },
            Doc::Line | Doc::SoftLine if mode == Mode::Flat => {
                if matches!(doc, Doc::Line) {
                    left -= 1;
                }
            }
            Doc::Line | Doc::SoftLine | Doc::HardLine | Doc::BlankLine | Doc::FreshLine => {
                return true;
            }
            Doc::Concat(docs) => stack.extend(docs.iter().rev().map(|d| (mode, d))),
            Doc::Indent(doc) => stack.push((mode, doc)),
            Doc::Flat(doc) => stack.push((Mode::Flat, doc)),
            // A group after this one is measured flat up to its first break;
            // a broken one would break there.
            Doc::Group(doc, hard) => {
                stack.push((if *hard { Mode::Break } else { mode }, doc));
            }
            Doc::IfBreak(broken, flat) => {
                stack.push((mode, if mode == Mode::Break { broken } else { flat }));
            }
        }
        if left < 0 {
            return false;
        }
    }
}

/// The text laid out so far. Line breaks are kept pending until text
/// follows, so no line ends in spaces and blank lines merge.
#[derive(Default)]
struct Output {
    text: String,
    column: usize,
    /// Line breaks still to write, and the indentation after them.
    newlines: usize,
    indent: usize,
    /// Spaces still to write, dropped at a line break.
    spaces: usize,
    /// Trailing comments waiting for the end of the line.
    suffixes: Vec<String>,
}

impl Output {
    fn text(&mut self, s: &str, level: usize) {
        if !s.is_empty() && s.bytes().all(|b| b == b' ') {
            self.spaces += s.len();
            return;
        }
        if self.newlines > 0 {
            for _ in 0..self.newlines {
                self.text.push('\n');
            }
            self.newlines = 0;
            self.text.extend(std::iter::repeat_n(' ', self.indent));
            self.column = self.indent;
        } else if self.text.is_empty() {
            self.text.extend(std::iter::repeat_n(' ', level));
            self.column = level;
        }
        self.text.extend(std::iter::repeat_n(' ', self.spaces));
        self.column += self.spaces;
        self.spaces = 0;
        self.text.push_str(s);
        match s.rsplit_once('\n') {
            Some((_, last)) => self.column = last.chars().count(),
            None => self.column += s.chars().count(),
        }
    }

    fn newline(&mut self, level: usize, count: usize) {
        self.spaces = 0;
        for suffix in std::mem::take(&mut self.suffixes) {
            self.text.push_str(&suffix);
        }
        if !self.text.is_empty() {
            self.newlines = self.newlines.max(count);
            self.indent = level;
        }
    }

    fn at_line_start(&self) -> bool {
        self.newlines > 0 || self.text.is_empty()
    }

    /// The column the next text starts in.
    fn column(&self) -> usize {
        if self.newlines > 0 {
            self.indent
        } else {
            self.column + self.spaces
        }
    }

    fn finish(mut self) -> String {
        self.spaces = 0;
        for suffix in std::mem::take(&mut self.suffixes) {
            self.text.push_str(&suffix);
        }
        if !self.text.is_empty() {
            self.text.push('\n');
        }
        self.text
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(args: &[&str]) -> Doc {
        let mut items = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if i > 0 {
                items.push(text(","));
                items.push(Doc::Line);
            }
            items.push(text(*arg));
        }
        items.push(if_break(text(","), Doc::Nil));
        group(concat([
            text("f("),
            indent(concat([Doc::SoftLine, concat(items)])),
            Doc::SoftLine,
            text(")"),
        ]))
    }

    #[test]
    fn a_group_that_fits_stays_flat() {
        assert_eq!(layout(&call(&["a", "b"]), 20), "f(a, b)\n");
    }

    #[test]
    fn a_group_that_does_not_fit_breaks_every_line() {
        assert_eq!(
            layout(&call(&["alpha", "beta"]), 10),
            "f(\n  alpha,\n  beta,\n)\n"
        );
    }

    #[test]
    fn text_after_a_group_counts_toward_its_line() {
        let doc = concat([call(&["a", "b"]), text(" { x }")]);
        assert_eq!(layout(&doc, 10), "f(\n  a,\n  b,\n) { x }\n");
    }

    #[test]
    fn a_trailing_comment_at_the_end_of_a_group_leaves_it_flat() {
        let doc = concat([
            group(concat([
                text("f(a,"),
                Doc::Line,
                text("b)"),
                Doc::LineSuffix("  // c".into()),
            ])),
            Doc::HardLine,
            text("g"),
        ]);
        assert_eq!(layout(&doc, 80), "f(a, b)  // c\ng\n");
    }

    #[test]
    fn a_trailing_comment_breaks_its_group_and_ends_the_line() {
        let doc = group(concat([
            text("f(a,"),
            Doc::LineSuffix("  // c".into()),
            Doc::Line,
            text("b)"),
        ]));
        assert_eq!(layout(&doc, 80), "f(a,  // c\nb)\n");
    }

    #[test]
    fn blank_lines_merge_and_lines_carry_no_trailing_spaces() {
        let doc = concat([
            text("a"),
            indent(concat([
                Doc::BlankLine,
                Doc::BlankLine,
                Doc::HardLine,
                text("b"),
            ])),
            Doc::FreshLine,
            Doc::FreshLine,
            text("c"),
        ]);
        assert_eq!(layout(&doc, 80), "a\n\n  b\nc\n");
    }
}
