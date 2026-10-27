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

//! The formatter (Implementation Plan §11.8.3): every Crag file in one
//! canonical layout (Specification §20.9).
//!
//! `format` builds a document from the syntax tree and lays it out in 100
//! columns. Before it returns, it parses its own output and compares the
//! trees: a file comes back only if it means what it meant, with every
//! comment kept.

mod comments;
mod doc;
mod print;

use crag_syntax::{
    LeafKind, ParseError, SyntaxElement, SyntaxKind, SyntaxNode, TokenKind, TriviaKind,
};

pub use doc::{Doc, layout};
use print::Separator;

/// The line length threshold.
pub const WIDTH: usize = 100;

#[derive(Debug, PartialEq, Eq)]
pub enum FormatError {
    /// The file does not parse; it is formatted only once it does.
    Syntax(Vec<ParseError>),
    /// The layout would have changed the file's meaning or lost a
    /// comment, which is a bug in the formatter. The file is left alone.
    Changed,
}

/// Formats a source file of the package named `package`, whose own modules
/// form the last group of imports; outside a project there is none.
pub fn format(text: &str, package: Option<&str>) -> Result<String, FormatError> {
    format_to(text, package, WIDTH)
}

/// `format` for another line length, which tests use to break everything.
#[doc(hidden)]
pub fn format_to(text: &str, package: Option<&str>, width: usize) -> Result<String, FormatError> {
    let root = parse(text)?;
    let out = print_module(&root, package, width);
    let formatted = parse(&out).map_err(|_| FormatError::Changed)?;
    if shape(&root) != shape(&formatted) || comments(&root) != comments(&formatted) {
        return Err(FormatError::Changed);
    }
    Ok(out)
}

/// The layout without the check, for looking into a refusal.
#[doc(hidden)]
pub fn unchecked(text: &str, package: Option<&str>) -> Result<String, FormatError> {
    Ok(print_module(&parse(text)?, package, WIDTH))
}

/// The shape `format` compares, for looking into a refusal.
#[doc(hidden)]
pub fn shape_of(text: &str) -> Result<String, FormatError> {
    Ok(shape(&parse(text)?))
}

/// Lays out each declaration on its own, since all of them start in the
/// first column, which tells which take a single line.
fn print_module(root: &SyntaxNode, package: Option<&str>, width: usize) -> String {
    let mut out = String::new();
    let mut one_line = false;
    for chunk in print::Printer::new(root, package).module(root) {
        let comments = layout(&chunk.comments, width);
        let decl = layout(&chunk.decl, width);
        if comments.is_empty() && decl.is_empty() {
            continue;
        }
        let single = decl.matches('\n').count() == 1;
        if !out.is_empty() {
            let blank = match chunk.separator {
                Separator::Line => false,
                Separator::Blank => true,
                Separator::OneLiners => !(one_line && single),
            };
            if blank {
                out.push('\n');
            }
        }
        out.push_str(&comments);
        if chunk.spaced && !comments.is_empty() && !decl.is_empty() {
            out.push('\n');
        }
        out.push_str(&decl);
        one_line = single;
    }
    out
}

fn parse(text: &str) -> Result<SyntaxNode, FormatError> {
    let tokens = crag_syntax::lex(text);
    let (green, errors) = crag_syntax::parse(text, &tokens);
    if errors.is_empty() {
        Ok(SyntaxNode::new_root(green))
    } else {
        Err(FormatError::Syntax(errors))
    }
}

/// The tree without what layout decides: trivia, newlines ending
/// statements, commas, parentheses around an expression and the order of
/// imports.
fn shape(node: &SyntaxNode) -> String {
    let mut out = String::new();
    write_shape(node, &mut out);
    out
}

fn write_shape(node: &SyntaxNode, out: &mut String) {
    if node.kind() == SyntaxKind::ParenExpr
        && let Some(inner) = node
            .children()
            .next()
            .and_then(|list| list.children().next())
    {
        return write_shape(&inner, out);
    }
    out.push_str(&format!("({:?}", node.kind()));
    let mut sorted = Vec::new();
    for child in node.children_with_tokens() {
        match child {
            SyntaxElement::Node(child) => {
                let sort = match node.kind() {
                    SyntaxKind::Module => child.kind() == SyntaxKind::Import,
                    SyntaxKind::ImportItems => true,
                    _ => false,
                };
                if sort {
                    sorted.push(shape(&child));
                } else {
                    write_shape(&child, out);
                }
            }
            SyntaxElement::Token(token) => match token.kind() {
                LeafKind::Token(TokenKind::Newline | TokenKind::Comma | TokenKind::Eof)
                | LeafKind::Trivia(_) => {}
                LeafKind::Token(_) => {
                    out.push(' ');
                    out.push_str(token.text());
                }
            },
        }
    }
    sorted.sort();
    for child in sorted {
        out.push_str(&child);
    }
    out.push(')');
}

/// The comments of a file, in order.
fn comments(root: &SyntaxNode) -> Vec<String> {
    let mut comments: Vec<String> = root
        .descendant_tokens()
        .filter(|t| {
            matches!(
                t.kind(),
                LeafKind::Trivia(TriviaKind::LineComment | TriviaKind::BlockComment)
            )
        })
        .map(|t| t.text().to_string())
        .collect();
    // Imports move, and their comments with them.
    comments.sort();
    comments
}
