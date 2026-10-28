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

//! The rules that turn a syntax tree into a document, one per kind of
//! node (Specification §20.9). A kind without a rule of its own prints its
//! tokens with the spacing of `space`.
//!
//! A line break goes only where the lexer reads a newline as whitespace:
//! inside brackets, after an operator, `,` or `->`, before `.` and between
//! the items of braces. So a document can break at any of its lines and
//! still parse to the same tree.

use crag_syntax::{
    LeafKind, SyntaxElement, SyntaxKind as S, SyntaxNode, SyntaxToken, TokenKind as T,
};

use crate::comments::Comments;
use crate::doc::{Doc, concat, flat, group, if_break, indent, text};

/// Where a node stands.
#[derive(Clone, Copy, Default)]
struct Cx {
    /// Inside brackets, where newlines are whitespace.
    brackets: bool,
}

const IN_BRACKETS: Cx = Cx { brackets: true };
const IN_BRACES: Cx = Cx { brackets: false };

pub(crate) struct Printer<'a> {
    comments: Comments,
    /// The first comment not printed yet.
    next: usize,
    /// The package whose modules are the file's own.
    package: Option<&'a str>,
}

fn kind(token: &SyntaxToken) -> Option<T> {
    match token.kind() {
        LeafKind::Token(kind) => Some(kind),
        LeafKind::Trivia(_) => None,
    }
}

/// Whether the element is printed: trivia and statement-ending newlines
/// are the printer's own business.
fn printed(element: &SyntaxElement) -> bool {
    match element {
        SyntaxElement::Node(_) => true,
        SyntaxElement::Token(token) => !matches!(kind(token), None | Some(T::Newline | T::Eof)),
    }
}

fn elements(node: &SyntaxNode) -> Vec<SyntaxElement> {
    node.children_with_tokens().filter(printed).collect()
}

fn tokens(node: &SyntaxNode) -> impl Iterator<Item = SyntaxToken> + use<> {
    node.descendant_tokens()
        .filter(|t| !matches!(kind(t), None | Some(T::Newline | T::Eof)))
}

fn first_kind(element: &SyntaxElement) -> Option<T> {
    match element {
        SyntaxElement::Token(token) => kind(token),
        SyntaxElement::Node(node) => tokens(node).next().and_then(|t| kind(&t)),
    }
}

fn last_kind(element: &SyntaxElement) -> Option<T> {
    match element {
        SyntaxElement::Token(token) => kind(token),
        SyntaxElement::Node(node) => tokens(node).last().and_then(|t| kind(&t)),
    }
}

fn token_of(node: &SyntaxNode, wanted: T) -> Option<SyntaxToken> {
    node.tokens().find(|t| kind(t) == Some(wanted))
}

/// Whether a token ends something that can be called or indexed, so that a
/// bracket right after it applies to it.
fn ends_operand(kind: T) -> bool {
    matches!(
        kind,
        T::Ident | T::RParen | T::RBracket | T::RBrace | T::Str | T::StrEnd | T::Underscore
    )
}

/// Whether a space goes between two tokens.
fn space(prev: T, next: T, parent: S) -> bool {
    use T::*;
    match (prev, next) {
        (Comma | Semicolon, _) => true,
        (_, Comma | Semicolon | RParen | RBracket | Colon | Dot | QuestionDot) => false,
        (LParen | LBracket | Dot | QuestionDot | DotDot, _) => false,
        (_, DotDot) => !matches!(parent, S::RangeExpr | S::RangePat),
        (StrStart | TripleStrStart | StrMid, _) | (_, StrMid | StrEnd) => false,
        (_, LParen | LBracket) => !ends_operand(prev),
        (Symbol, Symbol) => false,
        (Minus, _) => !matches!(
            parent,
            S::PrefixExpr | S::LiteralPat | S::RangePat | S::Literal
        ),
        _ => true,
    }
}

/// The group of an import: `std`, a package, or the project's own module.
fn import_group(path: &str, package: Option<&str>) -> u8 {
    let first = path.split('.').next().unwrap_or("");
    if first == "std" {
        0
    } else if Some(first) == package {
        2
    } else {
        1
    }
}

/// An import without layout, which is what imports are sorted by.
fn import_key(node: &SyntaxNode) -> String {
    tokens(node)
        .map(|t| t.text().to_string())
        .collect::<Vec<_>>()
        .join(" ")
}

impl<'a> Printer<'a> {
    pub fn new(root: &SyntaxNode, package: Option<&'a str>) -> Printer<'a> {
        Printer {
            comments: Comments::collect(root),
            next: 0,
            package,
        }
    }

    fn has_comments_before(&self, pos: u32) -> bool {
        self.comments
            .list
            .get(self.next)
            .is_some_and(|c| c.start < pos)
    }

    fn has_comments_within(&self, node: &SyntaxNode) -> bool {
        self.has_comments_in(node.range())
    }

    fn has_comments_in(&self, range: std::ops::Range<u32>) -> bool {
        self.comments.list[self.next..]
            .iter()
            .any(|c| range.start <= c.start && c.start < range.end)
    }

    fn blank_before(&self, node: &SyntaxNode) -> bool {
        tokens(node)
            .next()
            .is_some_and(|t| self.comments.blank_before.contains(&t.range().start))
    }

    /// The comments before `pos`. The first may keep an empty line before it
    /// only where `blank` allows.
    fn leading(&mut self, pos: u32, mut blank: bool) -> Doc {
        let mut docs = Vec::new();
        while let Some(c) = self.comments.list.get(self.next).filter(|c| c.start < pos) {
            if c.own_line {
                docs.push(if c.blank_before && blank {
                    Doc::BlankLine
                } else {
                    Doc::FreshLine
                });
                docs.push(text(c.text.as_str()));
                docs.push(if c.line || c.newline_after {
                    Doc::HardLine
                } else {
                    text(" ")
                });
            } else if c.line {
                docs.push(Doc::LineSuffix(format!("  {}", c.text).into()));
            } else {
                docs.push(text(format!(" {} ", c.text)));
            }
            blank = true;
            self.next += 1;
        }
        concat(docs)
    }

    /// The comments on the rest of the line after a token ending at `end`.
    fn trailing(&mut self, end: u32) -> Doc {
        let mut docs = Vec::new();
        while let Some(c) = self
            .comments
            .list
            .get(self.next)
            .filter(|c| !c.own_line && c.after == end)
        {
            if c.line {
                docs.push(Doc::LineSuffix(format!("  {}", c.text).into()));
            } else if c.newline_after {
                docs.push(text(format!(" {}", c.text)));
                docs.push(Doc::HardLine);
            } else {
                docs.push(text(format!(" {}", c.text)));
            }
            self.next += 1;
        }
        concat(docs)
    }

    fn token(&mut self, token: &SyntaxToken) -> Doc {
        let leading = self.leading(token.range().start, true);
        let trailing = self.trailing(token.range().end);
        concat([leading, text(token.text()), trailing])
    }

    fn element(&mut self, element: &SyntaxElement, cx: Cx) -> Doc {
        match element {
            SyntaxElement::Token(token) => self.token(token),
            SyntaxElement::Node(node) => self.node(node, cx),
        }
    }

    /// The elements in a row, spaced by `space`.
    fn row(&mut self, parent: S, elements: &[SyntaxElement], cx: Cx) -> Doc {
        let mut docs = Vec::new();
        let mut prev: Option<T> = None;
        for element in elements {
            if let (Some(p), Some(n)) = (prev, first_kind(element))
                && space(p, n, parent)
            {
                docs.push(text(" "));
            }
            docs.push(self.element(element, cx));
            prev = last_kind(element).or(prev);
        }
        concat(docs)
    }

    fn generic(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        let elements = elements(node);
        self.row(node.kind(), &elements, cx)
    }

    /// The whole file, one chunk per declaration with the comments before
    /// it; the last chunk holds the comments at the end.
    pub fn module(&mut self, node: &SyntaxNode) -> Vec<Chunk> {
        let decls: Vec<SyntaxNode> = node.children().collect();
        let mut chunks = Vec::new();
        let mut i = 0;
        let mut previous: Option<u8> = None;
        while i < decls.len() {
            let mut end = i + 1;
            if decls[i].kind() == S::Import {
                while end < decls.len() && decls[end].kind() == S::Import {
                    end += 1;
                }
            }
            let mut run = decls[i..end].to_vec();
            let span = run[0].range().start..run[run.len() - 1].range().end;
            if run.len() > 1 && !self.has_comments_in(span) {
                run.sort_by_key(|d| (self.import_group(d), import_key(d)));
            }
            for decl in &run {
                let group = (decl.kind() == S::Import).then(|| self.import_group(decl));
                let start = decl.range().start;
                let commented = self.has_comments_before(start);
                let blank = match self.comments.list.get(self.next) {
                    Some(c) if commented => c.blank_before,
                    _ => self.blank_before(decl),
                };
                let separator = if group.is_some() && group == previous {
                    Separator::Line
                } else if group.is_some() || previous.is_some() || blank {
                    Separator::Blank
                } else {
                    Separator::OneLiners
                };
                let comments = self.leading(start, false);
                let spaced = commented && self.blank_before(decl);
                let decl = self.node(decl, IN_BRACES);
                chunks.push(Chunk {
                    separator,
                    comments,
                    spaced,
                    decl,
                });
                previous = group;
            }
            i = end;
        }
        let comments = self.leading(u32::MAX, false);
        chunks.push(Chunk {
            separator: Separator::Blank,
            comments,
            spaced: false,
            decl: Doc::Nil,
        });
        chunks
    }

    fn import_group(&self, node: &SyntaxNode) -> u8 {
        let path = node.children().find(|c| c.kind() == S::Path);
        import_group(&path.map(|p| p.text()).unwrap_or_default(), self.package)
    }

    fn node(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        match node.kind() {
            S::Block => self.block(node),
            S::Closure => self.closure(node),
            S::IfExpr => group(self.if_chain(node)),
            S::CaseExpr => self.case(node),
            S::CaseArm => self.arm(node),
            S::BinExpr => self.binary(node, cx),
            S::CallExpr | S::FieldExpr | S::BracketExpr => self.postfix(node, cx),
            S::ParenExpr => {
                let list = node.children().next();
                match list {
                    Some(list) => self.generic(&list, IN_BRACKETS),
                    None => self.generic(node, cx),
                }
            }
            S::RecordExpr => match node.children().next() {
                Some(list) => {
                    let single = {
                        let items: Vec<_> = list.children().collect();
                        items.len() == 1 && !matches!(items[0].kind(), S::LabeledArg | S::SpreadArg)
                    };
                    self.list(&list, Spacing::Tight, single)
                }
                None => self.generic(node, cx),
            },
            S::ArgList
            | S::ListExpr
            | S::MapExpr
            | S::FieldList
            | S::ParamList
            | S::TypeParams
            | S::TypeArgs
            | S::FnTypeParams
            | S::RecordType
            | S::ListPat
            | S::ImportItems => self.list(node, Spacing::Tight, false),
            S::RecordPat => self.list(node, Spacing::Tight, false),
            S::GridExpr => self.grid(node),
            S::CImport => self.list(node, Spacing::Spaced, false),
            S::WhereClause | S::IsClause => self.braced_items(node),
            S::FormDecl => self.braced_lines(node),
            S::TypeDecl => self.type_decl(node, cx),
            S::FnDecl => self.fn_decl(node, cx),
            S::LetDecl => self.let_decl(node, cx),
            S::PrefixExpr => self.prefix(node, cx),
            S::StrExpr => flat(self.generic(node, IN_BRACKETS)),
            _ => self.generic(node, cx),
        }
    }

    /// A comma-separated list in brackets, which breaks into one item per
    /// line with a comma after each. The tokens before the opening bracket
    /// and after the closing one stay in a row; `keep_comma` keeps the comma
    /// after a single item, which a one-field record needs.
    fn list(&mut self, node: &SyntaxNode, spacing: Spacing, keep_comma: bool) -> Doc {
        let elements = elements(node);
        let opener = if node.kind() == S::CImport {
            T::LBrace
        } else {
            match elements.iter().find_map(|e| match e {
                SyntaxElement::Token(t) => {
                    kind(t).filter(|k| matches!(k, T::LParen | T::LBracket | T::LBrace))
                }
                SyntaxElement::Node(_) => None,
            }) {
                Some(opener) => opener,
                None => return self.generic(node, IN_BRACKETS),
            }
        };
        let closer = match opener {
            T::LParen => T::RParen,
            T::LBracket => T::RBracket,
            _ => T::RBrace,
        };
        let is = |e: &SyntaxElement, wanted: T| matches!(e, SyntaxElement::Token(t) if kind(t) == Some(wanted));
        let open = elements.iter().position(|e| is(e, opener));
        let close = elements.iter().rposition(|e| is(e, closer));
        let (Some(open), Some(close)) = (open, close) else {
            return self.generic(node, IN_BRACKETS);
        };
        let inner = &elements[open + 1..close];
        // Anything but items and commas, like the `:` of `[:]`, is a row.
        if close < open
            || inner
                .iter()
                .any(|e| matches!(e, SyntaxElement::Token(_)) && !is(e, T::Comma))
        {
            return self.generic(node, IN_BRACKETS);
        }
        let before = self.row(node.kind(), &elements[..open], IN_BRACKETS);
        let space_before = open > 0
            && first_kind(&elements[open])
                .zip(last_kind(&elements[open - 1]))
                .is_some_and(|(o, p)| space(p, o, node.kind()));
        let open_doc = self.element(&elements[open], IN_BRACKETS);
        let items: Vec<&SyntaxElement> = inner
            .iter()
            .filter(|e| matches!(e, SyntaxElement::Node(_)))
            .collect();
        let commas: Vec<SyntaxToken> = inner
            .iter()
            .filter_map(|e| match e {
                SyntaxElement::Token(t) if kind(t) == Some(T::Comma) => Some(t.clone()),
                _ => None,
            })
            .collect();
        let SyntaxElement::Token(close_token) = &elements[close] else {
            unreachable!()
        };
        let line = match spacing {
            Spacing::Tight => Doc::SoftLine,
            Spacing::Spaced => Doc::Line,
        };
        let mut body = Vec::new();
        let sort = node.kind() == S::ImportItems && !self.has_comments_within(node);
        let mut items: Vec<&SyntaxElement> = items;
        if sort {
            items.sort_by_key(|e| match e {
                SyntaxElement::Node(n) => import_key(n),
                SyntaxElement::Token(t) => t.text().to_string(),
            });
        }
        let count = items.len();
        for (i, item) in items.iter().enumerate() {
            if i > 0 {
                body.push(Doc::Line);
            }
            body.push(self.element(item, IN_BRACKETS));
            // The comma's own comments come with it; sorted items lose
            // nothing, since sorting needs a list without comments.
            let comma = commas
                .iter()
                .find(|c| c.range().start >= item_end(item) && !sort)
                .cloned();
            if i + 1 < count {
                match comma {
                    Some(comma) => body.push(self.token(&comma)),
                    None => body.push(text(",")),
                }
            } else {
                if let Some(comma) = comma {
                    // Its comments only.
                    let leading = self.leading(comma.range().start, true);
                    let trailing = self.trailing(comma.range().end);
                    body.push(if keep_comma {
                        text(",")
                    } else {
                        if_break(text(","), Doc::Nil)
                    });
                    body.push(leading);
                    body.push(trailing);
                } else {
                    body.push(if keep_comma {
                        text(",")
                    } else {
                        if_break(text(","), Doc::Nil)
                    });
                }
            }
        }
        let close_comments = self.leading(close_token.range().start, true);
        let close_doc = self.token(close_token);
        let after = self.row(node.kind(), &elements[close + 1..], IN_BRACKETS);
        let space_after = elements.get(close + 1).is_some_and(|e| {
            first_kind(e)
                .is_some_and(|n| space(kind(close_token).unwrap_or(T::RParen), n, node.kind()))
        });
        let list = if count == 0 {
            concat([open_doc, close_comments, close_doc])
        } else {
            group(concat([
                open_doc,
                indent(concat([line.clone(), concat(body), close_comments])),
                line,
                close_doc,
            ]))
        };
        concat([
            before,
            if space_before { text(" ") } else { Doc::Nil },
            list,
            if space_after { text(" ") } else { Doc::Nil },
            after,
        ])
    }

    /// `[a, b; c, d]`: rows separated by `;`.
    fn grid(&mut self, node: &SyntaxNode) -> Doc {
        let elements = elements(node);
        let mut docs = Vec::new();
        let mut body = Vec::new();
        let mut close = Doc::Nil;
        let last = elements.len().saturating_sub(1);
        for (i, element) in elements.iter().enumerate() {
            match element {
                SyntaxElement::Token(t) if i == 0 => docs.push(self.token(t)),
                SyntaxElement::Token(t) if i == last && kind(t) == Some(T::RBracket) => {
                    let comments = self.leading(t.range().start, true);
                    body.push(comments);
                    close = self.token(t);
                }
                SyntaxElement::Token(t) if kind(t) == Some(T::Semicolon) => {
                    body.push(self.token(t));
                    body.push(Doc::Line);
                }
                _ => body.push(self.element(element, IN_BRACKETS)),
            }
        }
        group(concat([
            concat(docs),
            indent(concat([Doc::SoftLine, concat(body)])),
            Doc::SoftLine,
            close,
        ]))
    }

    /// `is { A, B }` and `where { a, b }`: items in braces, separated by
    /// commas on one line and by line breaks when broken. Without braces
    /// the clause is a row.
    fn braced_items(&mut self, node: &SyntaxNode) -> Doc {
        let elements = elements(node);
        let Some(open) = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Token(t) if kind(t) == Some(T::LBrace)))
        else {
            return self.generic(node, IN_BRACES);
        };
        let keyword = self.row(node.kind(), &elements[..open], IN_BRACES);
        let open_doc = self.element(&elements[open], IN_BRACES);
        let mut body = Vec::new();
        let mut close = Doc::Nil;
        let mut close_comments = Doc::Nil;
        let mut count = 0;
        for element in &elements[open + 1..] {
            match element {
                SyntaxElement::Node(item) => {
                    if count > 0 {
                        body.push(if_break(Doc::Nil, text(",")));
                        body.push(Doc::Line);
                    }
                    body.push(self.node(item, IN_BRACES));
                    count += 1;
                }
                SyntaxElement::Token(t) if kind(t) == Some(T::Comma) => {
                    // Separators are the layout's; keep the comments.
                    let leading = self.leading(t.range().start, true);
                    let trailing = self.trailing(t.range().end);
                    body.push(leading);
                    body.push(trailing);
                }
                SyntaxElement::Token(t) => {
                    close_comments = self.leading(t.range().start, true);
                    close = self.token(t);
                }
            }
        }
        concat([
            keyword,
            text(" "),
            group(concat([
                open_doc,
                indent(concat([Doc::Line, concat(body), close_comments])),
                Doc::Line,
                close,
            ])),
        ])
    }

    /// `form F { fn… }`: the items one per line.
    fn braced_lines(&mut self, node: &SyntaxNode) -> Doc {
        let elements = elements(node);
        let Some(open) = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Token(t) if kind(t) == Some(T::LBrace)))
        else {
            return self.generic(node, IN_BRACES);
        };
        let head = self.row(node.kind(), &elements[..open], IN_BRACES);
        let items: Vec<SyntaxNode> = elements[open + 1..]
            .iter()
            .filter_map(|e| match e {
                SyntaxElement::Node(n) => Some(n.clone()),
                _ => None,
            })
            .collect();
        let SyntaxElement::Token(open_token) = &elements[open] else {
            unreachable!()
        };
        let close = elements[open + 1..].iter().rev().find_map(|e| match e {
            SyntaxElement::Token(t) if kind(t) == Some(T::RBrace) => Some(t.clone()),
            _ => None,
        });
        // Commas between the items go; their comments stay.
        concat([
            head,
            text(" "),
            self.lines(open_token, &items, close.as_ref(), false),
        ])
    }

    /// Items between braces, one per line: statements, case arms, form
    /// functions. `flat` lets a single item stay on the line of the braces
    /// when it fits.
    fn lines(
        &mut self,
        open: &SyntaxToken,
        items: &[SyntaxNode],
        close: Option<&SyntaxToken>,
        flat: bool,
    ) -> Doc {
        let open_doc = self.token(open);
        let close_pos = close.map_or(u32::MAX, |c| c.range().start);
        if items.is_empty() && !self.has_comments_before(close_pos) {
            let close_doc = close.map_or(Doc::Nil, |c| self.token(c));
            return concat([open_doc, close_doc]);
        }
        let mut body = Vec::new();
        for (i, item) in items.iter().enumerate() {
            let start = item.range().start;
            let commented = self.has_comments_before(start);
            if i == 0 {
                body.push(if flat && items.len() == 1 {
                    Doc::Line
                } else {
                    Doc::HardLine
                });
            } else if self.blank_before(item) && !commented {
                body.push(Doc::BlankLine);
            } else {
                body.push(Doc::HardLine);
            }
            body.push(self.leading(start, i > 0));
            if commented && i > 0 && self.blank_before(item) {
                body.push(Doc::BlankLine);
            }
            body.push(self.node(item, IN_BRACES));
            // Separating commas and semicolons are dropped; their comments
            // come with the next item.
        }
        body.push(self.leading(close_pos, true));
        let close_doc = close.map_or(Doc::Nil, |c| self.token(c));
        let line = if flat && items.len() == 1 {
            Doc::Line
        } else {
            Doc::HardLine
        };
        group(concat([open_doc, indent(concat(body)), line, close_doc]))
    }

    fn block(&mut self, node: &SyntaxNode) -> Doc {
        let open = token_of(node, T::LBrace);
        let close = token_of(node, T::RBrace);
        let statements: Vec<SyntaxNode> = node.children().collect();
        // A block inside a one-line block would be hard to read.
        let flat = !statements.iter().any(|s| {
            s.descendants()
                .any(|d| matches!(d.kind(), S::Block | S::CaseExpr))
        });
        match open {
            Some(open) => self.lines(&open, &statements, close.as_ref(), flat),
            None => self.generic(node, IN_BRACES),
        }
    }

    /// `{ params -> statements }`, on one line when it holds a single
    /// statement and fits.
    fn closure(&mut self, node: &SyntaxNode) -> Doc {
        let elements = elements(node);
        let Some(arrow) = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Token(t) if kind(t) == Some(T::Arrow)))
        else {
            return self.generic(node, IN_BRACES);
        };
        let mut head = vec![self.element(&elements[0], IN_BRACES)];
        for element in &elements[1..arrow] {
            head.push(text(" "));
            head.push(self.element(element, IN_BRACES));
        }
        head.push(text(" "));
        head.push(self.element(&elements[arrow], IN_BRACES));
        let statements: Vec<SyntaxNode> = elements[arrow + 1..]
            .iter()
            .filter_map(|e| match e {
                SyntaxElement::Node(n) => Some(n.clone()),
                _ => None,
            })
            .collect();
        let close = elements.last().and_then(|e| match e {
            SyntaxElement::Token(t) if kind(t) == Some(T::RBrace) => Some(t.clone()),
            _ => None,
        });
        let close_pos = close.as_ref().map_or(u32::MAX, |c| c.range().start);
        let single = statements.len() <= 1;
        let mut body = Vec::new();
        for (i, statement) in statements.iter().enumerate() {
            let start = statement.range().start;
            let commented = self.has_comments_before(start);
            if i == 0 {
                body.push(if single { Doc::Line } else { Doc::HardLine });
            } else if self.blank_before(statement) && !commented {
                body.push(Doc::BlankLine);
            } else {
                body.push(Doc::HardLine);
            }
            body.push(self.leading(start, i > 0));
            if commented && i > 0 && self.blank_before(statement) {
                body.push(Doc::BlankLine);
            }
            body.push(self.node(statement, IN_BRACES));
        }
        body.push(self.leading(close_pos, true));
        let close_doc = close.map_or(Doc::Nil, |c| self.token(&c));
        group(concat([
            concat(head),
            indent(concat(body)),
            if single { Doc::Line } else { Doc::HardLine },
            close_doc,
        ]))
    }

    /// `if … { } else if … { } else { }` as one group, so either every block
    /// stays on its line or all of them break.
    fn if_chain(&mut self, node: &SyntaxNode) -> Doc {
        let mut docs = Vec::new();
        let mut prev: Option<T> = None;
        for element in elements(node) {
            if let Some(p) = prev {
                docs.push(
                    if space(p, first_kind(&element).unwrap_or(T::Ident), S::IfExpr) {
                        text(" ")
                    } else {
                        Doc::Nil
                    },
                );
            }
            prev = last_kind(&element);
            docs.push(match &element {
                SyntaxElement::Node(n) if n.kind() == S::IfExpr => self.if_chain(n),
                SyntaxElement::Node(n) if n.kind() == S::Block => {
                    let open = token_of(n, T::LBrace);
                    let close = token_of(n, T::RBrace);
                    let statements: Vec<SyntaxNode> = n.children().collect();
                    match open {
                        Some(open) => self.block_lines(&open, &statements, close.as_ref()),
                        None => self.generic(n, IN_BRACES),
                    }
                }
                _ => self.element(&element, IN_BRACES),
            });
        }
        concat(docs)
    }

    /// A block's lines without a group of their own, for the group of an
    /// `if` chain.
    fn block_lines(
        &mut self,
        open: &SyntaxToken,
        items: &[SyntaxNode],
        close: Option<&SyntaxToken>,
    ) -> Doc {
        let flat = !items.iter().any(|s| {
            s.descendants()
                .any(|d| matches!(d.kind(), S::Block | S::CaseExpr))
        });
        match self.lines(open, items, close, flat) {
            Doc::Group(doc, _) => *doc,
            doc => doc,
        }
    }

    /// `case subject { arms }`, one arm per line.
    fn case(&mut self, node: &SyntaxNode) -> Doc {
        let elements = elements(node);
        let Some(open) = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Token(t) if kind(t) == Some(T::LBrace)))
        else {
            return self.generic(node, IN_BRACES);
        };
        let head = self.row(S::CaseExpr, &elements[..open], IN_BRACES);
        let SyntaxElement::Token(open_token) = &elements[open] else {
            unreachable!()
        };
        let arms: Vec<SyntaxNode> = elements[open + 1..]
            .iter()
            .filter_map(|e| match e {
                SyntaxElement::Node(n) => Some(n.clone()),
                _ => None,
            })
            .collect();
        let close = elements[open + 1..].iter().rev().find_map(|e| match e {
            SyntaxElement::Token(t) if kind(t) == Some(T::RBrace) => Some(t.clone()),
            _ => None,
        });
        concat([
            head,
            text(" "),
            self.lines(open_token, &arms, close.as_ref(), false),
        ])
    }

    /// `pattern -> body`, broken after `->` when it does not fit.
    fn arm(&mut self, node: &SyntaxNode) -> Doc {
        let elements = elements(node);
        let Some(arrow) = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Token(t) if kind(t) == Some(T::Arrow)))
        else {
            return self.generic(node, IN_BRACES);
        };
        let head = self.row(S::CaseArm, &elements[..=arrow], IN_BRACES);
        let body = self.row(S::CaseArm, &elements[arrow + 1..], IN_BRACES);
        let braced = matches!(elements.get(arrow + 1), Some(SyntaxElement::Node(n)) if matches!(n.kind(), S::Block | S::Closure | S::CaseExpr));
        if braced {
            concat([head, text(" "), body])
        } else {
            group(concat([head, indent(concat([Doc::Line, body]))]))
        }
    }

    /// A chain of operators of one precedence, broken before each operator
    /// in parentheses, which it adds unless newlines are whitespace already.
    fn binary(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        let power = |n: &SyntaxNode| {
            n.tokens()
                .find_map(|t| kind(&t).filter(|k| k.continues_line()))
                .map(binding_power)
        };
        let level = power(node);
        let mut operands = Vec::new();
        let mut current = node.clone();
        while current.kind() == S::BinExpr && power(&current) == level {
            let elements = elements(&current);
            let [left, op, right] = elements.as_slice() else {
                return self.generic(node, cx);
            };
            let (SyntaxElement::Node(left), SyntaxElement::Token(op)) = (left, op) else {
                return self.generic(node, cx);
            };
            operands.push((Some(op.clone()), right.clone()));
            current = left.clone();
        }
        let first = self.node(&current, IN_BRACKETS);
        let mut rest = Vec::new();
        for (op, operand) in operands.into_iter().rev() {
            rest.push(Doc::Line);
            if let Some(op) = op {
                rest.push(self.token(&op));
            }
            rest.push(text(" "));
            rest.push(self.element(&operand, IN_BRACKETS));
        }
        let inner = concat([first, indent(concat(rest))]);
        if cx.brackets {
            group(inner)
        } else {
            group(concat([
                if_break(text("("), Doc::Nil),
                inner,
                if_break(text(")"), Doc::Nil),
            ]))
        }
    }

    /// Calls, field accesses and indexing. A chain of two or more calls
    /// after its base breaks before each `.`.
    fn postfix(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        // The links from the base outward.
        let mut links = Vec::new();
        let mut current = node.clone();
        while matches!(current.kind(), S::CallExpr | S::FieldExpr | S::BracketExpr) {
            let Some(callee) = current.children().next() else {
                break;
            };
            links.push(current.clone());
            current = callee;
        }
        links.reverse();
        let base = current;
        // Segments: the base with its leading fields, then one per `.call`,
        // with the fields after it.
        let mut segments: Vec<Vec<SyntaxNode>> = vec![Vec::new()];
        let mut called = false;
        for (i, link) in links.iter().enumerate() {
            let calls_next = links.get(i + 1).is_some_and(|l| l.kind() != S::FieldExpr);
            if link.kind() == S::FieldExpr && (called || calls_next) {
                segments.push(Vec::new());
                called = false;
            }
            if link.kind() != S::FieldExpr {
                called = true;
            }
            segments.last_mut().unwrap().push(link.clone());
        }
        let chain = segments.len() > 2;
        let mut docs = vec![self.node(&base, cx)];
        let mut tail = Vec::new();
        for (i, segment) in segments.iter().enumerate() {
            let mut seg = Vec::new();
            for link in segment {
                seg.push(self.link(link));
            }
            if chain && i > 0 {
                tail.push(Doc::SoftLine);
                tail.push(concat(seg));
            } else {
                docs.push(concat(seg));
            }
        }
        if chain {
            group(concat([concat(docs), indent(concat(tail))]))
        } else {
            concat(docs)
        }
    }

    /// What a postfix node adds to its callee.
    fn link(&mut self, node: &SyntaxNode) -> Doc {
        let elements: Vec<SyntaxElement> = elements(node).into_iter().skip(1).collect();
        let mut docs = Vec::new();
        for element in &elements {
            match element {
                SyntaxElement::Node(n) if n.kind() == S::Closure => {
                    docs.push(text(" "));
                    docs.push(self.closure(n));
                }
                _ => docs.push(self.element(element, IN_BRACKETS)),
            }
        }
        concat(docs)
    }

    fn type_decl(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        let elements = elements(node);
        let clause = |e: &SyntaxElement| matches!(e, SyntaxElement::Node(n) if matches!(n.kind(), S::WhereClause | S::IsClause | S::OnClause));
        let split = elements.iter().position(clause).unwrap_or(elements.len());
        let head = self.row(S::TypeDecl, &elements[..split], cx);
        if split == elements.len() {
            return head;
        }
        let mut clauses = Vec::new();
        for element in &elements[split..] {
            clauses.push(Doc::Line);
            clauses.push(self.element(element, IN_BRACES));
        }
        group(concat([head, indent(concat(clauses))]))
    }

    fn fn_decl(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        let elements = elements(node);
        let body = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Node(n) if n.kind() == S::Block));
        let end = body.unwrap_or(elements.len());
        let mut head = Vec::new();
        let mut prev: Option<T> = None;
        for element in &elements[..end] {
            let is_where = matches!(element, SyntaxElement::Node(n) if n.kind() == S::WhereClause);
            if let Some(p) = prev {
                if is_where {
                    head.push(indent(Doc::Line));
                } else if first_kind(element).is_some_and(|n| space(p, n, S::FnDecl)) {
                    head.push(text(" "));
                }
            }
            if is_where {
                head.push(indent(self.element(element, IN_BRACES)));
            } else {
                head.push(self.element(element, cx));
            }
            prev = last_kind(element).or(prev);
        }
        let mut docs = vec![group(concat(head))];
        if let Some(body) = body {
            docs.push(text(" "));
            docs.push(self.element(&elements[body], IN_BRACES));
        }
        concat(docs)
    }

    /// `let pattern = value`, with an `else` part that moves to the next
    /// line when the whole does not fit.
    fn let_decl(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        let elements = elements(node);
        let split = elements
            .iter()
            .position(|e| matches!(e, SyntaxElement::Node(n) if n.kind() == S::LetElse));
        let Some(split) = split else {
            return self.row(S::LetDecl, &elements, cx);
        };
        let head = self.row(S::LetDecl, &elements[..split], cx);
        let rest = self.element(&elements[split], cx);
        concat([head, text(" "), rest])
    }

    /// `-x`, `not x` and prefixes, which a space follows.
    fn prefix(&mut self, node: &SyntaxNode, cx: Cx) -> Doc {
        let elements = elements(node);
        let mut docs = Vec::new();
        let mut prev: Option<T> = None;
        for element in &elements {
            if let (Some(p), Some(n)) = (prev, first_kind(element)) {
                // The symbols of one prefix are adjacent; the next prefix
                // is a node of its own.
                let joined = matches!(element, SyntaxElement::Token(_)) && n == T::Symbol;
                let attached = (p == T::Minus && n != T::Minus) || (p == T::Symbol && joined);
                if !attached {
                    docs.push(text(" "));
                }
            }
            docs.push(self.element(element, cx));
            prev = last_kind(element);
        }
        concat(docs)
    }
}

fn item_end(element: &SyntaxElement) -> u32 {
    element.range().end
}

/// Operators of one level of precedence (§6.2.1).
fn binding_power(kind: T) -> u8 {
    match kind {
        T::Or => 1,
        T::And => 3,
        T::EqEq | T::BangEq | T::Lt | T::LtEq | T::Gt | T::GtEq | T::Is => 7,
        T::DotDot => 9,
        T::Plus | T::Minus | T::PlusPercent | T::MinusPercent => 11,
        T::Star | T::Slash | T::Percent | T::StarPercent => 13,
        _ => 0,
    }
}

/// A declaration of a file and the comments before it.
pub(crate) struct Chunk {
    pub separator: Separator,
    pub comments: Doc,
    /// Whether an empty line separates the comments from the declaration.
    pub spaced: bool,
    pub decl: Doc,
}

/// What goes between a chunk and the one before.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Separator {
    /// A line break: imports of one group.
    Line,
    /// An empty line.
    Blank,
    /// A line break if both declarations take one line, else an empty
    /// line: they stood on consecutive lines.
    OneLiners,
}

#[derive(Clone, Copy)]
enum Spacing {
    /// `(a, b)`: nothing inside the brackets.
    Tight,
    /// `{ a, b }`: a space inside.
    Spaced,
}
