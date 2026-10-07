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

//! The parser's machinery: a cursor over the tokens that builds the green
//! tree as it goes (Implementation Plan §11.4.2). The grammar rules are in
//! `grammar`.
//!
//! The parser never gives up. A missing token is reported and assumed; an
//! unexpected one is wrapped in an `Error` node. Every loop in the grammar
//! consumes a token per round or stops, so parsing always ends.
//!
//! Trivia goes into the tree in front of the token it belongs to. When a
//! node starts, the trivia in front of its first token is added first, to
//! the enclosing node, so a node's range begins at its first token and a
//! comment above a declaration is that declaration's previous sibling.

use std::ops::Range;

use crate::green::{Builder, Checkpoint, GreenElement, GreenNode, NodeCache};
use crate::kind::{LeafKind, SyntaxKind};
use crate::token::{Token, TokenKind};

/// A syntax error: what was wrong, and where.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub range: Range<u32>,
}

/// Parses one source file. `tokens` must be `lex(text)`.
pub fn parse(text: &str, tokens: &[Token]) -> (GreenNode, Vec<ParseError>) {
    let mut p = Parser::new(text, tokens);
    crate::grammar::module(&mut p);
    p.finish()
}

/// Parses `text`, which must be one block `{ … }`, as the parser would at
/// `depth` in a file, for the incremental reparse. `None` if the text does
/// not parse as exactly that block: if it opens a closure instead, if the
/// block ends early or lacks its `}`, or if the nesting limit was reached,
/// which `depth` only bounds from above.
pub(crate) fn parse_block(
    text: &str,
    tokens: &[Token],
    depth: usize,
) -> Option<(GreenNode, Vec<ParseError>)> {
    let mut p = Parser::new(text, tokens);
    p.depth = depth;
    if !p.at(TokenKind::LBrace) || crate::grammar::closure_ahead(&p) {
        return None;
    }
    crate::grammar::block(&mut p);
    if p.too_deep || !p.at(TokenKind::Eof) {
        return None;
    }
    let (module, errors) = p.finish();
    let [GreenElement::Node(block)] = module.children() else {
        return None;
    };
    let closed = matches!(
        block.children().last(),
        Some(GreenElement::Token(t)) if t.kind() == LeafKind::Token(TokenKind::RBrace)
    );
    closed.then(|| (block.clone(), errors))
}

pub(crate) struct Parser<'a> {
    text: &'a str,
    tokens: &'a [Token],
    pos: usize,
    /// Whether the trivia of `tokens[pos]` is in the tree already.
    trivia_added: bool,
    builder: Builder,
    errors: Vec<ParseError>,
    /// The number of open nodes, which bounds the parser's recursion.
    depth: usize,
    /// Whether the nesting limit cut the input short somewhere.
    too_deep: bool,
}

/// How deeply nodes may nest. Deeper input is reported and skipped, so a
/// pathological file cannot overflow the stack.
const MAX_DEPTH: usize = 512;

/// A set of token kinds.
#[derive(Clone, Copy)]
pub(crate) struct TokenSet(u128);

impl TokenSet {
    pub(crate) const fn new(kinds: &[TokenKind]) -> TokenSet {
        let mut bits = 0;
        let mut i = 0;
        while i < kinds.len() {
            bits |= 1 << kinds[i] as u32;
            i += 1;
        }
        TokenSet(bits)
    }

    pub(crate) const fn contains(self, kind: TokenKind) -> bool {
        self.0 & (1 << kind as u32) != 0
    }

    pub(crate) const fn union(self, other: TokenSet) -> TokenSet {
        TokenSet(self.0 | other.0)
    }
}

const _: () = assert!((TokenKind::Eof as u32) < 128, "TokenSet holds 128 kinds");

/// Tokens recovery never skips: they end a statement or close what is open.
const ANCHORS: TokenSet = TokenSet::new(&[
    TokenKind::Newline,
    TokenKind::RBrace,
    TokenKind::RParen,
    TokenKind::RBracket,
    TokenKind::Eof,
]);

impl<'a> Parser<'a> {
    fn new(text: &'a str, tokens: &'a [Token]) -> Parser<'a> {
        assert_eq!(tokens.last().map(|t| t.kind), Some(TokenKind::Eof));
        let mut builder = Builder::new(NodeCache::default());
        builder.start_node(SyntaxKind::Module);
        Parser {
            text,
            tokens,
            pos: 0,
            trivia_added: false,
            builder,
            errors: Vec::new(),
            depth: 0,
            too_deep: false,
        }
    }

    fn finish(mut self) -> (GreenNode, Vec<ParseError>) {
        while !self.at(TokenKind::Eof) {
            self.bump();
        }
        self.add_trivia();
        self.builder.finish_node();
        (self.builder.finish().0, self.errors)
    }

    // Looking at tokens.

    pub(crate) fn nth(&self, n: usize) -> TokenKind {
        self.tokens
            .get(self.pos + n)
            .map_or(TokenKind::Eof, |t| t.kind)
    }

    pub(crate) fn current(&self) -> TokenKind {
        self.nth(0)
    }

    pub(crate) fn at(&self, kind: TokenKind) -> bool {
        self.current() == kind
    }

    pub(crate) fn at_set(&self, set: TokenSet) -> bool {
        set.contains(self.current())
    }

    /// The text of the token `n` ahead.
    pub(crate) fn nth_text(&self, n: usize) -> &'a str {
        self.tokens
            .get(self.pos + n)
            .map_or("", |t| t.text(self.text))
    }

    /// Whether the current token is the identifier `word`, a contextual
    /// keyword.
    pub(crate) fn at_word(&self, word: &str) -> bool {
        self.at(TokenKind::Ident) && self.nth_text(0) == word
    }

    /// Whether token `n` ahead follows token `n - 1` without trivia.
    pub(crate) fn nth_is_joined(&self, n: usize) -> bool {
        let i = self.pos + n;
        i > 0 && i < self.tokens.len() && self.tokens[i].trivia_start == self.tokens[i].start
    }

    /// The kind of the first token at or after `n` ahead that is not a
    /// newline, and its distance.
    pub(crate) fn nth_past_newlines(&self, mut n: usize) -> (TokenKind, usize) {
        while self.nth(n) == TokenKind::Newline {
            n += 1;
        }
        (self.nth(n), n)
    }

    /// From an opening bracket `n` ahead, the distance to the token after
    /// its matching closer.
    pub(crate) fn skip_balanced(&self, mut n: usize) -> usize {
        let mut depth = 0usize;
        loop {
            match self.nth(n) {
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::StrStart | TokenKind::TripleStrStart => depth += 1,
                TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace | TokenKind::StrEnd => {
                    depth = depth.saturating_sub(1)
                }
                TokenKind::Eof => return n,
                _ => {}
            }
            n += 1;
            if depth == 0 {
                return n;
            }
        }
    }

    // Building the tree.

    fn add_trivia(&mut self) {
        if self.trivia_added {
            return;
        }
        self.trivia_added = true;
        let token = self.tokens[self.pos];
        for (kind, range) in token.trivia(self.text) {
            self.builder.leaf(LeafKind::Trivia(kind), &self.text[range]);
        }
    }

    pub(crate) fn bump(&mut self) {
        if self.at(TokenKind::Eof) {
            return;
        }
        self.add_trivia();
        let token = self.tokens[self.pos];
        self.builder
            .leaf(LeafKind::Token(token.kind), token.text(self.text));
        self.pos += 1;
        self.trivia_added = false;
    }

    pub(crate) fn eat(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    /// Consumes `kind`, or reports it missing and goes on as if it were
    /// there.
    pub(crate) fn expect(&mut self, kind: TokenKind, what: &str) -> bool {
        if self.eat(kind) {
            return true;
        }
        self.error(format!("expected {what}"));
        false
    }

    pub(crate) fn eat_newlines(&mut self) {
        while self.eat(TokenKind::Newline) {}
    }

    pub(crate) fn start(&mut self, kind: SyntaxKind) {
        self.add_trivia();
        self.builder.start_node(kind);
        self.depth += 1;
    }

    pub(crate) fn finish_node(&mut self) {
        self.builder.finish_node();
        self.depth -= 1;
    }

    /// A checkpoint in front of the current token, after its trivia.
    pub(crate) fn checkpoint(&mut self) -> Checkpoint {
        self.add_trivia();
        self.builder.checkpoint()
    }

    pub(crate) fn start_at(&mut self, checkpoint: Checkpoint, kind: SyntaxKind) {
        self.builder.start_node_at(checkpoint, kind);
        self.depth += 1;
    }

    /// Runs `rule` one level deeper, for a rule that recurses before it
    /// can start its node.
    pub(crate) fn nested(&mut self, rule: impl FnOnce(&mut Self)) {
        self.depth += 1;
        rule(self);
        self.depth -= 1;
    }

    /// Whether a rule that recurses may start here. Past the nesting limit
    /// it reports an error and skips the current token, a whole bracket if
    /// it opens one, without recursing.
    pub(crate) fn enter(&mut self) -> bool {
        if self.depth < MAX_DEPTH {
            return true;
        }
        self.too_deep = true;
        self.bump_error("nesting too deep");
        false
    }

    // Errors.

    /// Reports an error at the current token.
    pub(crate) fn error(&mut self, message: impl Into<String>) {
        let token = self.tokens[self.pos];
        let range = if token.kind == TokenKind::Newline || token.kind == TokenKind::Eof {
            // Point at the end of the line rather than at the next one.
            token.start..token.start
        } else {
            token.start..token.end
        };
        // One error per position is enough; recovery would repeat it.
        if self.errors.last().is_some_and(|e| e.range == range) {
            return;
        }
        self.errors.push(ParseError {
            message: message.into(),
            range,
        });
    }

    /// Reports an error and wraps tokens in an `Error` node up to the end of
    /// the statement, a closer, or a token in `stop` (§2.3). Brackets
    /// opened on the way are skipped whole. Consumes at least one token
    /// unless at an anchor.
    pub(crate) fn recover(&mut self, message: impl Into<String>, stop: TokenSet) {
        self.error(message);
        let stop = stop.union(ANCHORS);
        if self.at_set(stop) {
            return;
        }
        self.start(SyntaxKind::Error);
        while !self.at_set(stop) {
            self.bump_balanced();
        }
        self.finish_node();
    }

    /// Wraps the current token in an `Error` node, with everything up to the
    /// matching closer if it opens a bracket.
    pub(crate) fn bump_error(&mut self, message: impl Into<String>) {
        self.error(message);
        if self.at(TokenKind::Eof) {
            return;
        }
        self.start(SyntaxKind::Error);
        self.bump_balanced();
        self.finish_node();
    }

    fn bump_balanced(&mut self) {
        let end = self.pos + self.skip_balanced(0);
        while self.pos < end && !self.at(TokenKind::Eof) {
            self.bump();
        }
    }

    /// The position in the token list, to check that a loop made progress.
    pub(crate) fn position(&self) -> usize {
        self.pos
    }
}
