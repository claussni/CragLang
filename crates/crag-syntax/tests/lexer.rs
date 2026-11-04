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

use crag_syntax::TokenKind::*;
use crag_syntax::{TokenKind, TriviaKind, lex};

const PROGRAM: &str = r#"// A point on the drawing canvas.
type Point(x: Int, y: Int)

/* Block comments may span
   several lines. */
pub fn describe(p: Point) -> Str {
  let names = people
    .filter { p -> p.age >= 18 }
    .map { p -> p.name }
  let total = p.x +
    p.y * 2
  -total
  if total > 0 {
    "positive {total} and {f({ x -> "{x}" })}, {{literal}}"
  }
  else {
    """
    SELECT name
    FROM orders
    WHERE id = {orderId}
    """
  }
  let mask: UInt8 = 0b1111_0000
  let r = 1..10
  let c = '\n'
  let b = b"\x00{"
  ~ sendMail(msg)
  let port = !! Int.parse(portText)
  case shape {
    Circle(r:) -> 3.14 * r * r
    _ -> ???
  }
  x?.and.or
}
"#;

fn kinds(text: &str) -> Vec<TokenKind> {
    lex(text).iter().map(|t| t.kind).collect()
}

fn tokens(text: &str) -> Vec<(TokenKind, &str)> {
    lex(text).iter().map(|t| (t.kind, t.text(text))).collect()
}

#[test]
fn every_byte_belongs_to_a_token_or_its_trivia() {
    let tokens = lex(PROGRAM);
    let mut pos = 0;
    for t in &tokens {
        assert_eq!(t.trivia_start, pos);
        assert!(t.trivia_start <= t.start && t.start <= t.end);
        pos = t.end;
    }
    assert_eq!(pos as usize, PROGRAM.len());
    assert_eq!(tokens.last().unwrap().kind, Eof);
    assert!(!tokens.iter().any(|t| t.kind == Error));
}

#[test]
fn trivia_splits_into_whitespace_newlines_and_comments() {
    let text = "a  // one\n  /* two */\n.b";
    let dot = lex(text)[1];
    assert_eq!(dot.kind, Dot);
    let pieces: Vec<_> = dot
        .trivia(text)
        .map(|(kind, range)| (kind, &text[range]))
        .collect();
    assert_eq!(
        pieces,
        [
            (TriviaKind::Whitespace, "  "),
            (TriviaKind::LineComment, "// one"),
            (TriviaKind::Newline, "\n"),
            (TriviaKind::Whitespace, "  "),
            (TriviaKind::BlockComment, "/* two */"),
            (TriviaKind::Newline, "\n"),
        ]
    );
}

#[test]
fn operators_take_the_longest_match() {
    assert_eq!(
        kinds("a+%b -% c*%d -> == != <= >= .. ?. ??? . = < > | ; : / %"),
        [
            Ident,
            PlusPercent,
            Ident,
            MinusPercent,
            Ident,
            StarPercent,
            Ident,
            Arrow,
            EqEq,
            BangEq,
            LtEq,
            GtEq,
            DotDot,
            QuestionDot,
            Hole,
            Dot,
            Equals,
            Lt,
            Gt,
            Pipe,
            Semicolon,
            Colon,
            Slash,
            Percent,
            Eof
        ]
    );
}

#[test]
fn prefixes_lex_as_single_symbols() {
    assert_eq!(kinds("~ f"), [Symbol, Ident, Eof]);
    assert_eq!(kinds("!!x"), [Symbol, Symbol, Ident, Eof]);
    assert_eq!(kinds("? load"), [Symbol, Ident, Eof]);
    assert_eq!(kinds("a != b"), [Ident, BangEq, Ident, Eof]);
}

#[test]
fn keywords_after_a_dot_are_field_names() {
    assert_eq!(
        kinds("not x.and?.or and y"),
        [Not, Ident, Dot, Ident, QuestionDot, Ident, And, Ident, Eof]
    );
    assert_eq!(kinds("_ _x"), [Underscore, Ident, Eof]);
    assert_eq!(kinds("größe"), [Ident, Eof]);
}

#[test]
fn numbers_never_swallow_ranges_calls_or_signs() {
    assert_eq!(
        tokens("1..10 2.abs() x-2 3.14 1e-9 2E5 0xFF_FF 0b1010 12ab"),
        [
            (Int, "1"),
            (DotDot, ".."),
            (Int, "10"),
            (Int, "2"),
            (Dot, "."),
            (Ident, "abs"),
            (LParen, "("),
            (RParen, ")"),
            (Ident, "x"),
            (Minus, "-"),
            (Int, "2"),
            (Float, "3.14"),
            (Float, "1e-9"),
            (Float, "2E5"),
            (Int, "0xFF_FF"),
            (Int, "0b1010"),
            (Int, "12ab"),
            (Eof, ""),
        ]
    );
}

#[test]
fn interpolation_nests_blocks_and_strings() {
    let text = r#""a {f({ x -> "{x}" })} b {{c}}""#;
    assert_eq!(
        tokens(text),
        [
            (StrStart, "\"a {"),
            (Ident, "f"),
            (LParen, "("),
            (LBrace, "{"),
            (Ident, "x"),
            (Arrow, "->"),
            (StrStart, "\"{"),
            (Ident, "x"),
            (StrEnd, "}\""),
            (RBrace, "}"),
            (RParen, ")"),
            (StrEnd, "} b {{c}}\""),
            (Eof, ""),
        ]
    );
    assert_eq!(
        kinds(r#""{a} and {b}""#),
        [StrStart, Ident, StrMid, Ident, StrEnd, Eof]
    );
}

#[test]
fn triple_quoted_strings_span_lines() {
    let text = "\"\"\"\n  a \"quoted\" {x}\n  \"\"\"";
    assert_eq!(kinds(text), [TripleStrStart, Ident, StrEnd, Eof]);
    assert_eq!(kinds("\"\"\"\n  plain\n  \"\"\""), [Str, Eof]);
}

#[test]
fn byte_and_code_point_literals() {
    assert_eq!(
        tokens(r#"b"\x00{" '\'' b"#),
        [
            (Bytes, r#"b"\x00{""#),
            (CodePoint, r"'\''"),
            (Ident, "b"),
            (Eof, ""),
        ]
    );
}

#[test]
fn unclosed_literals_end_at_the_line() {
    assert_eq!(
        tokens("\"abc\nx"),
        [(Str, "\"abc"), (Newline, "\n"), (Ident, "x"), (Eof, "")]
    );
    assert_eq!(
        tokens("'a\nx"),
        [(CodePoint, "'a"), (Newline, "\n"), (Ident, "x"), (Eof, "")]
    );
    assert_eq!(kinds("a /* never closed"), [Ident, Error, Eof]);
    assert_eq!(kinds("a \\ b"), [Ident, Error, Ident, Eof]);
}

#[test]
fn newlines_end_statements_except_where_lines_continue() {
    // Inside parentheses and brackets.
    assert_eq!(
        kinds("f(a,\n b\n)"),
        [Ident, LParen, Ident, Comma, Ident, RParen, Eof]
    );
    assert_eq!(kinds("[1\n2]"), [LBracket, Int, Int, RBracket, Eof]);
    // A block inside parentheses has statements again.
    assert_eq!(
        kinds("f({\na\nb\n})"),
        [
            Ident, LParen, LBrace, Newline, Ident, Newline, Ident, Newline, RBrace, RParen, Eof
        ]
    );
    // After a binary operator, `,` or `->`, but not before one.
    assert_eq!(kinds("a +\n\nb"), [Ident, Plus, Ident, Eof]);
    assert_eq!(kinds("a and\nb"), [Ident, And, Ident, Eof]);
    // `..` too, so an open range at the end of a line needs parentheses (§7.4).
    assert_eq!(kinds("a..\nb"), [Ident, DotDot, Ident, Eof]);
    assert_eq!(
        kinds("(a..)\nb"),
        [LParen, Ident, DotDot, RParen, Newline, Ident, Eof]
    );
    assert_eq!(
        kinds("{ x ->\n x }"),
        [LBrace, Ident, Arrow, Ident, RBrace, Eof]
    );
    assert_eq!(kinds("a\n-x"), [Ident, Newline, Minus, Ident, Eof]);
    // Before `.`, `?.` and `else`, even across blank lines and comments.
    assert_eq!(kinds("a\n  // c\n\n  .b"), [Ident, Dot, Ident, Eof]);
    assert_eq!(kinds("a\n?.b"), [Ident, QuestionDot, Ident, Eof]);
    assert_eq!(kinds("}\nelse {"), [RBrace, Else, LBrace, Eof]);
    assert_eq!(kinds("a\nelsewhere"), [Ident, Newline, Ident, Eof]);
    assert_eq!(kinds("a\n..b"), [Ident, Newline, DotDot, Ident, Eof]);
    // Every ending newline is its own token, comments stay trivia.
    assert_eq!(
        tokens("a // c\n\nb"),
        [
            (Ident, "a"),
            (Newline, "\n"),
            (Newline, "\n"),
            (Ident, "b"),
            (Eof, "")
        ]
    );
    // A field named like an operator keyword does not continue the line.
    assert_eq!(kinds("x.and\ny"), [Ident, Dot, Ident, Newline, Ident, Eof]);
}
