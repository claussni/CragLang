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

//! Comments anywhere survive formatting: a comment is put at every place a
//! sample allows one, and the formatter must keep it without changing the
//! file's meaning, and keep its own output as it is.

use crag_syntax::{LeafKind, SyntaxNode, TokenKind, lex, parse};

const SAMPLE: &str = r#"import std.time
import std.coll.{Map, List as L}

pub distinct type Percent(value: Int) is Solid where value >= 0

type Pair[T](left: T, right: T = 0, ..Base)

fn main(xs: List[Int], m: Map[Str, Int]) -> Int where T is Num {
  var total = 0
  for (k, v) in m { total = total + v }
  let name: Str = parse("x") else { e -> return e }
  let r = xs.map { x -> x + 1 }.filter { x -> x > 2 }.sum()
  let text = "sum {total * 2} of {name}"
  let grid = [1, 2; 3, 4]
  let dict = ["a": 1, "b": -2]
  let p = (a: 1, b: (2,), ..q)
  ~ !! parse("1")
  atomic { emit ok total }
  if total > 10 and not done { total } else if x { 1 } else { -total }
  case r {
    Order(id: n) where n > 0 -> "order {n}"
    [first, ..rest] -> first
    1..5 | 7 -> 0
    _ -> {
      total
    }
  }
  return total
}

test "t" { let x = b"\x01" }
"#;

/// The token boundaries of `text`: the offsets right after each token,
/// where a block comment changes nothing, and the line ends.
fn places(text: &str) -> (Vec<usize>, Vec<usize>) {
    let tokens = lex(text);
    let mut after = Vec::new();
    for pair in tokens.windows(2) {
        let (a, b) = (pair[0], pair[1]);
        // The symbols of a prefix must stay adjacent.
        if a.kind == TokenKind::Symbol && b.kind == TokenKind::Symbol {
            continue;
        }
        after.push(a.end as usize);
    }
    let ends = text.match_indices('\n').map(|(i, _)| i).collect();
    (after, ends)
}

fn comments(text: &str) -> usize {
    let tokens = lex(text);
    let (green, _) = parse(text, &tokens);
    SyntaxNode::new_root(green)
        .descendant_tokens()
        .filter(|t| matches!(t.kind(), LeafKind::Trivia(k) if k != crag_syntax::TriviaKind::Whitespace && k != crag_syntax::TriviaKind::Newline))
        .count()
}

fn check(text: &str) {
    let once = crag_fmt::format(text, None).unwrap_or_else(|e| panic!("{e:?} for\n{text}"));
    assert_eq!(
        comments(&once),
        comments(text),
        "a comment was lost:\n{text}\n---\n{once}"
    );
    let twice = crag_fmt::format(&once, None).unwrap_or_else(|e| panic!("{e:?} for\n{once}"));
    assert_eq!(once, twice, "not stable for\n{text}");
}

#[test]
fn a_block_comment_after_any_token_is_kept() {
    let (after, _) = places(SAMPLE);
    for at in after {
        check(&format!("{}/* c */{}", &SAMPLE[..at], &SAMPLE[at..]));
    }
}

#[test]
fn a_line_comment_at_any_line_end_is_kept() {
    let (_, ends) = places(SAMPLE);
    for at in ends {
        check(&format!("{} // c{}", &SAMPLE[..at], &SAMPLE[at..]));
    }
}

#[test]
fn a_comment_line_before_any_line_is_kept() {
    let (_, ends) = places(SAMPLE);
    for at in ends {
        check(&format!("{}\n// c{}", &SAMPLE[..at], &SAMPLE[at..]));
        check(&format!("{}\n\n// c\n{}", &SAMPLE[..at], &SAMPLE[at..]));
    }
}

#[test]
fn the_sample_is_stable() {
    check(SAMPLE);
}

#[test]
fn every_width_breaks_only_where_newlines_are_whitespace() {
    for width in 10..=100 {
        let once = crag_fmt::format_to(SAMPLE, None, width)
            .unwrap_or_else(|e| panic!("{e:?} at width {width}"));
        let twice = crag_fmt::format_to(&once, None, width).unwrap();
        assert_eq!(once, twice, "not stable at width {width}");
    }
}
