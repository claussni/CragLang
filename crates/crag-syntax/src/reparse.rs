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

//! Incremental reparse (Implementation Plan §11.4.3).
//!
//! An edit inside a block usually leaves everything outside the block as it
//! was, so only the block is lexed and parsed again, and the new block
//! replaces the old one in the tree. That is exact when three things hold:
//!
//! - The edited block still lexes as a block on its own (`lex_block`). Then
//!   the lexer never consults its state from outside the block, and leaves
//!   it as it found it, so the tokens around the block stay the same.
//! - It still parses as a block that ends at its last `}` (`parse_block`).
//!   No rule outside a block looks into it, except to decide whether a `{`
//!   opens a closure, which `parse_block` checks.
//! - The nesting limit is not reached. The depth at which the block was
//!   parsed is at most the number of its ancestors: every open node and
//!   every pending list encloses it.
//!
//! When the innermost block around the edit fails a check, the next one out
//! is tried, and without one the whole file is parsed again.

use crate::green::{GreenElement, GreenNode};
use crate::kind::SyntaxKind;
use crate::lexer::{lex, lex_block};
use crate::parser::{ParseError, parse, parse_block};
use crate::red::SyntaxNode;
use crate::token::TextEdit;

/// Parses again after an edit. `old` and `errors` are the result of parsing
/// the text before `edit`; the result equals parsing the text after it.
pub fn reparse(
    old: &GreenNode,
    errors: &[ParseError],
    edit: &TextEdit,
) -> (GreenNode, Vec<ParseError>) {
    reparse_block(old, errors, edit).unwrap_or_else(|| {
        let text = edit.apply(&old.text());
        parse(&text, &lex(&text))
    })
}

/// Reparses the innermost block around the edit that allows it.
fn reparse_block(
    old: &GreenNode,
    errors: &[ParseError],
    edit: &TextEdit,
) -> Option<(GreenNode, Vec<ParseError>)> {
    let root = SyntaxNode::new_root(old.clone());
    let token = root.token_at(edit.start)?;
    for block in token.parent().ancestors() {
        let range = block.range();
        // The braces themselves stay untouched.
        if block.kind() != SyntaxKind::Block || edit.start <= range.start || edit.end >= range.end {
            continue;
        }
        let local = TextEdit {
            start: edit.start - range.start,
            end: edit.end - range.start,
            insert: edit.insert.clone(),
        };
        let text = local.apply(&block.text());
        let Some(tokens) = lex_block(&text) else {
            continue;
        };
        // Neither the root nor the block itself count.
        let depth = block.ancestors().count() - 2;
        let Some((new, block_errors)) = parse_block(&text, &tokens, depth) else {
            continue;
        };
        let shift = |e: &ParseError, by: i64| ParseError {
            message: e.message.clone(),
            range: (e.range.start as i64 + by) as u32..(e.range.end as i64 + by) as u32,
        };
        // Errors inside the old block start after its `{`, the others
        // before it or at its end.
        let merged = errors
            .iter()
            .filter(|e| e.range.start <= range.start)
            .cloned()
            .chain(block_errors.iter().map(|e| shift(e, range.start as i64)))
            .chain(
                errors
                    .iter()
                    .filter(|e| e.range.start >= range.end)
                    .map(|e| shift(e, edit.delta())),
            )
            .collect();
        return Some((splice(&block, new), merged));
    }
    None
}

/// The tree of `node` with `node` replaced by `new`.
fn splice(node: &SyntaxNode, new: GreenNode) -> GreenNode {
    let mut green = new;
    let mut node = node.clone();
    while let Some(parent) = node.parent() {
        green = parent
            .green()
            .replace_child(node.index(), GreenElement::Node(green));
        node = parent;
    }
    green
}

#[cfg(test)]
mod tests {
    use super::*;

    fn edit(text: &str, find: &str, insert: &str) -> TextEdit {
        let start = text.find(find).expect("text to replace") as u32;
        TextEdit {
            start,
            end: start + find.len() as u32,
            insert: insert.into(),
        }
    }

    /// Whether the edit is reparsed within a block, and if so, that the
    /// result equals a full parse.
    fn incremental(text: &str, find: &str, insert: &str) -> bool {
        let (old, errors) = parse(text, &lex(text));
        let edit = edit(text, find, insert);
        let new_text = edit.apply(text);
        let Some(result) = reparse_block(&old, &errors, &edit) else {
            return false;
        };
        assert_eq!(result, parse(&new_text, &lex(&new_text)), "{new_text:?}");
        true
    }

    #[test]
    fn edits_inside_a_block_reparse_only_the_block() {
        let text = "fn f() {\n  let a = 1\n  if a { b(a) }\n}\nfn g() { 2 }\n";
        assert!(incremental(text, "b(a)", "c + d"));
        assert!(incremental(text, "1", "1 +\n  2"));
        assert!(incremental(text, "1", "\"x {a}\""));
        assert!(incremental(text, "b(a)", "case a { 1 -> 2 }"));
        // Errors before and after the block are kept and shifted.
        let broken = "let = 1\nfn f() { a }\nlet = 2";
        assert!(incremental(broken, "a", "a + + b"));
    }

    #[test]
    fn edits_that_break_a_block_reparse_the_file() {
        let text = "fn f() { a }\nfn g() { [b] }";
        // Unbalanced, or balanced only with brackets from outside.
        assert!(!incremental(text, "a", "a {"));
        assert!(!incremental(text, "a", ")"));
        assert!(!incremental(text, "a", "\"a"));
        assert!(!incremental(text, "a", "/* a"));
        // A block that turns into a closure.
        assert!(!incremental("let f = { a }", "a", "x -> a"));
        // An edit touching a brace.
        assert!(!incremental(text, "{ a", "{ b"));
        // Outside every block.
        assert!(!incremental(text, "g", "h"));
    }

    const PROGRAM: &str = r#"type Point(x: Int, y: Int = 0)

fn area(s: Shape) -> Float {
  case s {
    Circle(r:) -> 3.14 * r * r
    Square(side: n) where n > 0 -> { n * n }
    _ -> pass
  }
}

test "blocks" {
  let names = people
    .filter { p -> p.age >= 18 }
    .map { p -> p.name }
  let msg = "sum {a + b} of {names.join(", ")}"
  let ok = if xs.any { x -> x > 0 } { 1 } else if done { 2 } else { 3 }
  atomic { counter.update { c -> c + 1 } }
  for (k, v) in map {
    emit ok k
    { nested(k)
      [v, { w }] }
  }
  fn local(n: Int) -> Int { n * 2 }
}
"#;

    const FRAGMENTS: &[&str] = &[
        "\"", "{", "}", "(", ")", "[", "]", "/*", "*/", "//", "\n", ".", "..", "else", "x", " ",
        "+", "->", ",", "1", "=", "let", "case", "if", "{ x -> }", "{ 1 }", "\"{a}\"",
    ];

    /// A small deterministic generator, so failures reproduce.
    struct Rng(u64);

    impl Rng {
        fn below(&mut self, n: usize) -> usize {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            (self.0 % n as u64) as usize
        }
    }

    #[test]
    fn reparsing_after_an_edit_equals_parsing_from_scratch() {
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        let mut reparsed = 0;
        let steps = 400 * 10;
        // Short runs, since unbalanced edits pile up and leave no block
        // to reparse.
        for round in 0..400 {
            let mut text = PROGRAM.to_string();
            let (mut green, mut errors) = parse(&text, &lex(&text));
            for step in 0..10 {
                let start = rng.below(text.len() + 1);
                let end = (start + rng.below(6)).min(text.len());
                let insert: String = (0..rng.below(3))
                    .map(|_| FRAGMENTS[rng.below(FRAGMENTS.len())])
                    .collect();
                let edit = TextEdit {
                    start: start as u32,
                    end: end as u32,
                    insert,
                };
                let new_text = edit.apply(&text);
                reparsed += reparse_block(&green, &errors, &edit).is_some() as usize;
                let result = reparse(&green, &errors, &edit);
                assert!(
                    result == parse(&new_text, &lex(&new_text)),
                    "round {round}, step {step}: {edit:?} on {text:?}"
                );
                text = new_text;
                (green, errors) = result;
            }
        }
        // Many random edits unbalance their block, but enough are reparsed
        // incrementally that the comparison tests that path.
        assert!(reparsed * 6 > steps, "{reparsed} of {steps} reparsed");
    }

    #[test]
    fn the_nesting_limit_reparses_the_file() {
        let text = format!("fn f() {{ {}x{} }}", "(".repeat(600), ")".repeat(600));
        assert!(!incremental(&text, "x", "y"));
        let text = format!("fn f() {{ {}x{} }}", "(".repeat(100), ")".repeat(100));
        assert!(incremental(&text, "x", "y"));
        // A block near the limit, made to cross it.
        for (open, close) in [("(", ")"), ("[", "]"), ("[x, ", "]")] {
            for n in 230..520 {
                let text = format!("fn f() {{ {}{{ x }}{} }}", open.repeat(n), close.repeat(n));
                incremental(
                    &text,
                    "x",
                    &format!("{}x{}", "(".repeat(20), ")".repeat(20)),
                );
            }
        }
    }
}
