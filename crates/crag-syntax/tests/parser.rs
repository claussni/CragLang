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

use crag_syntax::{
    LeafKind, ParseError, SyntaxElement, SyntaxKind, SyntaxNode, TokenKind, lex, parse,
};

const PROGRAM: &str = r#"import std.io
import std.text as text
import std.coll.{List, Map as Dict}
import cLib("libm").{ sin(x: Float) -> Float, cos(x: Float) -> Float } is ThreadSafe

// A point on the drawing canvas.
pub type Point(x: Int, y: Int = 0)
type Shape = Circle | Square
type Empty
opaque type Meters = Float
type Named(..Point, name: Str)
  where { x >= 0
    y >= 0 }
  is Solid
  on Dispose { p -> log(p) }
type Row = (id: Int, ..)
type Handler = (Int, Str) -> Bool | Empty

pub form Show[T] {
  show(value: T) -> Str
}
form Number[T] = Int | Float

fn discard[T](value: T) -> () prefix "~" {
  ()
}

pub fn area(s: Shape) -> Float
  where s.valid() {
  case s {
    Circle(r:) -> 3.14 * r * r
    Square(side: n) where n > 0 -> n * n
    n: Int -> n
    [first, ..rest] -> 0
    1..9 | 20 -> 1
    Option[Int](value:) -> value
    _ -> pass
  }
}

let origin = Point(x: 0, y: 0)
embed logo: Bytes from "logo.png"

test "addition works" {
  let (a, b) = (left: 1, right: 2)
  var total = 0
  total = total + a
  ref counter = 0
  ext shared = 1
  let names = people
    .filter { p -> p.age >= 18 }
    .map { p -> p.name }
  let grid = [1, 2; 3, 4]
  let map = ["a": 1, "b": 2]
  let none = [:]
  let list = [1, 2, 3,]
  let r = (1..)
  let msg = "sum {a + b} of {names.join(", ")}"
  let f = { x: Int, y -> x + y }
  let g = { -> 42 }
  let x = fetch() else { return }
  ~ sendMail(msg)
  let port = !! Int.parse(portText)
  let lazyValue = lazy expensive()
  let ok = if xs.any { x -> x > 0 } { 1 } else if done { 2 } else { 3 }
  atomic { counter.update { c -> c + 1 } }
  for (k, v) in map {
    emit ok k
  }
  on Interrupt { s -> return }
  fn local(n: Int) -> Int { n * 2 }
  emit fail x?.and
  check(not a == b and c is Point or d < e, Fields[R, () -> _], List[Int | Str])
  ???
}
"#;

fn parse_text(text: &str) -> (SyntaxNode, Vec<ParseError>) {
    let (green, errors) = parse(text, &lex(text));
    (SyntaxNode::new_root(green), errors)
}

/// The tree as an S-expression of node kinds and token texts, without
/// trivia and newline tokens.
fn sexp(node: &SyntaxNode) -> String {
    let mut parts = vec![format!("{:?}", node.kind())];
    for child in node.children_with_tokens() {
        match child {
            SyntaxElement::Node(child) => parts.push(sexp(&child)),
            SyntaxElement::Token(token) => match token.kind() {
                LeafKind::Trivia(_) | LeafKind::Token(TokenKind::Newline) => {}
                LeafKind::Token(_) => parts.push(token.text().to_string()),
            },
        }
    }
    format!("({})", parts.join(" "))
}

/// The S-expression of the one expression statement in `fn f() { … }`.
fn expr(text: &str) -> String {
    let source = format!("fn f() {{ {text} }}");
    let (root, errors) = parse_text(&source);
    assert_eq!(errors, [], "{text}");
    let block = root
        .descendants()
        .find(|n| n.kind() == SyntaxKind::Block)
        .unwrap();
    let mut statements = block.children();
    let statement = statements.next().unwrap();
    assert!(statements.next().is_none(), "{text}");
    sexp(&statement)
}

fn errors(text: &str) -> Vec<String> {
    parse_text(text).1.into_iter().map(|e| e.message).collect()
}

#[test]
fn the_sample_program_parses_without_errors() {
    let (root, errors) = parse_text(PROGRAM);
    assert_eq!(errors, []);
    assert_eq!(root.text(), PROGRAM);
    assert!(
        !root.descendants().any(|n| n.kind() == SyntaxKind::Error),
        "{root:#?}"
    );
}

#[test]
fn binary_operators_follow_the_precedence_table() {
    assert_eq!(
        expr("a + b * c"),
        "(BinExpr (NameRef a) + (BinExpr (NameRef b) * (NameRef c)))"
    );
    assert_eq!(
        expr("a - b - c"),
        "(BinExpr (BinExpr (NameRef a) - (NameRef b)) - (NameRef c))"
    );
    assert_eq!(
        expr("a or b and c"),
        "(BinExpr (NameRef a) or (BinExpr (NameRef b) and (NameRef c)))"
    );
    assert_eq!(
        expr("not x == y"),
        "(PrefixExpr not (BinExpr (NameRef x) == (NameRef y)))"
    );
    assert_eq!(
        expr("a..b - 1"),
        "(RangeExpr (NameRef a) .. (BinExpr (NameRef b) - (Literal 1)))"
    );
    assert_eq!(
        expr("x is Point and x.y > 0"),
        "(BinExpr (IsExpr (NameRef x) is (NamedType Point)) and \
         (BinExpr (FieldExpr (NameRef x) . y) > (Literal 0)))"
    );
}

#[test]
fn prefixes_bind_tighter_than_binary_operators() {
    assert_eq!(
        expr("-2.abs()"),
        "(PrefixExpr - (CallExpr (FieldExpr (Literal 2) . abs) (ArgList ( ))))"
    );
    assert_eq!(
        expr("!! a + b"),
        "(BinExpr (PrefixExpr ! ! (NameRef a)) + (NameRef b))"
    );
    assert_eq!(
        expr("~ a.b().c()"),
        "(PrefixExpr ~ (CallExpr (FieldExpr (CallExpr (FieldExpr (NameRef a) . b) \
         (ArgList ( ))) . c) (ArgList ( ))))"
    );
    // Separated symbols are separate prefixes.
    assert_eq!(expr("! ! a"), "(PrefixExpr ! (PrefixExpr ! (NameRef a)))");
}

#[test]
fn comparisons_and_ranges_do_not_chain() {
    assert_eq!(
        errors("fn f() { a < b < c }"),
        ["comparisons cannot be chained; use `and`"]
    );
    assert_eq!(errors("fn f() { a..b..c }"), ["ranges cannot be chained"]);
}

#[test]
fn a_brace_is_a_closure_only_before_an_arrow() {
    assert_eq!(
        expr("xs.map { x -> x }"),
        "(CallExpr (FieldExpr (NameRef xs) . map) (Closure { (ClosureParams \
         (ClosureParam (NamePat x))) -> (NameRef x) }))"
    );
    assert_eq!(
        expr("if xs.any { x -> x } { 1 }"),
        "(IfExpr if (CallExpr (FieldExpr (NameRef xs) . any) (Closure { \
         (ClosureParams (ClosureParam (NamePat x))) -> (NameRef x) })) (Block { (Literal 1) }))"
    );
    assert_eq!(
        expr("case x { _ -> 1 }"),
        "(CaseExpr case (NameRef x) { (CaseArm (WildcardPat _) -> (Literal 1)) })"
    );
    assert_eq!(
        expr("f(a) { -> b }"),
        "(CallExpr (NameRef f) (ArgList ( (NameRef a) )) (Closure { -> (NameRef b) }))"
    );
}

#[test]
fn parentheses_make_units_groups_and_records() {
    assert_eq!(expr("()"), "(RecordExpr (ArgList ( )))");
    assert_eq!(expr("(a)"), "(ParenExpr (ArgList ( (NameRef a) )))");
    assert_eq!(
        expr("(x: 1, ..p)"),
        "(RecordExpr (ArgList ( (LabeledArg (Label x) : (Literal 1)) , \
         (SpreadArg .. (NameRef p)) )))"
    );
    assert_eq!(
        expr("p.update(pos.x: 1, and: 2)"),
        "(CallExpr (FieldExpr (NameRef p) . update) (ArgList ( (LabeledArg (Label pos . x) \
         : (Literal 1)) , (LabeledArg (Label and) : (Literal 2)) )))"
    );
}

#[test]
fn brackets_make_lists_maps_and_grids() {
    assert_eq!(expr("[]"), "(ListExpr [ ])");
    assert_eq!(expr("[:]"), "(MapExpr [ : ])");
    assert_eq!(expr("[1, 2]"), "(ListExpr [ (Literal 1) , (Literal 2) ])");
    assert_eq!(
        expr("[\"a\": 1]"),
        "(MapExpr [ (MapEntry (Literal \"a\") : (Literal 1)) ])"
    );
    assert_eq!(
        expr("[1, 2; 3, 4]"),
        "(GridExpr [ (GridRow (Literal 1) , (Literal 2)) ; (GridRow (Literal 3) , (Literal 4)) ])"
    );
    assert_eq!(
        expr("xs[0]"),
        "(BracketExpr (NameRef xs) (ArgList [ (Literal 0) ]))"
    );
}

#[test]
fn bracket_arguments_may_be_types() {
    assert_eq!(
        expr("Fields[R, () -> _]"),
        "(BracketExpr (NameRef Fields) (ArgList [ (NameRef R) , \
         (FnType (FnTypeParams ( )) -> (InferType _)) ]))"
    );
    assert_eq!(
        expr("List[Int | Str]"),
        "(BracketExpr (NameRef List) (ArgList [ (UnionType (NameRef Int) | \
         (NamedType Str)) ]))"
    );
}

#[test]
fn strings_hold_their_interpolations() {
    assert_eq!(
        expr("\"a {x} b {f(y)} c\""),
        "(StrExpr \"a { (NameRef x) } b { (CallExpr (NameRef f) (ArgList ( (NameRef y) ))) } c\")"
    );
}

#[test]
fn declarations() {
    let decl = |text: &str| {
        let (root, errors) = parse_text(text);
        assert_eq!(errors, [], "{text}");
        sexp(&root.children().next().unwrap())
    };
    assert_eq!(
        decl("pub type Point(x: Int, y: Int = 0)"),
        "(TypeDecl pub type Point (FieldList ( (Field x : (NamedType Int)) , \
         (Field y : (NamedType Int) = (Literal 0)) )))"
    );
    assert_eq!(
        decl("type Handler = (Int) -> Bool | Empty"),
        "(TypeDecl type Handler = (FnType (FnTypeParams ( (NamedType Int) )) -> \
         (UnionType (NamedType Bool) | (NamedType Empty))))"
    );
    assert_eq!(
        decl("fn id[T](x: T) -> T\n  where Show[T] {\n  x\n}"),
        "(FnDecl fn id (TypeParams [ (TypeParam T) ]) (ParamList ( (Param x : (NamedType T)) )) \
         (ReturnType -> (NamedType T)) (WhereClause where (BracketExpr (NameRef Show) \
         (ArgList [ (NameRef T) ]))) (Block { (NameRef x) }))"
    );
    assert_eq!(
        decl("fn sin(x: Float) -> Float"),
        "(FnDecl fn sin (ParamList ( (Param x : (NamedType Float)) )) \
         (ReturnType -> (NamedType Float)))"
    );
    assert_eq!(
        decl("import std.coll.{List, Map as Dict}"),
        "(Import import (Path std . coll) . (ImportItems { (ImportItem List) , \
         (ImportItem Map as Dict) }))"
    );
}

#[test]
fn patterns() {
    assert_eq!(
        expr("case s { Circle(r:) | Square(side: _) -> 1\n n: Int -> 2\n [a, ..] -> 3 }"),
        "(CaseExpr case (NameRef s) { (CaseArm (OrPat (RecordPat Circle ( (PatField r :) )) | \
         (RecordPat Square ( (PatField side : (WildcardPat _)) ))) -> (Literal 1)) \
         (CaseArm (BindPat n : (NamePat Int)) -> (Literal 2)) \
         (CaseArm (ListPat [ (NamePat a) , (RestPat ..) ]) -> (Literal 3)) })"
    );
}

#[test]
fn a_comment_above_a_declaration_is_its_previous_sibling() {
    let text = "// Docs.\nfn f() {}\n";
    let (root, _) = parse_text(text);
    let fn_decl = root.children().next().unwrap();
    assert_eq!(fn_decl.kind(), SyntaxKind::FnDecl);
    assert_eq!(fn_decl.range(), 9..18);
    let before: Vec<_> = root
        .tokens()
        .take_while(|t| t.range().end <= fn_decl.range().start)
        .map(|t| t.text().to_string())
        .collect();
    assert_eq!(before, ["// Docs.", "\n"]);
}

#[test]
fn errors_stay_in_their_statement() {
    let text = "fn f() {\n  let = 1\n  let y = 2\n}\nfn g() {}";
    let (root, found) = parse_text(text);
    assert_eq!(found.len(), 1, "{found:?}");
    assert_eq!(found[0].message, "expected a pattern");
    let lets = root
        .descendants()
        .filter(|n| n.kind() == SyntaxKind::LetDecl)
        .count();
    assert_eq!(lets, 2);
    let fns = root.children().filter(|n| n.kind() == SyntaxKind::FnDecl);
    assert_eq!(fns.count(), 2);

    assert_eq!(
        errors("fn f() { a b }\nfn g() {}"),
        ["expected a newline or `}`"]
    );
    assert_eq!(errors("fn f(x: Int {\n}"), ["expected `,` or `)`"]);
    assert_eq!(
        errors(") fn"),
        // Both missing pieces are at the end of the file; one error is enough.
        ["expected a declaration", "expected a function name"]
    );
}

/// A small deterministic generator, so failures reproduce.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Checks the tree: lossless, and every node's children laid end to end.
fn check_tree(node: &SyntaxNode) {
    let mut pos = node.range().start;
    for child in node.children_with_tokens() {
        assert_eq!(child.range().start, pos);
        pos = child.range().end;
        if let SyntaxElement::Node(child) = child {
            check_tree(&child);
        }
    }
    assert_eq!(pos, node.range().end);
}

#[test]
fn any_input_parses_to_a_lossless_tree() {
    let pieces: Vec<&str> = {
        let tokens = lex(PROGRAM);
        tokens
            .iter()
            .map(|t| &PROGRAM[t.trivia_start as usize..t.end as usize])
            .collect()
    };
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    for round in 0..300 {
        // Shuffle in, drop and duplicate runs of the program's tokens.
        let mut text = String::new();
        let mut i = 0;
        while i < pieces.len() {
            match rng.below(20) {
                0 => i += rng.below(8),
                1 => text.push_str(pieces[rng.below(pieces.len())]),
                _ => {
                    text.push_str(pieces[i]);
                    i += 1;
                }
            }
        }
        let (root, _) = parse_text(&text);
        assert_eq!(root.text(), text, "round {round}");
        assert_eq!(root.range(), 0..text.len() as u32);
        check_tree(&root);
    }
}

#[test]
fn deep_nesting_is_reported_instead_of_overflowing_the_stack() {
    for (open, close) in [("(", ")"), ("[", "]"), ("{", "}"), ("-", "")] {
        let depth = 100_000;
        let text = format!(
            "fn f() {{ {}x{} }}",
            open.repeat(depth),
            close.repeat(depth)
        );
        let (root, errors) = parse_text(&text);
        assert_eq!(root.text(), text);
        assert!(
            errors.iter().any(|e| e.message == "nesting too deep"),
            "{open}"
        );
    }
    let (_, errors) = parse_text(&format!(
        "fn f() {{ {}x{} }}",
        "(".repeat(100),
        ")".repeat(100)
    ));
    assert_eq!(errors, []);
}
