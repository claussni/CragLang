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

//! The layout rules of Specification §20.9, each on an example.

fn fmt(text: &str) -> String {
    crag_fmt::format(text, Some("geo")).unwrap_or_else(|e| panic!("{e:?} for\n{text}"))
}

/// Formats `input` and checks that the result is `expected` and stays so.
fn check(input: &str, expected: &str) {
    let out = fmt(input);
    assert_eq!(
        out, expected,
        "\n--- got ---\n{out}--- expected ---\n{expected}"
    );
    assert_eq!(fmt(&out), out, "formatting again changed it");
}

#[test]
fn spacing() {
    check(
        "fn f( a :Int,b:Int )->Int{let x=-a*( b+1 )\nlet y=g(a,b ,c: 1)[0]\nx+y}\n",
        "fn f(a: Int, b: Int) -> Int {\n  let x = -a * (b + 1)\n  let y = g(a, b, c: 1)[0]\n  x + y\n}\n",
    );
    check(
        "fn f() { let r = (..p,a: 1)\nlet c = {x->x*2}\nlet xs = [ 1,2 ]\nlet m = [ :]\n}\n",
        "fn f() {\n  let r = (..p, a: 1)\n  let c = { x -> x * 2 }\n  let xs = [1, 2]\n  let m = [:]\n}\n",
    );
}

#[test]
fn a_prefix_is_followed_by_a_space() {
    check(
        "fn f() { !!cfg.decode[Limits]() }\n",
        "fn f() { !! cfg.decode[Limits]() }\n",
    );
    check("fn f() { not  done }\n", "fn f() { not done }\n");
}

#[test]
fn a_block_that_fits_with_one_statement_stays_on_its_line() {
    check("fn f() -> Int {\n  1\n}\n", "fn f() -> Int { 1 }\n");
    check(
        "fn f() {\n  if a {\n    1\n  }\n  else {\n    2\n  }\n}\n",
        "fn f() {\n  if a { 1 } else { 2 }\n}\n",
    );
}

#[test]
fn empty_lines_inside_blocks() {
    check(
        "fn f() {\n\n  a()\n\n\n  b()\n  c()\n\n}\n",
        "fn f() {\n  a()\n\n  b()\n  c()\n}\n",
    );
}

#[test]
fn declarations_are_separated_by_an_empty_line() {
    check(
        "fn a() { 1 }\nfn b() {\n  x()\n  y()\n}\n\n\n\nfn c() { 2 }\n",
        "fn a() { 1 }\n\nfn b() {\n  x()\n  y()\n}\n\nfn c() { 2 }\n",
    );
    // One-line declarations on consecutive lines stay together.
    check("type A\ntype B\n\ntype C\n", "type A\ntype B\n\ntype C\n");
}

#[test]
fn a_long_binary_expression_is_parenthesized_and_broken_before_operators() {
    check(
        "fn f() {\n  let total = subtotalOfTheOrderSoFar + shippingCostsOfAllTheParcels - discountGrantedToTheCustomer + 1\n}\n",
        "fn f() {\n  let total = (subtotalOfTheOrderSoFar\n    + shippingCostsOfAllTheParcels\n    - discountGrantedToTheCustomer\n    + 1)\n}\n",
    );
    // In an argument list, newlines are whitespace already.
    check(
        "fn f() {\n  g(subtotalOfTheOrderSoFar + shippingCostsOfAllTheParcels - discountGrantedToTheCustomer + handlingFee)\n}\n",
        "fn f() {\n  g(\n    subtotalOfTheOrderSoFar\n      + shippingCostsOfAllTheParcels\n      - discountGrantedToTheCustomer\n      + handlingFee,\n  )\n}\n",
    );
}

#[test]
fn a_long_list_puts_one_item_per_line_with_commas() {
    check(
        "fn f() {\n  callWithManyArguments(firstArgumentIsLong, secondArgumentIsEvenLonger, third: thirdArgumentIsLabeled,)\n}\n",
        "fn f() {\n  callWithManyArguments(\n    firstArgumentIsLong,\n    secondArgumentIsEvenLonger,\n    third: thirdArgumentIsLabeled,\n  )\n}\n",
    );
    check("fn f() { g(a, b,) }\n", "fn f() { g(a, b) }\n");
    // A record of one field keeps its comma.
    check("fn f() { (a,) }\n", "fn f() { (a,) }\n");
}

#[test]
fn a_long_method_chain_breaks_before_each_call() {
    check(
        "fn f() {\n  let r = orders.filter { o -> o.isOpen }.map { o -> o.total * taxRateOfTheCountryOfTheBuyerAndSeller }.sum()\n}\n",
        "fn f() {\n  let r = orders\n    .filter { o -> o.isOpen }\n    .map { o -> o.total * taxRateOfTheCountryOfTheBuyerAndSeller }\n    .sum()\n}\n",
    );
}

#[test]
fn a_case_arm_breaks_after_its_arrow() {
    check(
        "fn f() {\n  case r {\n    Order -> \"order {r.id}\"\n    Rejected(code: 404, reason: \"resource permanently removed by its owner\") -> \"gone for good: {r.reason}\"\n  }\n}\n",
        "fn f() {\n  case r {\n    Order -> \"order {r.id}\"\n    Rejected(code: 404, reason: \"resource permanently removed by its owner\") ->\n      \"gone for good: {r.reason}\"\n  }\n}\n",
    );
}

#[test]
fn type_clauses_go_on_their_own_lines_when_long() {
    check(
        "pub distinct type Percent(value: Int) is Solid where { value >= 0, value <= 100, value != 55, value != 56 }\n",
        "pub distinct type Percent(value: Int)\n  is Solid\n  where { value >= 0, value <= 100, value != 55, value != 56 }\n",
    );
    check(
        "type P(value: Int) is { Solid, Secret }\n",
        "type P(value: Int) is { Solid, Secret }\n",
    );
}

#[test]
fn imports_are_grouped_and_sorted() {
    check(
        "import geo.shape\nimport http.client\nimport std.time\nimport std.coll.{Map, List}\n\nfn f() { 1 }\n",
        "import std.coll.{List, Map}\nimport std.time\n\nimport http.client\n\nimport geo.shape\n\nfn f() { 1 }\n",
    );
}

#[test]
fn comments_keep_their_place() {
    check(
        "// head\n\n// about f\nfn f() { // opens\n  a() // after a\n\n  // before b\n  b() /* inline */\n  // last\n}\n// tail\n",
        "// head\n\n// about f\nfn f() {  // opens\n  a()  // after a\n\n  // before b\n  b() /* inline */\n  // last\n}\n\n// tail\n",
    );
    // A comment inside a list breaks it.
    check(
        "fn f() { g(a, // first\n  b) }\n",
        "fn f() {\n  g(\n    a,  // first\n    b,\n  )\n}\n",
    );
}

#[test]
fn strings_and_numbers_are_untouched() {
    check(
        "fn f() { let s = \"a  {x+1}  b\"\nlet n = 1_000_000\nlet h = 0xFF }\n",
        "fn f() {\n  let s = \"a  {x + 1}  b\"\n  let n = 1_000_000\n  let h = 0xFF\n}\n",
    );
}

#[test]
fn a_file_that_does_not_parse_is_left_alone() {
    assert!(matches!(
        crag_fmt::format("fn f( {", None),
        Err(crag_fmt::FormatError::Syntax(_))
    ));
}
