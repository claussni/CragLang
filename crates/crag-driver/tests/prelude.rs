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

//! The functions of the prelude on text, bytes and collections
//! (Specification §19.10, §19.11), each input with what the REPL shows for
//! it.

use crag_driver::{Project, Repl, Scratch};
use crag_session::ImageCommand;

fn repl() -> Repl {
    let scratch = Scratch::start(ImageCommand {
        program: env!("CARGO_BIN_EXE_crag").into(),
        args: vec!["__image".into()],
    })
    .unwrap();
    Repl::new(Project::bare(), scratch)
}

/// Runs each input and compares what the REPL shows, without its newline.
fn check(cases: &[(&str, &str)]) {
    let mut r = repl();
    let mut wrong = Vec::new();
    for (input, expected) in cases {
        let shown = match r.eval_input(input) {
            Ok(output) => output.render(),
            Err(errors) => errors,
        };
        if shown.trim_end() != *expected {
            wrong.push(format!(
                "{input}\n  expected {expected}\n  shown    {}",
                shown.trim_end()
            ));
        }
    }
    assert!(wrong.is_empty(), "\n{}", wrong.join("\n"));
}

#[test]
fn strings() {
    check(&[
        (r#""héllo".byteCount()"#, "6"),
        (r#""héllo".codePointCount()"#, "5"),
        (r#""".isEmpty()"#, "True"),
        (r#""ab".codePoints()"#, "['a', 'b']"),
        (r#""a,,b".split(",")"#, r#"["a", "", "b"]"#),
        (r#""".split(",")"#, r#"[""]"#),
        (r#""ab".split("")"#, r#"["a", "b"]"#),
        (r#""a\r\nb\n".lines()"#, r#"["a", "b"]"#),
        (r#""\n".lines()"#, r#"[""]"#),
        (r#""".lines()"#, "[]"),
        (r#"["a", "b", "c"].join(", ")"#, r#""a, b, c""#),
        (r#"["a", "b"].join()"#, r#""ab""#),
        (r#""Grüße".contains("üß")"#, "True"),
        (r#""Grüße".startsWith("Gr")"#, "True"),
        (r#""Grüße".endsWith("x")"#, "False"),
        (r#""  hi \t".trim()"#, r#""hi""#),
        (r#""  hi ".trimStart()"#, r#""hi ""#),
        (r#""  hi ".trimEnd()"#, r#""  hi""#),
        (r#""straße".toUpper()"#, r#""STRASSE""#),
        (r#""ÄB".toLower()"#, r#""äb""#),
        (r#""a.b.c".replace(".", "::")"#, r#""a::b::c""#),
        (r#""ab".repeat(3)"#, r#""ababab""#),
        (r#""ab".repeat(0)"#, r#""""#),
        (r#""7".padStart(3, with: '0')"#, r#""007""#),
        (r#""ab".padEnd(4)"#, r#""ab  ""#),
        (r#""long".padStart(2)"#, r#""long""#),
        (r#""b" + "c""#, r#""bc""#),
        (r#""ab".compare("ac")"#, "Less"),
        (r#""b".compare("b")"#, "Equal"),
    ]);
}

#[test]
fn positions_in_strings() {
    check(&[
        (r#"let s = "Grüße, Crag""#, ""),
        (
            r#"s.indexOf(",").then { at -> s.substring(before: at) }"#,
            r#""Grüße""#,
        ),
        (r#"s.indexOf("x")"#, "Empty"),
        (
            r#"s.lastIndexOf("r").then { at -> s.substring(from: at) }"#,
            r#""rag""#,
        ),
        (
            r#"s.substring(from: s.start(), before: s.end())"#,
            r#""Grüße, Crag""#,
        ),
        (r#"s.codePointAt(s.start())"#, "'G'"),
        (
            r#"s.after(s.start()).then { at -> s.codePointAt(at) }"#,
            "'r'",
        ),
        (r#"s.before(s.start())"#, "Empty"),
        (r#"s.after(s.end())"#, "Empty"),
        (
            r#"s.indexOf("ü").then { at -> s.after(at) }.then { at -> s.substring(from: at) }"#,
            r#""ße, Crag""#,
        ),
        (
            r#"s.indexOf("r", from: s.indexOf("C").orElse(s.start())).then { at -> s.substring(from: at) }"#,
            r#""rag""#,
        ),
        (r#"s.start().compare(s.end())"#, "Less"),
    ]);
}

#[test]
fn a_position_off_a_boundary_traps() {
    let mut r = repl();
    r.eval_input(r#"let s = "ü""#).unwrap();
    r.eval_input(r#"let t = "ab""#).unwrap();
    let out = r
        .eval_input(r#"t.after(t.start()).then { at -> s.substring(from: at) }"#)
        .unwrap()
        .render();
    assert!(out.contains("trap: index out of range"), "{out}");
}

#[test]
fn numbers_from_text() {
    check(&[
        (r#"Int.parse("42")"#, "42"),
        (r#"Int.parse("-17")"#, "-17"),
        (r#"Int.parse("+5")"#, "5"),
        (r#"Int.parse("ff", base: 16)"#, "255"),
        (r#"Int.parse("1_000")"#, r#"ParseError(text: "1_000")"#),
        (r#"Int.parse(" 1")"#, r#"ParseError(text: " 1")"#),
        (r#"Int.parse("")"#, r#"ParseError(text: "")"#),
        (
            r#"Int.parse("99999999999999999999")"#,
            r#"ParseError(text: "99999999999999999999")"#,
        ),
        (r#"Float.parse("1.5")"#, "1.5"),
        (r#"Float.parse("-2e3")"#, "-2000.0"),
        (r#"Float.parse("inf")"#, r#"ParseError(text: "inf")"#),
        (r#"Float.parse("NaN")"#, r#"ParseError(text: "NaN")"#),
        (r#"Float.parse("1e400")"#, r#"ParseError(text: "1e400")"#),
    ]);
}

#[test]
fn code_points() {
    check(&[
        ("codePoint(65)", "'A'"),
        ("codePoint(55296)", "InvalidCodePoint(value: 55296)"),
        ("codePoint(1114112)", "InvalidCodePoint(value: 1114112)"),
        ("'A'.value()", "65"),
        ("'ß'.isLetter()", "True"),
        ("'7'.isDigit()", "True"),
        ("'٣'.isDigit()", "False"),
        ("'٣'.isNumeric()", "True"),
        ("' '.isWhitespace()", "True"),
        ("'a'.isUpper()", "False"),
        ("'a'.isLower()", "True"),
        ("'a'.toUpper()", "'A'"),
        ("'ß'.toUpper()", "'ß'"),
        ("'Ä'.toLower()", "'ä'"),
        ("'x'.text()", r#""x""#),
    ]);
}

#[test]
fn bytes() {
    check(&[
        (r#"bytes("hé")"#, r#"b"h\xc3\xa9""#),
        (r#"bytes("hé").count()"#, "3"),
        (r#"bytes("hé").text()"#, r#""hé""#),
        (r#"b"\xff".text()"#, "NotUtf8()"),
        (r#"bytes("hi").hex()"#, r#""6869""#),
        (r#"bytes("hi").get(1)"#, "105"),
        (r#"bytes("hi").get(2)"#, "Empty"),
        (r#"bytes("hello").slice(1..3)"#, r#"b"ell""#),
        (r#"b"a" + b"b""#, r#"b"ab""#),
        (r#"b"a".compare(b"b")"#, "Less"),
    ]);
}

#[test]
fn values_compare_hash_and_show_by_their_structure() {
    check(&[
        ("type P(x: Int, name: Str)", ""),
        (r#"P(x: 1, name: "a") == P(x: 1, name: "a")"#, "True"),
        (r#"P(x: 1, name: "a") != P(x: 2, name: "a")"#, "True"),
        (r#"P(x: 1, name: "b") < P(x: 2, name: "a")"#, "True"),
        (r#"P(x: 1, name: "a").compare(P(x: 1, name: "b"))"#, "Less"),
        (r#"P(x: 1, name: "q").show()"#, r#""P(x: 1, name: \"q\")""#),
        (
            r#"P(x: 1, name: "a").hash() == P(x: 1, name: "a").hash()"#,
            "True",
        ),
        ("[1, 2] == [1, 2]", "True"),
        ("[1, 2] < [1, 3]", "True"),
        ("[1, 2] < [1, 2, 0]", "True"),
        (r#"["a": 1, "b": 2] == ["b": 2, "a": 1]"#, "True"),
        (r#"["a": 1].hash() == ["a": 1].hash()"#, "True"),
        ("(0.0).hash() == (-0.0).hash()", "True"),
        ("3.compare(4)", "Less"),
        ("(1.5).show()", r#""1.5""#),
        (r#""x".show()"#, r#""\"x\"""#),
        ("type Odd", ""),
        (
            "fn half(n: Int) -> Int | Odd { if n % 2 == 0 { n / 2 } else { Odd } }",
            "",
        ),
        ("half(3) == half(5)", "True"),
        ("half(2) < half(3)", "True"),
    ]);
}

#[test]
fn a_type_of_its_own_wins_over_the_structure() {
    check(&[
        ("type Q(n: Int)", ""),
        ("fn compare(x: Q, y: Q) -> Ordering { Greater }", ""),
        ("fn show(q: Q) -> Str { \"a Q\" }", ""),
        ("Q(n: 1).compare(Q(n: 2))", "Greater"),
        ("Q(n: 1) < Q(n: 2)", "False"),
        ("Q(n: 3).show()", r#""a Q""#),
    ]);
}

#[test]
fn maps_have_no_order() {
    // §19.11: maps and sets fit no `Ordered`, nor does what holds one.
    let mut r = repl();
    let out = r.eval_input(r#"["a": 1].compare(["a": 1])"#).unwrap_err();
    assert!(out.contains("no function `compare` takes"), "{out}");
}

#[test]
fn lists() {
    check(&[
        ("let xs = [3, 1, 2]", ""),
        ("xs.count()", "3"),
        ("let none: List[Int] = []", ""),
        ("none.isEmpty()", "True"),
        ("xs.get(5)", "Empty"),
        ("xs.get(-1)", "Empty"),
        ("xs.first()", "3"),
        ("xs.last()", "2"),
        ("xs.append(4)", "[3, 1, 2, 4]"),
        ("xs.prepend(0)", "[0, 3, 1, 2]"),
        ("xs + [9]", "[3, 1, 2, 9]"),
        ("xs.insert(1, 7)", "[3, 7, 1, 2]"),
        ("xs.insert(3, 7)", "[3, 1, 2, 7]"),
        ("xs.set(0, 8)", "[8, 1, 2]"),
        ("xs.remove(1)", "[3, 2]"),
        ("xs.slice(1..2)", "[1, 2]"),
        ("xs.take(2)", "[3, 1]"),
        ("xs.take(9)", "[3, 1, 2]"),
        ("xs.drop(1)", "[1, 2]"),
        ("xs.drop(9)", "[]"),
        ("xs.reverse()", "[2, 1, 3]"),
        ("xs", "[3, 1, 2]"),
        ("xs.sort()", "[1, 2, 3]"),
        (
            r#"["bb", "a", "ccc", "d"].sortBy { s -> s.byteCount() }"#,
            r#"["a", "d", "bb", "ccc"]"#,
        ),
        ("xs.sortWith { a, b -> compare(b, a) }", "[3, 2, 1]"),
        ("xs.indexOf(2)", "2"),
        ("xs.indexOf(5)", "Empty"),
        ("xs.contains(1)", "True"),
        ("[1, 2, 1, 3].unique()", "[1, 2, 3]"),
        (
            r#"xs.zip(["a", "b"])"#,
            r#"[(first: 3, second: "a"), (first: 1, second: "b")]"#,
        ),
        (
            "xs.indexed()",
            "[(index: 0, value: 3), (index: 1, value: 1), (index: 2, value: 2)]",
        ),
        ("[1, 2, 3, 4, 5].chunks(2)", "[[1, 2], [3, 4], [5]]"),
    ]);
}

#[test]
fn collectors() {
    check(&[
        ("let xs = [3, 1, 2]", ""),
        ("xs.map { x -> x * 2 }", "[6, 2, 4]"),
        ("xs.filter { x -> x > 1 }", "[3, 2]"),
        ("let ys: List[Int] = xs.flatMap { x -> [x, x] }", ""),
        ("ys", "[3, 3, 1, 1, 2, 2]"),
        ("xs.fold(0) { acc, x -> acc + x }", "6"),
        ("xs.find { x -> x < 3 }", "1"),
        ("xs.find { x -> x > 5 }", "Empty"),
        ("xs.any { x -> x > 2 }", "True"),
        ("xs.all { x -> x > 2 }", "False"),
        ("xs.count { x -> x > 1 }", "2"),
        ("xs.min()", "1"),
        ("xs.max()", "3"),
        ("let none: List[Int] = []", ""),
        ("none.max()", "Empty"),
        (r#"["bb", "a"].minBy { s -> s.byteCount() }"#, r#""a""#),
        (r#"["bb", "a"].maxBy { s -> s.byteCount() }"#, r#""bb""#),
        ("xs.sum()", "6"),
        ("[1.5, 2.5].sum()", "4.0"),
        (
            "[1, 2, 3, 4].groupBy { x -> x % 2 }",
            "[0: [2, 4], 1: [1, 3]]",
        ),
        ("(1..5).map { n -> n * n }", "[1, 4, 9, 16, 25]"),
        ("(1..10).filter { n -> n % 3 == 0 }", "[3, 6, 9]"),
        ("(1..4).fold(0) { a, n -> a + n }", "10"),
        ("(1..4).contains(3)", "True"),
        ("(1..3).toList()", "[1, 2, 3]"),
    ]);
}

#[test]
fn maps_and_sets() {
    check(&[
        (r#"let m = ["a": 1, "b": 2]"#, ""),
        ("m.count()", "2"),
        (r#"m.get("a")"#, "1"),
        (r#"m.has("c")"#, "False"),
        (r#"m.set("c", 3)"#, r#"["a": 1, "b": 2, "c": 3]"#),
        (r#"m.remove("a")"#, r#"["b": 2]"#),
        (
            r#"m.change("a") { v -> v.then { n -> n + 10 } }"#,
            r#"["a": 11, "b": 2]"#,
        ),
        (r#"m.change("a") { v -> Empty }"#, r#"["b": 2]"#),
        ("m.keys()", r#"["a", "b"]"#),
        ("m.values().sort()", "[1, 2]"),
        (
            "m.entries().sortBy { e -> e.key }",
            r#"[(key: "a", value: 1), (key: "b", value: 2)]"#,
        ),
        (
            r#"m.merge(["b": 20, "z": 26])"#,
            r#"["a": 1, "b": 20, "z": 26]"#,
        ),
        (
            r#"m.merge(["b": 20]) { k, a, b -> a + b }"#,
            r#"["a": 1, "b": 22]"#,
        ),
        ("m.mapValues { v -> v * 100 }", r#"["a": 100, "b": 200]"#),
        ("m.filter { k, v -> v > 1 }", r#"["b": 2]"#),
        (
            r#"[(key: "x", value: 1), (key: "x", value: 2)].toMap()"#,
            r#"["x": 2]"#,
        ),
        ("let s: Set[Int] = [1, 2, 3]", ""),
        ("s.count()", "3"),
        ("s.contains(2)", "True"),
        ("s.insert(4)", "[1, 2, 3, 4]"),
        ("s.remove(1)", "[2, 3]"),
        ("s.union([9])", "[1, 2, 3, 9]"),
        ("s.intersection([2, 3, 4])", "[2, 3]"),
        ("s.difference([2])", "[1, 3]"),
        ("s.isSubset([1, 2, 3, 4])", "True"),
        ("s.filter { x -> x > 1 }", "[2, 3]"),
        ("s.map { x -> x * 10 }.sort()", "[10, 20, 30]"),
        ("[1, 1, 2].toSet()", "[1, 2]"),
    ]);
}

#[test]
fn positions_outside_a_list_trap() {
    let mut r = repl();
    for input in [
        "[1].set(1, 0)",
        "[1].remove(-1)",
        "[1].insert(2, 0)",
        "[1, 2].slice(1..2)",
    ] {
        let out = r.eval_input(input).unwrap().render();
        assert!(out.contains("trap: index out of range"), "{input}: {out}");
    }
}

#[test]
fn numbers_in_bytes() {
    check(&[
        ("let b = bytes([1, 2, 3, 255])", ""),
        ("b", r#"b"\x01\x02\x03\xff""#),
        ("b.readUInt8(3)", "255"),
        ("b.readInt8(3)", "-1"),
        ("b.readUInt16(0, Little)", "513"),
        ("b.readUInt16(0, Big)", "258"),
        ("b.readInt32(0, Big)", "16909311"),
        ("b.readUInt32(1, Big)", "Empty"),
        ("b.readUInt8(-1)", "Empty"),
        ("b.writeUInt16(1, 4660, Big)", r#"b"\x01\x124\xff""#),
        ("let z = bytes([0, 0, 0, 0, 0, 0, 0, 0])", ""),
        (
            "z.writeFloat64(0, 1.5, Little).readFloat64(0, Little)",
            "1.5",
        ),
        ("z.writeFloat32(0, 0.25, Big).readFloat32(0, Big)", "0.25"),
        ("z.writeInt64(0, -2, Little).readInt64(0, Little)", "-2"),
        (
            "z.writeUInt64(0, 18446744073709551615, Big).readUInt64(0, Big)",
            "18446744073709551615",
        ),
        (r#"Int8.parse("-128")"#, "-128"),
        (r#"Int8.parse("128")"#, r#"ParseError(text: "128")"#),
        (r#"UInt8.parse("ff", base: 16)"#, "255"),
        (r#"UInt32.parse("-1")"#, r#"ParseError(text: "-1")"#),
        (
            r#"UInt64.parse("18446744073709551615")"#,
            "18446744073709551615",
        ),
        (
            r#"UInt64.parse("18446744073709551616")"#,
            r#"ParseError(text: "18446744073709551616")"#,
        ),
    ]);
}

#[test]
fn a_write_past_the_end_traps() {
    let mut r = repl();
    let out = r
        .eval_input("bytes([1]).writeUInt16(0, 1, Big)")
        .unwrap()
        .render();
    assert!(out.contains("trap: index out of range"), "{out}");
}
