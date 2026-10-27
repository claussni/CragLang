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
            wrong.push(format!("{input}\n  expected {expected}\n  shown    {}", shown.trim_end()));
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
        (r#"s.indexOf(",").then { at -> s.substring(before: at) }"#, r#""Grüße""#),
        (r#"s.indexOf("x")"#, "Empty"),
        (r#"s.lastIndexOf("r").then { at -> s.substring(from: at) }"#, r#""rag""#),
        (r#"s.substring(from: s.start(), before: s.end())"#, r#""Grüße, Crag""#),
        (r#"s.codePointAt(s.start())"#, "'G'"),
        (r#"s.after(s.start()).then { at -> s.codePointAt(at) }"#, "'r'"),
        (r#"s.before(s.start())"#, "Empty"),
        (r#"s.after(s.end())"#, "Empty"),
        (r#"s.indexOf("ü").then { at -> s.after(at) }.then { at -> s.substring(from: at) }"#, r#""ße, Crag""#),
        (r#"s.indexOf("r", from: s.indexOf("C").orElse(s.start())).then { at -> s.substring(from: at) }"#, r#""rag""#),
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
        (r#"Int.parse("99999999999999999999")"#, r#"ParseError(text: "99999999999999999999")"#),
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
