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

use crag_db::RootDatabase;
use crag_hir::{ModuleId, Previous, Program, SourceFile, check_shadowing};

/// Each redeclared name with the line of the redeclaration and of what
/// had the name first.
fn redeclarations(text: &str) -> Vec<String> {
    let db = RootDatabase::new();
    let core = ModuleId::new(
        &db,
        "std.core".to_string(),
        SourceFile::new(&db, "pub type Int\npub fn print(s: Str) {}".to_string()),
    );
    let module = ModuleId::new(
        &db,
        "app".to_string(),
        SourceFile::new(&db, text.to_string()),
    );
    let program = Program::new(&db, vec![core, module]);
    let line = |offset: u32| text[..offset as usize].matches('\n').count() + 1;
    check_shadowing(&db, program, module)
        .iter()
        .map(|r| {
            let previous = match &r.previous {
                Previous::Local(range) => format!("line {}", line(range.start)),
                Previous::Item(id) => format!("item {}", id.module(&db).path(&db)),
            };
            format!(
                "{} at line {}, first {previous}",
                r.name,
                line(r.range.start)
            )
        })
        .collect()
}

#[test]
fn nested_scopes_may_not_redeclare() {
    let text = r#"fn f(a: Int, b: Int = a) -> Int {
  let c = a
  if c > 0 {
    let a = 1
    var c = 2
  }
  for (a, d) in pairs { d }
  xs.map { b -> b }
  case a {
    Some(value: c) -> c
    x: Shape -> x
  }
  fn local(c: Int) -> Int { local(c) }
  fn f() {}
}
"#;
    assert_eq!(
        redeclarations(text),
        [
            "a at line 4, first line 1",
            "c at line 5, first line 2",
            "a at line 7, first line 1",
            "b at line 8, first line 1",
            "c at line 10, first line 2",
            "c at line 13, first line 2",
        ]
    );
}

#[test]
fn siblings_and_later_declarations_may_reuse_a_name() {
    let text = r#"fn f() {
  { let a = 1 }
  { let a = 2 }
  xs.map { x -> x }
  ys.map { x -> x }
  case v {
    Some(value: n) -> n
    Other(value: n) | Third(value: n) -> n
  }
  let x = 3
}
fn g(x: Int) -> Int { x }
test "t" { let x = 1 }
"#;
    assert_eq!(redeclarations(text), Vec::<String>::new());
}

#[test]
fn module_values_and_types_are_in_scope_but_functions_are_not() {
    let text = r#"type Point(x: Int)
let limit = 10
embed logo: Bytes from "logo.png"
fn area(p: Point) -> Int {
  let limit = 1
  let Point(x) = p
  let area = 2
  let print = 3
  let (logo, Int) = pair
  let [first, ..Point] = list
  // At the top of an arm a bare name is a type or tag, never a binding.
  case p { limit -> 0 }
}
"#;
    assert_eq!(
        redeclarations(text),
        [
            "limit at line 5, first item app",
            "logo at line 9, first item app",
            "Point at line 10, first item app",
        ]
    );
}

#[test]
fn a_pattern_binds_each_name_once() {
    let text = r#"fn f() {
  let (a, a) = pair
  { x, x -> x }
  case v {
    A(n) | B(n) -> n
  }
}
"#;
    assert_eq!(
        redeclarations(text),
        ["a at line 2, first line 2", "x at line 3, first line 3"]
    );
}
