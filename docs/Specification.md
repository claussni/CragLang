# The Crag Language Specification — Working Draft

Sep 28, 2026 · @Ralf Claußnitzer

This is working draft 0.1 of Crag, a fast, type-safe, REPL-friendly language: immutable by default, structurally typed, statically dispatched, with strictly structured concurrency. It records every design decision taken so far; syntax marked *provisional* is a placeholder until settled.

## Contents

1. [Introduction](#1-introduction) — goals, status, notation, conformance
2. [Lexical structure](#2-lexical-structure) — comments, newlines, literals, prefixes
3. [Types](#3-types) — primitives, records, unions, parents, modifiers, clauses, markers
4. [Forms and generics](#4-forms-and-generics) — forms, bounds, `where`, dispatch
5. [Declarations and bindings](#5-declarations-and-bindings) — `let`, `var`, `ref`, `ext`, functions, overloading
6. [Expressions](#6-expressions) — blocks, operators, UFCS, closures, partial application, updates, options, patterns
7. [Control flow](#7-control-flow) — `if`, narrowing, `case`, `for`, ranges
8. [Errors and type mappings](#8-errors-and-type-mappings) — error unions, `pass`, traps, `discard`, prefixes
9. [Shared state: ref and ext](#9-shared-state-ref-and-ext) — access functions, optimistic updates, transactions
10. [Concurrency](#10-concurrency) — structured tasks, combinators, cancellation, streams
11. [Signals and lifecycle](#11-signals-and-lifecycle) — `emit`, `on`, `Dispose[T]`, debugging
12. [Collections and strings](#12-collections-and-strings) — lists, maps, grids, slices, `Str`, `CodePoint`
13. [Memory model](#13-memory-model) — reference counting, runtime structures, disposal
14. [Modules and packages](#14-modules-and-packages) — imports, merging, versions
15. [Runtime I/O](#15-runtime-io) — abstract I/O types, cryptography
16. [Foreign function interface](#16-foreign-function-interface) — C imports, pointers, threading, native versions
17. [The REPL](#17-the-repl) — discovery, rebind
18. [Introspection and code transport](#18-introspection-and-code-transport) — generics over fields, type functions, compile-time evaluation, `Expr`, codecs
19. The standard library — compiler-owned types, the prelude, module layout
20. Runtime and tooling — processes, hot reload, debugger, registries, commands, release builds

Appendices: [A Glossary](#appendix-a-glossary) · [B Reserved words and markers](#appendix-b-reserved-words-and-standard-markers) · [C Open questions](#appendix-c-open-questions-and-provisional-syntax)

## 1 Introduction

Crag is a general-purpose, compiled language that stays pleasant to explore interactively. Its mascot is the mountain goat: sure-footed on narrow ground.

### 1.1 Design goals

1. **Immutable first.** Values never change. Updates produce new versions backed by efficient persistent data structures.
2. **Mutation is visible.** Every mutable thing is a distinct binding kind (`var`, `ref`, `ext`) that the type system and the reader can see.
3. **Structural and static.** Types are identified by structure; dispatch is resolved at compile time from inferred concrete types.
4. **Correct values.** Type conditions, the compiler and the runtime enforce valid values, in that order.
5. **Maximal, structured concurrency.** Every task lives inside a scope that awaits it. There are no detached tasks.
6. **REPL-friendly.** The same rules hold in the REPL as in files; the REPL adds discovery, not exceptions.
7. **Not a scientific language.** Collections are practical (lists, maps, 2D grids), not n-dimensional arrays.

### 1.2 Status of this document

This draft collects decisions made so far. Normative text states what is decided. Text marked **Provisional** shows placeholder syntax used only so examples can be written; Appendix C lists every such item.

How the toolchain is built is recorded, non-normatively, in the tab Compiler architecture.

### 1.3 Notation

Grammar fragments use EBNF: `?` optional, `*` zero or more, `+` one or more, `|` alternatives, quoted strings are terminals.

```
let_decl   = "let" pattern (":" type)? "=" expr
```

Code examples are Crag unless labelled otherwise. `// ⇒` shows a result, `// error:` shows a compile error.

A function signature without a body is shorthand: the function is declared with that signature and its body is omitted. In source, only intrinsics may lack a body (§19.2).

### 1.4 Conformance terms

*Must* and *must not* are requirements on programs and implementations. *Should* is a strong recommendation. A program that violates a *must* is ill-formed and must be rejected at compile time unless the text says the check happens at run time.

> **Hint.** When a rule reads as unusually strict, look for its reason in the design goals. Most restrictions exist so the compiler can prove immutability or safe concurrency.

## 2 Lexical structure

### 2.1 Source text

A source file is UTF-8 text. Each file is exactly one module (Chapter 14).

### 2.2 Comments

Crag has `//` line comments and `/* ... */` block comments. There is no separate documentation-comment syntax: a comment placed directly above a declaration documents that declaration.

```
// A point on the drawing canvas.
type Point(x: Int, y: Int)

/* Block comments may span
   several lines. */
```

> **Hint.** Tooling (the REPL, doc generators) picks up the comment directly above a declaration. Leave a blank line between a comment and a declaration if the comment is not meant as documentation.

### 2.3 Statement termination

A newline terminates a statement, except:

- inside parentheses and brackets, where newlines are whitespace, so arguments may span lines;
- after a line that ends in a binary operator, `,` or `->`;
- before a line that begins with `.`, `?.` or `else`.

A line that begins with a binary operator does not continue the previous line, because `-x` on its own line is a statement; a broken expression keeps the operator at the end of the line. The `{` of a trailing closure must be on the line of its call; on a new line it starts an ordinary block.

A line that begins with `.` continues the previous expression, which allows fluent chains:

```
let names = people
  .filter { p -> p.age >= 18 }
  .map { p -> p.name }
```

### 2.4 Identifiers

Identifiers start with a letter or `_` followed by letters, digits or `_`. By convention types, forms and markers are `UpperCamelCase`; bindings and functions are `lowerCamelCase`. A lone `_` is the placeholder (ignored pattern, partial-application hole, or “any type” in type position).

### 2.5 Keywords

The reserved words are listed in Appendix B. Boolean operators are keywords: `and`, `or`, `not`. A keyword may still name a record field or a named argument, because there it always stands before `:` or after `.` (for example `and:` in §18.11); it can never name a binding.

### 2.6 Literals

| Kind | Examples | Notes |
| --- | --- | --- |
| Integer | `0`, `42`, `1_000_000` | Typed by context, `Int` by default; a value that does not fit its type is a compile error |
| Float | `3.14`, `1e-9` | Type `Float`, finite IEEE 754 (§3.1.4) |
| String | `"hello"` | Type `Str`, UTF-8 |
| Unit | `()` | The empty record, type `()` |
| Record | `(x: 1, y: 2)` | Anonymous record, named fields only |
| List | `[1, 2, 3]`, `[]` | Type `List[T]` |
| Map | `["a": 1, "b": 2]`, `[:]` | Type `Map[K, V]`; `[:]` is the empty map |
| Grid | `[1, 2; 3, 4]` | Type `Grid[T]`; `;` separates rows |
| Range | `1..10` | `Range[T]`, inclusive on both ends; `1..` is open, `RangeFrom[T]` (§7.4) |

A `CodePoint` literal uses single quotes: `'a'`. Single quotes are reserved for code points. A byte literal is a string-like literal with a `b` prefix, typed `Bytes`: `b"\x00\xff"`. A decimal literal such as `19.99` is a `Fixed[S]` when the expected type is `Fixed`, and a `Float` otherwise; more decimals than the scale `S` allows is a compile error. A decimal literal at an end of a range is a `Fixed[S]` whose scale is exactly the number of decimals written, so `0.00..2.00` is a `Range[Fixed[2]]` (§7.4).

A multi-line string literal is enclosed in triple quotes. The line break after the opening `"""` and the one before the closing `"""` are not part of the value, and the indentation common to all content lines is stripped, so the literal can follow the surrounding code. Interpolation and escapes work as in ordinary string literals.

```
let query = """
    SELECT name, total
    FROM orders
    WHERE id = {orderId}
    """
```

String and code-point literals accept the escapes `\n`, `\t`, `\r`, `\0`, `\\`, `\"` and `\'`, and `\u{…}` with one to six hexadecimal digits naming a Unicode scalar value. Byte literals also accept `\xHH`; a `Str` does not, since it could produce invalid UTF-8. An unknown escape is a compile error. Literal braces are written `{{` and `}}`.

Integer literals may be written in hexadecimal, binary or octal: `0x1F`, `0b1010`, `0o755`, with `_` as a separator (`0xFF_FF`). Like decimal integers they take their type from context, so `let mask: UInt8 = 0b1111_0000` is valid; a value that does not fit its type is a compile error.

### 2.7 Operators and punctuation

`..` is both the range syntax (§7.4) and the spread marker; context always decides which. `->` separates closure parameters from the body and function parameters from the return type. `?.` is optional chaining. `e[...]` is bracket application (§6.5).

### 2.8 Prefixes

A *prefix* is a user-declared token placed before an expression that applies a type-mapping function (§8.5). Lexing rules:

1. A symbol prefix must not start with a binary operator character sequence.
2. The longest matching prefix wins.
3. A word prefix (for example `disc`) is reserved as a keyword only in modules that import it.
4. A prefix can be declared only once across all packages; the standard library’s prefixes are fixed for everyone.

## 3 Types

Crag is structurally typed: a type is identified by its shape, and a named type by its name plus its shape. Tags and types are one concept, so there is no enum-case dot syntax.

### 3.1 Primitive types

| Type | Meaning | Key rules |
| --- | --- | --- |
| `Int` | Signed 64-bit integer on every platform | Overflow traps; `+%` style operators wrap |
| `Float` | IEEE 754 binary float, finite values only | Overflow and division by zero trap; partial functions of `std.math` return `Float \| NaN` (§3.1.4); `Ordered` |
| `Fixed[S]` | Decimal fixed point, `S` fractional digits | Multiplying or dividing two fixed values requires explicit rounding |
| `Bool` | `type Bool = True \| False` | An ordinary union of two tag types |
| `Str` | UTF-8 text | No integer indexing, no list interface (§12.5) |
| `CodePoint` | One Unicode scalar value | Examine and construct characters |
| `()` | Unit, the empty record | The value of blocks that produce nothing |

#### 3.1.1 Integer overflow

Arithmetic overflow on `Int` traps and raises a catchable runtime error, as do division and remainder by zero. Traps are handled by trap handlers (§8.3.1). Overflow in an expression the compiler can evaluate is a compile error.

```
let big = 9_223_372_036_854_775_807 + 1  // error: constant overflow
let wrapped = a +% b  // wraps silently, never traps
```

#### 3.1.2 Fixed-point arithmetic

```
let price: Fixed[2] = 19.99
let total = price * 3  // Fixed * Int: exact
let share = (price * rate).roundHalfEven(to: 2)  // Fixed * Fixed: rounding required
```

Each rounding mode is its own function, taking the target scale: `roundHalfEven(to:)`, `roundHalfUp(to:)`, `roundUp(to:)` (away from zero), `roundDown(to:)` (toward zero), `floor(to:)` and `ceil(to:)`.

#### 3.1.3 Sized integers

`Int` is 64 bits wide on every platform, so a program overflows at the same values everywhere. For narrower or unsigned values the prelude has the compiler-owned types `Int8`, `Int16`, `Int32`, `UInt8`, `UInt16`, `UInt32` and `UInt64`.

- They follow the rules of `Int` (§3.1.1): overflow traps, the wrapping operators never trap, and overflow the compiler can evaluate is a compile error. For an unsigned type, going below zero is an overflow.
- There are no implicit conversions: `Int + Int32` is a compile error. Conversions use the constructor style. One that may not fit returns an error union (`Int32(n)` for an `Int` n), one that always fits returns the plain type (`Int(x)` for an `Int32` x), and `trunc` wraps explicitly.
- Literals take their type from context: `let b: UInt8 = 255` is valid, and `256` in its place is a compile error.
- `UInt64` values above the largest `Int` do not fit in it, so converting a `UInt64` to `Int` returns an error union.
- The runtime may store lists of sized integers packed; a `List[UInt8]` takes one byte per element.

The `C…` types of `std.c` (Ch. 16) exist for the C calling convention, not for general use.

#### 3.1.4 Floating point

A `Float` is a finite IEEE 754 double: never ±∞ and never NaN. Where IEEE 754 would produce an infinity, Crag traps; where it would produce NaN, the operation returns the prelude tag `type NaN`, and its result type says so.

- Overflow traps, as on `Int` (§3.1.1): a result whose magnitude exceeds `Float.max` raises the same catchable runtime error, and overflow the compiler can evaluate is a compile error. So is a literal beyond `Float.max`. Underflow does not trap: a result too small to represent becomes a subnormal or zero.
- Division and remainder by zero trap, whatever the dividend. So the arithmetic operators of two `Float`s return a `Float`, as do `negate`, `abs`, `min`, `max`, `floor`, `ceil`, `round`, the comparisons and `Float(n)` from an integer.
- A function of `std.math` whose domain is not all of `Float` returns `Float | NaN`, and `NaN` outside its domain: `sqrt(-1.0)`, `log(-1.0)`, `asin(2.0)`, `pow(-8.0, 0.5)`. At a pole, where the IEEE result is infinite, as for `log(0.0)` or `pow(0.0, -1.0)`, it traps. `Float.fromBits` returns `NaN` for the bit patterns of ∞ and NaN.
- `x.number()` turns a `Float | NaN` into a `Float` and traps on NaN. `case` and `is` narrow it without a trap. The arithmetic operators take only `Float`s, so a `NaN` is handled where it arises.
- `Float` is totally ordered and fits `Ordered` (§6.2), with `Float.min` its least value and `Float.max` its greatest. `-0.0` and `0.0` compare `Equal` and hash alike, so a `Float` can be a map key or a set member.
- `Float | NaN` costs nothing: `NaN` keeps its IEEE bit patterns, the union is one double, and `x is NaN` is the hardware check. `NaN` is one value; its payload bits are not observable, so `NaN == NaN` is `True`, as for every tag.
- `Float.parse` never returns ∞ or NaN: `"inf"`, `"NaN"` and `"1e400"` are `ParseError`s.

The compiler may check a sequence of operations once, through the hardware's sticky overflow flag, before their result is stored, passed, returned or compared. The trap then reports the expression rather than the operation.

```
fn area(r: Float) -> Float { 3.14159 * r * r }  // traps only if it overflows
fn hypot(a: Float, b: Float) -> Float { sqrt(a * a + b * b).number() }
let angle = case asin(ratio) {
  NaN -> 0.0
  a -> a
}
```

### 3.2 Tag types

A declaration without fields and without `=` introduces a tag type with exactly one value, written by its name.

```
type Done
type Empty[T]
```

### 3.3 Named record types

```
type Point(x: Int, y: Int)
let p = Point(x: 1, y: 2)
```

Type identity is **name + fields**. Two independent declarations with the same name and the same fields denote the same type; indistinguishable types from different modules merge silently.

### 3.4 Anonymous records

`(x: Int, y: Int)` is an anonymous record type, identified by its fields alone. Field order does not matter for identity. There are no positional tuples; `()` is the unit type.

```
let a: (x: Int, y: Int) = (y: 2, x: 1)  // same type, order irrelevant
```

### 3.5 Aliases

`type X = T` makes `X` a fully interchangeable name for `T`. It is distinct from the record form `type X(fields)`.

### 3.6 Unions

A union lists alternatives with `|`. Unions are how Crag spells enumerations, options and error results.

A value of a union type belongs to **exactly one** member, because a value has one concrete type. In a union of function types each member is parenthesized (§3.7): `((Str) -> T) | ((Bytes) -> T)`.

```
type Option[T] = T | Empty[T]
type Shape = Circle | Rect
type Lookup = Int | NotFound
```

#### 3.6.1 Overlapping members

Two members *overlap* when some value could belong to both: one spreads the other, an open record accepts the other's fields, or a generic member is instantiated to another member's type. Identical members are not overlap; `A | A` is `A`.

1. Overlap in a union written in source is a compile error, including containment such as `NotFound | LookupError`.
2. Overlap created by instantiating a generic union is a compile error at the instantiation.
3. An inferred union (for example a function's error union) absorbs a member that another member already contains. Absorption never widens: `NotFound | Timeout` is never replaced by a common parent.

Absorption loses no values. A `LookupError` value can already hold a `NotFound`, which stays matchable:

```
case result {
  n: Int -> use(n)
  NotFound -> "missing"
  LookupError -> "other lookup failure"
}
```

`Empty` carries a type parameter so that options nest without overlap. `Option[Option[Int]]` is `Int | Empty[Int] | Empty[Option[Int]]`: "key missing" and "present but empty" stay distinct. Context typing infers the parameter, so `Empty` is usually written bare; a bare `Empty` pattern that could match several levels is a compile error and must name its level.

```
let cache: Map[Str, Option[Int]] = ["a": Empty]

case cache["a"] {
  Empty[Option[Int]] -> "missing"
  Empty[Int] -> "present, empty"
  n: Int -> "value {n}"
}
```

`orElse` gives an option a fallback. One overload takes a plain value; the other takes a `Lazy` fallback, computed only when the option is `Empty`. Nothing is wrapped implicitly (§6.10), so `lazy` is written exactly where the cost matters:

```
fn orElse[T](o: Option[T], fallback: T) -> T
fn orElse[T](o: Option[T], fallback: Lazy[T]) -> T

let name = p.name.orElse(u.name)
let conf = p.conf.orElse(lazy loadDefault())
```

> **For users.** An inferred type may name fewer members than the calls that produced it, because contained members are absorbed. The REPL and compiler diagnostics should show absorbed members next to an inferred type (e.g. `LookupError (absorbs NotFound)`), and the error for a written overlap should name the containing member.

#### 3.6.2 Runtime type of union values

Generic functions are specialized for each concrete instantiation, so a type parameter is always a known type inside its function and types are otherwise a compile-time matter. The one exception is a union value: its runtime tag is its complete type, type arguments included. Members that differ only in their type arguments therefore stay distinguishable, even when the value itself carries no hint, such as an empty list.

```
fn describe(x: List[Int] | List[Str]) -> Str {
  case x {
    List[Int] -> "numbers"
    List[Str] -> "text"
  }
}
```

The same complete type is what code transport checks received values against (§18.8) and what the REPL shows as a value's type. There is no type erasure.

#### 3.6.3 Never

`Never` is the empty union: it has no members and no values. Like any contained member it is absorbed, so `T | Never` is `T`. It is the return type of a function that never returns normally, such as one that always traps or runs a loop without end.

`Never` is always written, never inferred. The compiler checks a declared `Never` conservatively: a path that returns normally is an error. It never has to prove termination.

### 3.7 Function types

In a function type, everything after `->` is the return type. A function type inside a union needs parentheses.

```
type Parse = (Str) -> Int | ParseError  // returns a union
type Handler = ((Event) -> ()) | Ignore  // union containing a function type
```

### 3.8 Parent types and subtyping

A named type may amend exactly one parent by spreading it as the first entry of its field list. A type is a subtype only if it spreads its parent explicitly; structure alone never creates a subtype.

```
type Shape(pos: Point)
type Circle(..Shape, r: Float)
type Blip(..(pos: Point), r: Float)  // anonymous parent structure also works
```

The structure identifies the amended type; naming the parent is sugar and good convention. At most one spread is allowed per declaration.

#### 3.8.1 Extra fields (row polymorphism)

Accepting records with extra fields is opt-in and must be requested explicitly at the use site.

A trailing `..` in a record type accepts records with any further fields. A named type is opened by spreading it into such a record: `(..Point, ..)` accepts `Point`'s fields plus any others.

```
fn norm(p: (x: Float, y: Float, ..)) -> Float { sqrt(p.x * p.x + p.y * p.y).number() }
fn label(p: (..Point, ..)) -> Str { "{p.x}, {p.y}" }
```

To change a field of an open record without losing its type, use `update` (§6.7.1).

### 3.9 Declaration modifiers

Modifiers appear in this fixed order (outside-in):

```
pub opaque type Name[T](..Parent, fields)
pub distinct type Name[T](..Parent, fields)
```

- `pub` exports the type from its module.
- `opaque` hides the whole type (its fields and constructor) outside its module. There is no per-field hiding. `opaque` implies `distinct`: a type that reveals nothing cannot merge by accident with a same-shaped declaration. Writing `opaque distinct` is a compile error. Anonymous records cannot be opaque.
- `distinct` makes the type nominal: a same-shaped declaration elsewhere does not merge with it. Use it for official domain types and field-less category parents.

### 3.10 Clauses

After the field list, clauses appear in this order:

1. `where` requirements on type parameters
2. `is` markers
3. `where` value conditions
4. `on` lifecycle handlers (§11.4)

```
pub distinct type Percent(value: Int)
  is Solid
  where value >= 0 and value <= 100

pub opaque type Db(handle: CPtr[DbHandle])
  on Dispose closeDb
```

Several markers or conditions are grouped in braces, `is { Solid, Secret }`, with items separated by commas, newlines or both. Several conditions must all hold; they are checked in order and the first failure is reported. A condition may be named with the label syntax of records, `name: expr`:

```
pub distinct type Percent(value: Int)
  is Solid
  where {
    nonNegative: value >= 0
    atMost100: value <= 100
  }
```

A failed condition reports its name, or its source text when it has none, together with its origin: a conversion returns `Invalid(condition: "atMost100", origin: …)` (§3.10.1), and a trap is `ConditionFailed(condition: "balance >= -limit", …)` (§8.3). Naming is optional; it makes messages stable and readable. A type that needs its own error types keeps a custom value checker (§3.10.1).

#### 3.10.1 Value conditions (invariants)

Validation logic belongs in the type definition. Constructing a value that fails its `where` condition at runtime traps with `ConditionFailed` (§8.3); a failure the compiler can see is a compile error. Code that must handle bad input checks it first: a conversion to a conditioned alias returns `Invalid` (below), and a type may provide its own value checker that returns custom errors. Modules provide correct parsers; the type system, compiler and runtime enforce correct values, in that order.

A type alias may carry a condition too, which makes a checked subset of an existing type. Inside the condition, `this` is the whole value.

```
type Percent = Int where this >= 0 and this <= 100
type SqlExpr[F] = Expr[F] where sql.accepts(this)
```

A value enters the alias only through a check. At runtime this is an explicit conversion, `Percent(n)`, which returns `Percent | Invalid`; a failed check is a value, never a trap. A value known at compile time may be passed directly where the alias is expected.

A condition whose inputs are all known at compile time is evaluated at compile time (§18.4), and a failure is a compile error. Literals, constants and closure literals qualify, so `Percent(150)` and an untranslatable closure literal passed as an `SqlExpr` are both rejected where they are written.

### 3.11 Markers

A marker is a type constraint with no definition beyond its name. Markers on a value always come from the value’s type; there are no per-value markers.

| Marker | Meaning |
| --- | --- |
| `Solid` | Values can never produce a runtime error: closures only if they are Pure and capture only Solid values, compile-time validated, runtime safe. Inferred, or asserted with `is Solid`. `where` conditions allowed if they are Solid too. |
| `Pure` | Functions of this type perform no effects (§3.14). |
| `Secret` | Hidden when printed or inspected, barred from signals, constant-time `==`, memory wiped on dispose. |
| `Immediate`, `Deferred` | When the type's `on Dispose` handler runs: at the drop, or later during deferred teardown. Unmarked means `Deferred` (§13.3). |
| `ThreadUnsafe`, `ThreadSafe`, `ThreadBound` | Thread-safety of foreign libraries (§16.4). |
| `Errno` | Opt-in `errno` capture for a foreign function (§16.3). |

A negated marker, `is not F`, forbids a form. The type never fits `F`, defining a function that would make it fit is a compile error in any module, and subtypes inherit the ban. Automatic forms such as `Eq` are switched off the same way. Only declared types can forbid forms; anonymous records cannot.

```
pub distinct type Password(raw: Bytes)
  is { Secret, not Show, not Hash }

pub distinct type UserId(value: Int)
  is not Num
```

### 3.12 Closures that carry refs

A closure that captures a ref, directly or through another closure, *carries* it and is bindings-only, like the ref itself (§9.2): it may be passed as an argument and called, but never stored in a data structure or a ref, and never returned. A closure that only resolves refs it receives as parameters merely has the `ref` effect (§3.14) and is an ordinary value. There is no field marker for closures.

```
fn tally(xs: List[Int]) -> Int {
  ref total = 0
  let add = { n: Int -> total.update(_ + n) }  // carries total
  all { g -> for x in xs { g.start { -> add(x) } } }  // ok: passed
  let jobs = [add]  // error: a closure carrying a ref cannot be stored
  total.use()
}
```

### 3.13 Inference and subtyping

#### 3.13.1 What is written

- Function parameters are always typed.
- A `pub` function states its success type; its errors are inferred (§8.2) and recorded in `api.crag`, so the publishing check sees every change (§20.5).
- A function that is not `pub` may leave its whole return type to inference.
- A recursive function, and each member of a group of mutually recursive functions, states its success type.
- Recursion is judged by what inference needs, not by which calls run. Functions form a recursive group when inferring their success types depends on each other, including through every overload the return-type filter must compare (§5.6.1), even one the call does not choose. As in any recursive group, each member states its success type, even where one written type would already break the cycle; the diagnostic names every member missing one and the call that links them.
- Closure parameters and `let` bindings are inferred from context. Bounds (§4.2) and `Never` (§3.6) are always written.

#### 3.13.2 How inference runs

Inference is local and bidirectional. An expected type flows down into an expression (literals, closures, `Empty`, `lazy`), and the expression's type flows up. Nothing is inferred across function boundaries; a generic call's type parameters come from its arguments and its expected result.

The error unions of a recursive group are inferred by fixpoint: they start empty and grow by the errors the bodies produce until nothing changes. Members only accumulate from a finite set of declared types, so this terminates. The effects of a recursive group are inferred the same way, starting from none; there are only three effects (§3.14).

Where branches meet (`if`/`else`, `case` arms, several `return`s), the result is the union of the branch types, absorbed as in §3.6. There is never a least common parent.

#### 3.13.3 Subtyping

A value of type `S` fits where `T` is expected when:

- `S` spreads `T`, directly or through a chain of parents (§3.8); this holds for `distinct` and `opaque` parents too, so a `NotFound` fits `LookupError` and every signal fits `Signal`;
- `S` and `T` are the same `distinct` or `opaque` type; apart from spreading, such types fit only themselves, by name;
- both are records with the same fields and each field of `S` fits the one of `T`; extra fields fit only where `T` opts in with `..` (§3.8.1);
- both are function types, `T`'s parameters fit `S`'s and `S`'s result fits `T`'s; a `Pure` function fits a function type without `Pure`, never the reverse;
- every member of a union `S` fits some member of `T`;
- both are the same immutable generic type and each argument of `S` fits the one of `T`: `List[Int]` fits `List[Int | Str]`. Ref types are invariant.

#### 3.13.4 Narrowing

Narrowing is flow-sensitive. `x is T` narrows a `let` binding, or a `var` until it is reassigned, to the members fitting `T` where the test holds and to the rest where it does not: in `if` branches, `case` arms (§7.2) and the right operand of `and`. After `if x is E { return … }`, the rest of the block sees `x` without `E`. Refs and fields are never narrowed; bind a field first (`let n = p.name`).

### 3.14 Effects

The language has three effects:

| Effect | Caused by |
| --- | --- |
| `io` | files, network, processes, the clock, randomness, `ext` operations, every C call |
| `ref` | reading or updating a ref (§9.3) |
| `signal` | `emit` (Ch. 11) |

Traps, allocation, non-termination and starting tasks are not effects; a combinator over pure closures is pure. There are no user-defined effects.

A function's effects are the union of its body's effects, including those of everything it calls. They are inferred and never written in a signature; `:help` shows them, and `api.crag` records them for every `pub` function, so gaining an effect is a breaking change (§20.5). The only written form is the restriction `is Pure`: no effects at all.

A function that calls a closure parameter takes on that closure's effects at each call site, so `xs.map(f)` has the effects of `f`, and mapping a pure closure is pure. A stored function value (a record field, a closure in a collection) has no known call site: a plain function type admits every effect, and `is Pure` on the type admits none.

| Context | Effects allowed |
| --- | --- |
| `is Pure` functions, compile-time code (§18.4), type functions (§18.3), codec handlers (§18.9), transported `Expr` bodies (§18.6) | none |
| `atomic` blocks and `update` closures (§9.5) | `ref`, and `signal`, delivered according to `ok`, `fail` and `retry` (§11.2) |
| everywhere else | all |

Two existing rules follow from effects: a closure that resolves refs (§6.4.1) is a closure with the `ref` effect, and a `Lazy[T]` carries its expression's effects, which reading `.value` performs (§6.10).

## 4 Forms and generics

A *form* is a structural requirement set over one or more types. Any types for which the required functions exist satisfy the form automatically; nothing is declared with `impl`.

Types and forms answer different questions. A type says what a value *is*; a form says what can be *done* with a type. Functions are the only link between them:

1. A type has a fixed identity (name + fields, §3.3), and every value has exactly one concrete type.
2. A form never describes a value. It appears only as a bound on a type parameter, or as shorthand for one in parameter or return position (§4.3), so dispatch stays static.
3. A type fits a form when matching functions are visible in scope. Fitting is never declared on the type, so which forms a type fits depends on what is imported.
4. A declared type can restrict fitting from its own side: `is not F` bans a form everywhere, and automatic forms such as `Eq` can be switched off (§3.11).
5. Markers (§3.11) are constraints attached to a type by name; forms are earned through functions.

### 4.1 Form declarations

```
form Sizable[U] {
  size(u: U) -> Int
}

form Convert[A, B] {
  convert(a: A) -> B
}
```

Rules:

1. Every function in a form takes explicitly typed inputs, including the value that other languages call `self`. There is no implicit receiver.
2. A form is a pure requirement set. It must not contain default implementations; the standard library provides defaults as ordinary functions.
3. All type parameters of a form are independent. There are no associated or determined types.
4. Bounds belong on the form’s own type parameters.
5. Because satisfaction is structural, a form’s name has no semantic weight; it names a requirement for the reader.

> **Hint.** The keyword is `form`, not `interface`: multi-parameter structural requirement sets behave differently from the single-receiver interfaces of other languages.

### 4.2 Type parameters and bounds

Bounds on type parameters must always be written out; the compiler never infers a bound.

```
fn largest[T: Ordered](xs: List[T]) -> Option[T] { ... }
```

A named type may also be a bound. `[S: Shape]` admits `Shape` and every type that spreads it (§3.8), and the function is specialized for each, like any type parameter (§3.6.2). This is how type-preserving code over a family is written (§6.7.1). Records related only by shape use an open record type instead (§3.8.1).

A complex bound can be given an alias name and reused.

A bound alias is an empty form with a `where` clause; it needs no syntax of its own:

```
form Keyed[T] where Hash[T], Ordered[T] {}
fn index[K: Keyed, V](entries: List[(key: K, value: V)]) -> Index[K, V]
```

### 4.3 Forms in parameter and return position

A form used as a parameter type is shorthand for an unnamed type parameter bounded by that form. Return types may also be forms.

```
fn store(k: Key, v: Str) -> ()  // same as fn store[K: Key](k: K, v: Str)
```

### 4.4 The `where` clause

Requirements that span several type parameters go in a `where` clause after the signature, not inside the brackets.

```
fn head[C, E](c: C) -> Option[E]
  where First[C, E]
{ first(c) }
```

### 4.5 Compiler-known forms

`Fields[R, T]` holds when every field of record type `R` has type `T`. `_` means any type. It lets combinators accept a record of closures built from named arguments (§10.2).

```
fn all[R](branches: R) -> ... where Fields[R, () -> _]
```

### 4.6 Dispatch

Dispatch is static. The compiler keeps concrete types through inference and resolves every call at compile time. There are no vtables and no packed form values.

#### 4.6.1 Union lifting

When a function is called with a union value and an overload exists for every member, the call dispatches on the value's tag. The compiler generates the `case`, and a missing overload is a compile error.

```
fn area(c: Circle) -> Float { 3.14159 * c.r * c.r }
fn area(r: Rect) -> Float { r.w * r.h }

let shapes: List[Circle | Rect] = [c, r]
let areas = shapes.map(area)  // List[Float]
```

- For each member, the most specific overload is chosen (§5.6.1). The result type is the union of the chosen overloads' results.
- With several union arguments, lifting covers every combination of members, and an overload must exist for each.
- Lifting applies to unions only. A value of a parent type may hold subtypes from other packages, a set that is never closed, so subtypes are still matched with `case`:

```
fn area(s: Shape) -> Float {
  case s {
    c: Circle -> 3.14159 * c.r * c.r
    r: Rect -> r.w * r.h
  }
}
```

### 4.7 Unions of forms

A union of forms is satisfied by fitting **at least one** member; fitting several is allowed. A union of types, by contrast, is satisfied by a value in exactly one member (§3.6).

```
form Hash[T] { hash(x: T) -> Int }
form Ordered[T] { compare(a: T, b: T) -> Ordering }
form Keyable[T] = Hash[T] | Ordered[T]

type Index[K: Keyable, V](entries: List[(key: K, value: V)])

fn lookup[K: Hash, V](ix: Index[K, V], k: K) -> Option[V]  // hash probe
fn lookup[K: Ordered, V](ix: Index[K, V], k: K) -> Option[V]  // binary search
fn lookup[K, V](ix: Index[K, V], k: K) -> Option[V]
  where Hash[K], Ordered[K]  // both: hashing
```

Exclusivity comes from overload resolution, not from the bound. The specificity rule (§5.6.1) picks the combined overload when a type fits both; the module must provide it, because incomparable bounds on one parameter shape require it. Crag has no `xor` constraint.

## 5 Declarations and bindings

Crag has four binding kinds. Each uses a three-letter keyword, and the keyword tells the reader exactly what may change. `embed` (§18.4.1) is not a fifth kind: it is a module-level form of `let` whose value comes from a resource.

| Keyword | Rebindable | Shared across tasks | Access | Typical use |
| --- | --- | --- | --- | --- |
| `let` | No | Yes (immutable value) | Direct | Values and constants |
| `var` | Yes, in its own scope only | Read-only in closures | Direct | Local accumulation |
| `ref` | No (contents change) | Yes, atomically | Through access functions | Shared state, optimistic |
| `ext` | No (contents change) | Yes, with locking | Through access functions | Mutable foreign state, pessimistic |

### 5.1 `let`

`let` binds an immutable value. There is no `const` keyword; `let` covers constants.

```
let limit = 100
let origin: Point = Point(x: 0, y: 0)
```

### 5.2 `var`

`var` is the only binding that can be rebound, and only within the scope that declared it.

```
var total = 0
for x in xs { total = total + x }
```

A closure may read a `var` but must never write it. Reading `var`s inside closures, including concurrent combinator branches, is the common case and is allowed.

```
var count = 0
let inc = { -> count = count + 1 }  // error: var written inside a closure
let show = { -> print("{count}") }  // ok: read only
```

### 5.3 `ref` and `ext`

`ref` binds shared atomic state updated optimistically; `ext` binds external (foreign) state updated under a lock. Both are specified in Chapter 9.

### 5.4 Scoping and names

1. Redeclaring a name already in scope is never allowed. There is no shadowing.
2. Rebinding is only allowed for `var`.
3. A declared function name is not a binding. A binding may share a name with a (possibly imported) function when the compiler can tell the uses apart by type.

```
let x = 1
let x = 2  // error: x is already declared in this scope
```

### 5.5 Module level

Only `let` bindings and embed declarations with `Solid` values are allowed at module level. They are evaluated at compile time or once on first use. There are no top-level `var`, `ref` or `ext` bindings. They are private to their module: `pub` exports only types, forms and functions (§14.1).

### 5.6 Functions

```
fn distance(a: Point, b: Point) -> Float {
  let dx = a.x - b.x
  let dy = a.y - b.y
  sqrt(Float(dx * dx + dy * dy)).number()
}
```

A type name applied to one unnamed argument of another type is a conversion, resolved through `Convert[A, B]` (§4.1): `Float(n)`. Record construction always names its fields, so the two never clash.

#### 5.6.1 Overloading

Functions may be overloaded by their full signature, including the return type. A call is resolved statically from argument types and, where needed, the expected result type.

An overloaded name used as a value rather than called is resolved against the expected type. If that type is a union of function types and the name fits more than one member, it is a compile error. Overloads that differ only in form bounds follow §4.7.

```
fn parse(s: Str) -> Int | ParseError { ... }
fn parse(s: Str) -> Float | ParseError { ... }
let n: Int | ParseError = parse("42")
```

**Specificity.** When several candidates from the same module are viable, the most specific wins. Candidate A is more specific than B if every call A accepts, B also accepts, but not the reverse. Per parameter:

1. A concrete type beats a type parameter.
2. A subtype beats its parent.
3. A strictly larger requirement set beats a smaller one. Bounds in brackets and `where` requirements form one set; a union bound is weaker than each of its members.

A must be at least as specific on every parameter and strictly more specific on one. The return type never ranks; it only filters candidates by the expected type.

```
fn describe[T: Show](x: T) -> Str  // A
fn describe[T: Show](xs: List[T]) -> Str  // B
fn describe(xs: List[Int]) -> Str  // C

describe(3)  // A: the only viable candidate
describe(["a", "b"])  // B: beats A
describe([1, 2])  // C: beats B and A
```

**Ambiguity is fixed where it is created.** All resolution is static, so every ambiguity is a compile error; there is no call-site hint.

1. Within a module, two overloads with the same parameter shape and incomparable bounds must come with their combined overload, or the module fails to compile. A call therefore never meets an ambiguity inside one module's overload set.
2. Candidates from different modules are never ranked. If more than one module offers a viable candidate, the call is a compile error, fixed in the importing module by a selective import or a rename (§14.2).
3. A call is resolved against the imports of the module where it is written, so a caller's imports never change a library's internal calls.

```
fn describe[T: Show](xs: List[T]) -> Str  // B
fn describe[T: Hash](xs: List[T]) -> Str  // D
// error: describe B and D have incomparable bounds;
//   add describe[T](xs: List[T]) -> Str where Show[T], Hash[T]
```

#### 5.6.2 Named arguments build records

Calling a function whose single parameter is a record with named arguments constructs that record. This is how record-typed combinators receive their branches (§10.2).

#### 5.6.3 Tail calls

Every call in tail position is guaranteed not to grow the stack, including calls between different functions. Tail recursion is how a loop carries a value, since `for` carries none (§7.3).

```
fn sum(xs: List[Int], i: Int, acc: Int) -> Int {
  if i == xs.size { acc } else { sum(xs, i + 1, acc + xs[i]) }
}
```

1. The caller's bindings are released before the jump, so `Immediate` handlers of its values run before the callee starts.
2. A stack-allocated closure passed in a tail call is copied into the callee's frame.
3. A foreign call in tail position is an ordinary call.

#### 5.6.4 Local functions

A `fn` may be declared inside a block. Unlike a closure, it can call itself, so recursion needs no module-level helper.

```
fn depth(t: Tree) -> Int {
  fn walk(n: Node, d: Int) -> Int {
    case n {
      Leaf -> d
      Branch(left, right) -> max(walk(left, d + 1), walk(right, d + 1))
    }
  }
  walk(t.root, 0)
}
```

- A local function follows the rules of a closure: it captures bindings declared before it (§6.4.1), it is never `pub`, and its escape and effects are inferred.
- It is visible from its declaration to the end of the block and may call itself. Local functions cannot call each other recursively; mutually recursive functions belong at module level.
- Its name is a binding of the block, so it cannot be overloaded and follows the no-shadowing rule (§5.4).

### 5.7 Tests

`test "name" { … }` declares a test at module level. Tests run with the `test` command (§20.6) and are never part of a release build (§20.7). A test passes when its block completes; it fails when it traps or its value is an error. Assertions come from `std.test`, and development dependencies are visible to tests (§14.5.1).

## 6 Expressions

### 6.1 Blocks

A block is a sequence of statements in curly braces. Its value is the value of the last evaluated expression; a block ending in a declaration has value `()`.

```
let area = {
  let w = 3
  let h = 4
  w * h
}  // ⇒ 12
```

### 6.2 Operators

Every operator is syntactic sugar for an ordinary standard-library function on the operand types. Defining that function for a type makes the operator available.

| Operator | Function | Notes |
| --- | --- | --- |
| `a + b`, `a - b`, `a * b`, `a / b` | `add`, `subtract`, `multiply`, `divide` | Trap on overflow and on division by zero (§3.1.1, §3.1.4) |
| `a +% b`, `a -% b`, `a *% b` | `addWrapping`, `subtractWrapping`, `multiplyWrapping` | Never trap |
| `a == b`, `a != b` | `equals` | |
| `a < b`, `a <= b`, `a > b`, `a >= b` | `lessThan`, `lessOrEqual`, `greaterThan`, `greaterOrEqual` | Return `Bool` |
| `and`, `or`, `not` | boolean keywords | Short-circuiting |

The operator functions are `add`, `subtract`, `multiply`, `divide`, `remainder`, `negate`, `addWrapping`, `subtractWrapping`, `multiplyWrapping`, `equals`, `lessThan`, `lessOrEqual`, `greaterThan` and `greaterOrEqual`. Each comparison operator calls its own function, which returns a `Bool`.

General-purpose ordering, as used by sorting and `SortedMap`, goes through `compare`, the function of the `Ordered` form (§4.7). It returns an `Ordering`, one of the prelude tags `Less`, `Equal` and `Greater`. For every `Ordered` type the prelude defines the comparison functions from `compare`, so `a < b` there means `compare(a, b) is Less`. A type defines a comparison function itself only when it orders values without `compare`, or more cheaply.

```
type Less
type Equal
type Greater
type Ordering = Less | Equal | Greater
form Ordered[T] { compare(a: T, b: T) -> Ordering }

fn lessThan[T: Ordered](a: T, b: T) -> Bool { compare(a, b) is Less }
fn lessOrEqual[T: Ordered](a: T, b: T) -> Bool { not (compare(a, b) is Greater) }
```

`Float` is `Ordered`, since it holds only finite values (§3.1.4). A `Float | NaN` is not, so sorting values that may be NaN first narrows them or takes an explicit comparator.

`a % b` calls `remainder`, and unary `-a` calls `negate`.

#### 6.2.1 Precedence

From tightest to loosest:

| Level | Operators | Associativity |
| --- | --- | --- |
| 1 | call `f(…)`, bracket `e[…]`, `.name`, `?.name`, trailing closure | left |
| 2 | prefixes (§8.5), unary `-` | applies to the whole level-1 expression |
| 3 | `*` `/` `%` `*%` | left |
| 4 | `+` `-` `+%` `-%` | left |
| 5 | `..` | none |
| 6 | `==` `!=` `<` `<=` `>` `>=` `is` | none |
| 7 | `not` | prefix |
| 8 | `and` | left |
| 9 | `or` | left |
| 10 | `lazy` | prefix; takes the whole expression to its right (§6.10) |

- Operators without associativity cannot be chained: `a < b < c` and `a..b..c` are compile errors.
- `not x == y` means `not (x == y)`.
- `if x is Point and x.y > 0` parses as `(x is Point) and (x.y > 0)`. Narrowing by `is` flows into the right operand of `and`, so `x.y` sees `x` as a `Point`.
- `a..b - 1` means `a..(b - 1)`.
- `-2.abs()` means `-(2.abs())`, which is `-2`. A numeric literal never includes its sign, so `x-2` stays a subtraction.

### 6.3 Uniform function call syntax

`x.f(args)` means `f(x, args)`. If `x` has a field named `f`, the field wins. Every visible function whose first parameter accepts the type of `x` is callable this way, without a module prefix.

```
xs.map(f)  // same as map(xs, f)
p.distance(origin)  // same as distance(p, origin)
```

A type name before the dot makes a type-qualified call: `T.f(args)` calls `f(args)`, choosing among the overloads of `f` those whose success type is `T` (§5.6.1). It adds no static methods and no namespaces; `T.` only states the result the call must produce. If no overload of `f` produces `T`, the call is a compile error.

```
let n = Int.parse("42")  // Int | ParseError, not the Float overload
let z = Zone.named("Europe/Berlin")  // Zone | UnknownZone
let r = Rng.seeded(42)  // Rng
```

### 6.4 Closures

A closure literal is `{ params -> body }`. A closure passed as the last argument may be written after the call’s parentheses (trailing closure), and the parentheses may be dropped when empty.

```
let double = { n -> n * 2 }
let evens = xs.filter { n -> n % 2 == 0 }
```

#### 6.4.1 Capture rules

1. A closure may read captured `let` and `var` bindings.
2. A closure must never write a captured `var`.
3. Whether a closure escapes is inferred by the compiler. An escaping closure that captures a mutable local is a compile error.
4. Whether a closure resolves refs is inferred as its ref effect, never written in a signature (§3.14). A closure that captures a ref is bindings-only (§3.12).

### 6.5 Bracket application

`e[...]` is a single syntax for indexing and for supplying generic type arguments. The compiler decides which from what `e` is.

```
let empty = List[Int]()  // type argument
let first = xs[0]  // index
let age = ages["ada"]  // map index: Option[Int]
```

Indexing a map returns an `Option`.

### 6.6 Partial application

Partial application is explicit: write `_` for each missing argument. There is no automatic currying.

```
let addTen = add(_, 10)
let clampPercent = clamp(_, min: 0, max: 100)
```

Rules:

- A `_` turns the smallest enclosing argument into a function. Several `_` in one argument become parameters, left to right. `_.f()` works through UFCS.
- Supplied arguments are evaluated once, when the partial application is created, not on every call.
- The result is a closure whose type is the function type of the missing parameters, such as `(Image) -> Image`. It is structural and fits anywhere a function of that shape is expected.
- The missing parameters' types must be fixed where the partial application is created, by the supplied arguments or the expected type. A generic or overloaded target whose remaining types stay open is a compile error. An overloaded name used as a function value, as in `xs.map(area)`, resolves against the element type, including union lifting (§4.6.1).
- The compiler knows the target and every supplied value, so it may specialize the target for them. `power(_, 3)` can compile to `x * x * x`.

```
xs.map(_ * 2)  // xs.map { x -> x * 2 }
f(g(_))  // f({ x -> g(x) })
let thumb = resize(_, width: 256)
let notify = send(_, loadConfig())  // loadConfig runs once, here
```

### 6.7 Record construction and update

A record is updated by constructing a new one from an existing value with a spread, then overriding fields. Dotted paths reach into nested records. The compiler collapses batched changes into one copy.

```
let moved = Shape(..s, pos.x: 3, size: 50)
```

Each override is a value or a transform. A value replaces the field. A function from the field's type to itself transforms the current field value, and `_` keeps it short. When the field's own type is a function type, both readings fit and the argument is a compile error; write the new value explicitly from the old one instead. A list of dotted paths with values or transforms is a *field-update list*, and it means the same wherever a record is rebuilt. Anonymous records take it too.

```
let bigger = Shape(..s, size: _ * 2, pos.x: 0)
let shifted = (..p, x: _ + 1)
```

#### 6.7.1 update on values

`v.update(list)` rebuilds `v` as its own type with a field-update list and returns the new value; `v` is unchanged. A constructor always builds the type it names, so `Shape(..s, …)` given a `Circle` yields a plain `Shape` and loses the circle's fields. `update` keeps the value's actual type, including subtypes and the extra fields of open records, which makes it the way to write type-preserving field changes in generic code.

```
fn nudge[S: Shape](s: S) -> S {
  s.update(pos.x: _ + 1)
}
```

On a ref or `ext` binding the same call commits atomically (§9.3).

> **Hint.** `where` is never used for updates; it is reserved for constraints (§3.10).

### 6.8 Option handling

`?.` chains through `Option` values: if the left side is `Empty`, the whole chain is `Empty`. `.then { v -> ... }` runs an action only when a value is present.

```
let city = user?.address?.city  // Option[Str]
ages["ada"].then { a -> print("Ada is {a}") }
```

Crag deliberately has no `??` default operator, no `if let`, and no mixing of `else` with `?` in one expression. Defaults are supplied with functions or `case`.

### 6.9 Patterns

- Anonymous-record patterns bind fields by name.
- Named types may also be bound positionally.
- `_` ignores a part.

```
let (x, y) = (y: 2, x: 1)  // binds by name: x = 1, y = 2
let Point(a, b) = p  // positional for named types
```

A bare name in a pattern is resolved by position:

- At the top of a `case` arm, a bare name is always a type or tag. An unknown name there is a compile error, so a misspelt tag never becomes a catch-all binding.
- Everywhere else (in a `let`, a `for`, a closure parameter, and inside the slots of a pattern) a bare name is a type if a type of that name is visible, and a new binding otherwise.
- A binding may not have the name of a visible type. Like any other collision, a type with that name arriving through an import is a compile error, so a pattern never silently changes meaning.

```
type Wrapped(inner: NotFound | Timeout)
case w {
  Wrapped(inner: NotFound) -> "wrapped miss"  // NotFound is a type: matched
  Wrapped(inner: t) -> "wrapped {t}"  // t is not a type: binds
}
```

String interpolation writes an expression in braces inside a string literal: `"Ada is {a}"`. Literal braces are written `{{` and `}}`.

### 6.10 Lazy evaluation

`lazy expr` and `lazy { block }` produce a `Lazy[T]`. It is evaluated on the first read of `.value` and cached; concurrent first reads evaluate it once.

`lazy` binds loosest of all: it takes the whole expression to its right, so `lazy a + b` is a `Lazy[Int]` of `a + b`. In an argument list the expression ends at the comma, as any argument does.

```
let config = lazy loadConfig()  // Lazy[Config], nothing runs yet
let report = lazy {
  let rows = query(db)
  summarize(rows)
}
fn log(level: Level, msg: Lazy[Str]) { ... }
log(Debug, lazy "state: {dump(s)}")
config.value  // runs loadConfig() once
```

1. An expression in a `Lazy[T]` position is never wrapped implicitly; `let c: Lazy[Config] = loadConfig()` is a type error.
2. A lazy parameter is a `Lazy[T]` parameter. A parameter that must re-evaluate on each use is a closure, written as one: `{ -> n < 10 }`.
3. A `lazy` expression captures like a closure (§6.4.1): it cannot capture a `var` if it escapes, and one that captures a ref is bindings-only (§3.12). Its effects are inferred and checked where `.value` is read.
4. `Lazy[T]` is never `Solid`.
5. A trap during `.value` traps at the read and emits a signal carrying the origin of the `lazy` expression (§8.3).

#### 6.10.1 Lazy sequences

`Seq[T]` is a lazy sequence computed within one task. `map`, `filter` and `take` on a `Seq` compute only the elements consumed, so infinite sequences are safe. A `Seq` converts to and from the `Finite` and `Infinite` stream types (§10.5).

```
let firstSquares = range(1..).map { n -> n * n }.take(10)
```

### 6.11 Type holes

`???` is a type hole: an expression standing in for code not yet written. It is a single token and may appear wherever an expression may.

```
fn area(s: Shape) -> Float {
  case s {
    Circle(r:) -> 3.14159 * r * r
    Rect(w:, h:) -> ???
  }
}
```

Rules:

- A hole fits any expected type, so code containing holes type-checks and the rest of the program can be compiled and run.
- The compiler reports each hole with the type it must have and the bindings in scope at that point. The REPL shows this as the code is typed. When the context fixes no type, the hole's type is inferred from its uses; if it remains open, the report shows it as `_`.
- Evaluating a hole traps, like any other runtime error.
- A hole is allowed everywhere, including where a `Solid` value is required. The code that later fills the slot is checked like any other.
- Building a package for release fails while any hole remains.

## 7 Control flow

Crag has three control constructs: `if`, `case` and `for`. There are no loop labels and no `goto`.

### 7.1 `if` and narrowing

`if` is an expression. `if x is T` tests a type and narrows `x` to `T`:

- inside the `if` branch always;
- for a `let` binding, for the rest of the scope after an early exit;
- for a `var`, until it is reassigned;
- never for a `ref`, whose value may change at any time.

```
fn describe(v: Int | NotFound) -> Str {
  if v is NotFound { return "missing" }
  "value {v + 1}"  // v is narrowed to Int here
}
```

`return expr` exits the innermost enclosing `fn`, closure literal or `atomic` block with that value; `return` alone returns `()`. In a closure it is always a local return: it ends the closure, never the function around it.

```
let sizes = files.map { f ->
  if f.isEmpty() { return 0 }
  f.size()
}
```

- The result type of a function or closure is the union of its `return` values and its last expression.
- In a combinator branch, `return` ends that branch with a value.
- A `lazy { … }` block counts as a closure.
- A `for` body is not a closure: `return` there exits the enclosing `fn`.
- In an `atomic` block, the returned value decides whether the transaction commits (§9.5.1).

#### 7.1.1 `let … else`

A `let` with `else` binds only when the value matches its pattern; otherwise the `else` part runs, and it must leave: by `return`, a trap, or a call that returns `Never`. The compiler rejects an `else` part that can complete normally, so the binding is never left unbound. With `else`, a type annotation on the pattern is a type test instead of a requirement.

The `else` part is a block, or a closure whose parameter receives the unmatched value, narrowed to the members the pattern did not match:

```
let name: Str = p.name else { return Empty }
let port: Int = Int.parse(portText) else { return defaultPort }
let u: User = lookup(id) else { rest -> return rest }  // rest: NotFound | DbError
```

### 7.2 `case`

`case` matches a value against type and structural patterns. It must be exhaustive. `pass` propagates every alternative not handled so far to the caller (§8.2).

```
case lookup(id) {
  u: User -> greet(u)
  NotFound -> signUp()
  pass  // remaining errors flow to the caller
}
```

Arms may overlap, for example a subtype and its parent. The **first matching arm in source order** wins; there is no ranking by specificity (that applies only to overload resolution, §5.6.1). An arm that can never match because earlier arms cover it is a compile error.

```
case result {
  NotFound -> "missing"
  LookupError -> "other lookup failure"  // catches the rest
  n: Int -> use(n)
}

case result {
  LookupError -> "lookup failure"
  NotFound -> "missing"  // error: unreachable, covered by LookupError
  n: Int -> use(n)
}
```

Guards (`where`) never make an arm cover a later one: an arm with a guard can fail, so the arms after it stay reachable.

A `case` on a `let` or `var` binding narrows that binding in each arm (§7.1). The arm `_` sees it narrowed to the members no earlier arm matched. A `case` on any other expression binds with `name: T`, or `name: _` for the rest. `name: T` is allowed on a binding too; the new name must not already be in scope (§5.4).

```
type Timeout(..Error, after: Duration)
type Rejected(..Error, code: Int, reason: Str)

case r {
  Order -> "order {r.id}"  // r is narrowed to Order
  NotFound -> "no such order"
  Timeout(after:) -> "timed out after {after}"
  Rejected(code: 404, reason) -> "gone: {reason}"
  Rejected(code, reason:) -> "rejected {code}: {reason}"
  _ -> "other error: {r}"  // r is narrowed to the rest
}

case lookup(id) {
  o: Order -> "order {o.id}"
  NotFound -> "no such order"
  pass
}
```

### 7.3 `for` is a collector with no value

`for` iterates a collection purely for effects: updating refs, rebinding `var`s, and I/O. It never produces a value. To compute a value from a collection, use the appropriate collector function (`map`, `filter`, `fold`, …).

```
var sum = 0
for n in numbers { sum = sum + n }

let squares = numbers.map { n -> n * n }  // values come from collectors
```

#### 7.3.1 Iterating maps

Map iteration destructures each entry. Use `_` for parts you ignore. Any entry type that matches the pattern structurally is accepted.

```
for (key, value) in ages { print("{key}: {value}") }
for (key, _) in ages { print(key) }
```

### 7.4 Ranges

A range is an increasing sequence of values of a discrete type. `a..b` runs from `a` to `b`, inclusive at both ends, and has type `Range[T]`. An open range `a..` has no upper end and has type `RangeFrom[T]`. `..` is syntax, not an operator: no function stands behind it, and it cannot be overloaded. Both ends must have the same type `T`, and `T` must fit `Discrete`:

```
form Discrete[T] where Ordered[T] {
  next(t: T) -> T
}

type Range[T: Discrete](first: T, last: T)
type RangeFrom[T: Discrete](first: T)
```

- `next(t)` is the least value greater than `t`. A type whose `compare` and `next` disagree breaks iteration; the compiler cannot check this.
- `a..b` requires `a <= b`, so a range is never empty and `a..a` holds one value. A range whose ends are both constants and decrease is a compile error; otherwise `a..b` traps when `a > b`, since a decreasing range is almost always a mistake.
- Iterating `a..b` yields `a` and applies `next` until it reaches `b`; it never calls `next(b)`, so `0..UInt8.max` is safe. Iterating `a..` applies `next` without end: the loop runs until it is left, and `next` traps when the type runs out of values, as integer overflow does.
- `Int`, the sized integers, `CodePoint` and `Fixed[S]` fit `Discrete` through the prelude, and the compiler handles their ranges directly. `Float` is `Ordered` but has no `next`, since the gap between neighbouring floats depends on their magnitude, so it forms no range.
- A range over `Fixed[S]` steps by one unit of its scale, 10⁻ˢ: `0.00..2.00` holds 0.00, 0.01, …, 2.00. A decimal literal at an end has exactly the scale it is written with, so the step shows in the range itself. `0.0..2.00` is a compile error, since its ends are a `Fixed[1]` and a `Fixed[2]`, and so is `0.0..p` for a `p: Fixed[2]`.
- Any type fits `Discrete` once it has `compare` and `next`, so ranges work over the program's own types.
- A range pattern `lo..hi` in a `case` arm (§7.2) follows the same rules: its ends are literals of a discrete type, decimal ends are written with the scale of the subject's `Fixed[S]`, and `lo > hi` is a compile error.
- An open range fits only where an unbounded sequence is accepted, as in `range(1..)` (§6.10.1).

At the end of a line an open range must be parenthesized, since a line ending in `..` continues (§2.3). `..` also serves as the spread marker; the two uses never collide because a range always has an operand on its left, while a spread, an open-record marker and a rest pattern never do.

```
for i in 1..3 { print("{i}") }  // prints 1, 2, 3
for c in 'a'..'e' { print("{c}") }  // prints a to e
for p in 0.0..0.5 { print("{p}") }  // prints 0.0, 0.1, …, 0.5

distinct type Grade(rank: Int)
fn compare(a: Grade, b: Grade) -> Ordering { compare(a.rank, b.rank) }
fn next(g: Grade) -> Grade { Grade(rank: g.rank + 1) }
for g in Grade(rank: 1)..Grade(rank: 6) { … }
```

> **Hint.** Ranges bind looser than arithmetic, so `0..n - 1` means `0..(n - 1)` (§6.2.1). It traps when `n` is 0; to visit the indices of a possibly empty list, iterate the list itself or guard the loop.

## 8 Errors and type mappings

Crag reports through three channels, each with one job:

|  | Errors | Signals (Ch. 11) | Traps (§8.3) |
| --- | --- | --- | --- |
| Carry | domain outcomes | domain or logging information | runtime and machine conditions |
| Raised by | any code, as a return value | any code, with `emit` | the runtime, or `!!` |
| Per block | one result | any number | at most one |
| Effect on the block | none, it is a value | none, execution continues | ends the block |
| Travel | to the immediate caller | up the scope tree to a handler | past all code to a handler |
| In signatures | yes | never | never |
| Handled by | `case`, `let … else`, prefixes | `on S { … }`, returning `()` | `on T { … }`, whose value replaces the block's |

Errors are ordinary values. A fallible function returns a union of its success type and its error types, and the compiler infers that union. There are no exceptions for expected failures.

### 8.1 Error unions

```
type NotFound(..Error)
type Expired(..Error, at: Time)

fn session(id: Str) -> Session | NotFound | Expired {
  ...
}
```

The error part of a return type is inferred from the function body; writing it out is optional documentation that the compiler checks.

An error type spreads the `distinct` parent `Error`, directly or through a family parent, just as signal types spread `Signal` (§11.1). Only such types are error members: `Errs[X]` selects them and `Oks[X]` the rest, so `Empty` and `Closed` are outcomes, not errors. A type spreads at most one of `Error`, `Signal` and `Trap`.

```
pub distinct type LookupError(..Error)
type NotFound(..LookupError)
type Expired(..LookupError, at: Time)
```

Every error type of the standard library spreads `Error`, through a family parent where one exists: `IoError`, `ParseError`, `DecodeError`, `EmbedError`, `UnknownZone` and the rest. Examples in this document that use an error type without declaring it assume the same.

### 8.2 Handling results with `case` and `pass`

A result must be handled exhaustively, by `case` or by `if ... is` narrowing. `pass` inside a `case` hands every unhandled alternative to the caller, whose inferred return type grows accordingly.

```
fn greetUser(id: Str) -> Str | NotFound {
  case session(id) {
    s: Session -> "Hello {s.user}"
    Expired -> "Please log in again"
    pass  // NotFound flows out
  }
}
```

> **Hint.** There is no `?` propagation operator. `pass` makes propagation visible at the one place the value is inspected.

### 8.3 Traps

Traps are runtime and machine conditions: integer overflow, failed value conditions, exhausted resources, runtime faults, and `!!` applied to an error (§8.4). Where an error is a domain outcome returned to the caller, a trap ends the code that raised it and travels past every intermediate call to the nearest trap handler (§8.3.1). Traps never appear in signatures, and user code never raises one directly: they come from the runtime, and from expect (!!) through a std intrinsic (§19.2).

Stack overflow traps too: a task's stack reaching its maximum is a trap, not an abort (§13.6).

A *deferred trap* happens in code that runs away from where it was written. It is handled by whether anything waits for the result:

- **Nothing waits** (a `Deferred` dispose handler, deferred teardown): the trap becomes a signal only, and execution continues.
- **A reader waits** (`.value` on a `Lazy[T]`): the read traps, and a signal carrying the origin of the `lazy` expression is emitted as well.

A trap that becomes a signal is delivered as `TrapSignal(..Signal, trap: Trap)`. Traps are `Solid`: they carry a message and an origin, never closures or the failed value. The trap types form a family; their constructors are intrinsics (§19.2), so user code reads traps but never creates them.

```
pub distinct type Trap(message: Str, origin: Origin)
pub type Overflow(..Trap)
pub type ConditionFailed(..Trap, condition: Str)
pub type Expectation(..Trap, errorType: Str)  // raised by !!
pub type StackOverflow(..Trap)
pub type Fault(..Trap)
```

#### 8.3.1 Trap handlers

`on T { t -> … }` with a trap type `T` is a statement. It covers the rest of its block, including everything called from there, up to the nearest inner trap handler.

```
fn render(r: Report) -> Str {
  on Trap { t ->
    log("render failed: {t.message}")
    "<unavailable>"
  }
  layout(r).toHtml()
}
```

- When a covered trap occurs, unwinding stops at the handler's block. Dispose handlers run for the values created in it and `ext` locks are released (§9.6); then the handler runs.
- The handler's value becomes the value of the block and must fit the block's type, so no signature changes.
- Inside a handler, `emit t` passes the trap on to the next outer handler.
- A parent trap type catches its subtypes. When several handlers of one block match, the most specific wins.
- Refs keep the updates made before the trap; only an `atomic` block rolls back (§9.5.1).
- A trap in a branch or task cancels the rest of its scope and continues to the handlers around it (§10.4).
- A trap that no handler takes reaches the root, which writes it to stderr with its stack and ends the program.

### 8.4 Type mapping functions

A *type mapping function* transforms the type of its argument. The standard library defines three:

| Function | Prefix | Keeps | Errors become | Use |
| --- | --- | --- | --- | --- |
| `discard` | `~` | the errors | themselves | A value you do not need; its errors are still handled |
| `check` | `?` | the success | `Empty` | Whether it worked matters, not why |
| `expect` | `!!` | the success | a trap | Scripts, the REPL, tests and true invariants |

```
pub fn discard[X](x: X) -> () | Errs[X] prefix "~"
pub fn check[X](x: X) -> Oks[X] | Empty prefix "?"
pub fn expect[X](x: X) -> Oks[X] prefix "!!"
```

- `check`: if the success type already contains `Empty`, success and failure would merge, so this is a compile error.
- `expect`: the trap carries the kind, the origin and the error's type name, never the error value (§8.3).
- `check` and `expect` on a value with no error members are compile errors. `discard` is allowed there, since it is also how an unneeded value is dropped, such as the old value returned by `swap`.

`discard` is error-preserving: the remaining errors still require `case` or `if` for exhaustiveness.

```
case discard(file.write(bytes)) {
  () -> ()
  e: IoError -> log(e)
}
```

### 8.5 Prefixes

A type mapping function may declare a prefix, so it can be applied without parentheses. The standard library declares the prefixes of `discard`, `check` and `expect`; they are fixed for every program.

```
~ sendMail(msg)  // same as discard(sendMail(msg))
let cfg = ? loadConfig(path)  // Config | Empty
let port = !! Int.parse(portText)  // Int, or a trap
```

Rules (see also §2.8):

1. Any package may declare prefixes, but a prefix may be declared only once.
2. Prefixes may have several characters (for example `disc` or `!!!`).
3. A prefix replaces the rejected form `_ = expr`, which reads like a broken `let _ = expr`.

A type mapping function has exactly one parameter, and its return type is computed from the parameter's type, usually with type functions (§18.3). `prefix "…"` comes last in the signature, before the body.

A prefix applies to the whole postfix expression that follows, including calls and field access, and binds tighter than any binary operator: `~ a.b().c()` means `~ (a.b().c())`, and `!! a + b` means `(!! a) + b`.

> **Hint.** `expect` uses `!!`, not `!`: to readers from C-like languages, `!ready()` looks like "not ready", but it would mean "ready, or trap".

## 9 Shared state: `ref` and `ext`

Refs are the only mutable values in Crag, and therefore the one place where the immutable-first principle bends. The rules below keep that bend small, explicit and safe under concurrency.

### 9.1 The `Ref[T]` type

`ref counter = 0` declares a binding of the compiler-owned type `Ref[Int]`. `Ref` is not a library type. A ref gives access to the latest version of a value; resolving it always yields the latest value within the lifetime of the scope. A ref keeps no history; history can be built from ordinary types.

### 9.2 Refs are bindings only

1. A ref must never be stored in a data structure; only values can be stored.
2. A closure that captures a ref is bindings-only too: passed and called, never stored or returned (§3.12).
3. A ref is never narrowed by `if ... is` (§7.1).
4. The compiler may inline a ref into a plain local when it proves there is only one user.

### 9.3 Access functions

There are no getters or setters. Every access is an atomic operation that passes a closure:

| Function | Purpose |
| --- | --- |
| `update` | Replace the value with the closure’s result |
| `use` | Compute something from the current value without changing it |
| `swap` | Place a new value and return the old one |
| `empty` | For a type that includes `Empty`: return the value and leave `Empty` in its place |

```
ref hits = 0
hits.update { n -> n + 1 }
let snapshot = hits.use { n -> n }
let batch = queue.swap([])
queue.update { q -> if q.size < 100 { q.append(job) } else { q } }
```

The signatures of the two value-moving functions:

```
swap[T](r: Ref[T], new: T) -> T
empty[T](r: Ref[Option[T]]) -> Option[T]
```

There is no conditional update function. A condition on the value is ordinary code inside the `update` closure, which already sees the current value atomically; a condition involving other refs goes in an `atomic` block. When an `update` closure returns its input unchanged (the identical value, not merely an equal one, so v.update(x: v.x) counts as a write), nothing is written and the version is not bumped, so a failed condition never causes conflicts for other transactions. Whether a caller learns that an update applied is program behavior, not a language feature.

An `update` closure may also produce an error value. Then the ref keeps its value, nothing is written, and the error is the result of `update`, whose type becomes `() | E`. `return` ends the closure early (§7.1).

Two forms shorten common accesses:

- `r.use()` with no closure returns the current value as an atomic snapshot. It is still an explicit call: a ref's name alone never denotes its value.
- `r.update(list)` with a field-update list (§6.7) means exactly `r.update { v -> v.update(list) }`. All paths commit together as one update.

```
let n = hits.use()
state.update(count: _ + 1, pos.x: 0)
atomic { if a.use() > b.use() { b.update(_ + 1) } }
```

There is no operator assignment (`r += 1`) and no read prefix: every ref access stays a visible call. Both forms apply to `ext` unchanged.

### 9.4 Optimistic updates

A ref update is optimistic. The closure runs against the version it read; the result commits only if the ref still holds that version, otherwise the closure reruns. Therefore update closures must be free of I/O and may run more than once.

The compiler infers commutative updates (for example counters) and may apply them without conflict retries.

### 9.5 One ref per update; transactions

Reading a second ref inside a single-ref update closure is a compile error. To update several refs together, use an atomic transaction block.

```
ref from = 100
ref to = 0

atomic {
  from.update { b -> b - 25 }
  to.update { b -> b + 25 }
}
```

No I/O of any kind is allowed in an atomic block or update closure, not even tracing. Use signals to defer effects (Chapter 11).

Nothing that suspends or lets other tasks see an attempt is allowed there either: `put`, `next`, starting a task and waiting on a hub are compile errors in an atomic block or update closure, because the attempt may still be discarded.

#### 9.5.1 Failing a transaction

An `atomic` block commits when its value is a success value and aborts when its value is an error value, as selected by `Errs` (§8.1). An aborted block discards all its ref changes, delivers its `emit fail` signals (§11.2) and does not rerun; the error becomes the block's value. `return` (§7.1) aborts early from anywhere inside the block.

```
type InsufficientFunds(..Error)

let r = atomic {
  if from.use { a -> a.balance } < amount { return InsufficientFunds }
  from.update { a -> Account(..a, balance: a.balance - amount) }
  to.update   { a -> Account(..a, balance: a.balance + amount) }
}
// r: () | InsufficientFunds
```

Three outcomes stay apart: a conflict reruns the block and delivers `emit retry` signals; an error value aborts it once; a trap aborts it and continues to the nearest trap handler (§8.3.1).

### 9.6 `ext`: pessimistic external state

Mutable foreign state (typically FFI handles) cannot be retried safely, so it is bound with `ext`, a locking ref. `ext` offers the same access functions as `ref`; the closure runs exactly once while holding the lock.

Accessing another `ext` inside an `ext` closure is a compile error, as reading a second ref is in an update closure (§9.5), so locks never nest and cannot deadlock. Accessing an `ext` inside an atomic block or update closure is a compile error too, since an attempt may rerun. A fiber waiting for the lock suspends without blocking its thread.

```
ext db = openDb("app.sqlite")
let rows = db.use { h -> query(h, "select * from users") }
```

### 9.7 Closures that capture both `var`s and refs

A closure may read captured `var`s and resolve refs through access functions. The combination is sound because `var`s are only read and refs are only changed atomically.

## 10 Concurrency

Crag is designed for maximal concurrency under strict structure: every task is started by a scope and finishes before that scope returns.

### 10.1 Structured tasks

1. There are no detached or background tasks.
2. A scope that starts tasks awaits all of them before it completes.
3. The scope decides the error-handling policy for its tasks.
4. There is no `scope` keyword and there are no block qualifiers; concurrency is expressed with combinator functions.

> **Hint.** Long-running processes belong in separate programs or daemons scheduled by the operating system, not in detached tasks.

#### 10.1.1 Sequential code and tasks

Statements always run in order, and their effects happen in that order; a block's value is its last expression. The compiler never runs statements concurrently on its own. Concurrency exists only inside collectors: each closure passed to a combinator (§10.2) or started in a task group (§10.2.1) becomes a task, and the collector's scope ends only when its tasks have.

```
let a = fetchUser(id)  // runs first
let b = fetchPosts(id)  // then this

let both = all(  // concurrently, by request
  user: { -> fetchUser(id) },
  posts: { -> fetchPosts(id) },
)
```

Inside a task, code is sequential and blocking. A call that waits (reading a connection, receiving from a stream, reading a `Lazy` another task is computing) suspends only that task. Tasks are therefore lightweight stackful tasks, fibers, suspended and resumed by the runtime over non-blocking I/O:

- There is no `async` or `await` and no function colouring. A function that waits is called like any other, inside a task or outside one.
- Waiting costs a task's stack, never an operating-system thread, so thousands of waiting tasks are cheap.
- A suspended task keeps its real call stack, which the debugger shows (§20.3).

### 10.2 Combinators

Concurrency combinators are ordinary functions that take closures. Branches are given as named arguments, which build a record (§5.6.2); the result is a record with the same field names.

| Combinator | Completes when | Result |
| --- | --- | --- |
| `all` | Every branch succeeds, or the first one fails | All successes, or the first error |
| `allDone` | Every branch has finished, success or failure | Each branch’s result or error |
| `first` | The first branch succeeds | That success; others are cancelled |
| `firstDone` | The first branch finishes, success or failure (a race) | That outcome; others are cancelled |

The suffix `Done` always means “finished, successfully or not”.

```
let page = all(
  user: { -> fetchUser(id) },
  posts: { -> fetchPosts(id) },
)
show(page.user, page.posts)

let fastest = firstDone(
  primary: { -> query(primaryDb) },
  replica: { -> query(replicaDb) },
)
```

The signature uses the compiler-known form `Fields` (§4.5):

```
pub fn all[R](branches: R) -> Oks[R] | Errs[R]
  where Fields[R, () -> _]

pub fn allDone[R](branches: R) -> Returns[R]
  where Fields[R, () -> _]

pub fn first[R](branches: R) -> OneOf[Oks[R]] | Errs[R]
  where Fields[R, () -> _]

pub fn firstDone[R](branches: R) -> OneOf[Returns[R]]
  where Fields[R, () -> _]
```

The result types use four type functions (§18.3) over the branch record `R`:

- `Returns[R]`: each field's full return type.
- `Oks[R]`: each field with its error members removed.
- `Errs[R]`: the union of all branches' error members.
- `OneOf[X]`: the union of a record's field types.

If every branch of `first` fails, its result is the last failure.

#### 10.2.1 Task groups

When the number of tasks is known only at runtime, a task group is used. `all` and `firstResult` take a single closure that receives a group handle; the body starts tasks through it while the scope runs.

```
pub opaque type Group[T](handle: RuntimeGroup)

pub fn start[T](g: Group[T], task: () -> T) -> ()

pub fn all[V](limit: Int | Empty = Empty, body: (Group[()]) -> V) -> V

pub fn firstResult[T](limit: Int | Empty = Empty, body: (Group[T | Empty]) -> ()) -> T | Empty
```

Rules:

- The scope completes when the body and every started task have finished. Nothing outlives it.
- Tasks started through a group handle their own errors: `T` contains no error members. Results flow through refs, streams or hubs.
- In `all`, tasks return `()` and the scope's value is the body's value.
- In `firstResult`, the first task to return a `T` wins, and the body and all other tasks are cancelled. A task returns `Empty` to give no result. The scope's value is `Empty` if no task produced a result.
- `limit` bounds the number of running tasks: `start` suspends while it is reached.
- A task started through a group captures `var` bindings by value, as they stand when `start` runs. The body keeps running and may rebind them, and the task never sees those rebinds. Combinator branches need no such rule, because the code that starts them waits until they finish.
- `Group` is bindings-only, like a ref. It may be captured by the scope's own tasks and passed as a parameter within them, but never stored or returned. A function can therefore start tasks only if it receives a group, and its signature shows it.
- A task ends by returning. Removing a task from outside goes through the data it consumes (§10.6), never through a handle.
- The fixed and dynamic forms of `all` never clash: a branch record must satisfy `Fields[R, () -> _]`, which `limit:` and a trailing group closure cannot.

```
ref pages = []
let done = all(limit: 8) { g ->
  for url in urls {
    g.start { ->
      case fetch(url) {
        p: Page -> pages.update(_.append(p))
        HttpError -> log("skipped {url}")
      }
    }
  }
}

let page = firstResult { g ->
  for mirror in mirrors {
    g.start { ->
      case fetch(mirror) {
        p: Page -> p
        HttpError -> Empty
      }
    }
    sleep(ms: 200)
  }
}
```

### 10.3 Captures in branches

Branches may read captured `let` and `var` bindings. They must not write `var`s. Shared changes go through refs (Chapter 9).

### 10.4 Failure, traps and cancellation

A trap in a branch (§8.3) is not a result. In every combinator it cancels the remaining branches and continues to the trap handlers around the combinator (§8.3.1). A branch that must survive a trap handles it inside its own closure with `on Trap`. Otherwise, whether sibling branches are cancelled follows from the combinator's semantics: `all` and `first` cancel remaining branches once their outcome is decided; `allDone` never cancels.

In a task group (§10.2.1), a trap in the body or any task likewise cancels everything else in the group and continues to the handlers around it. Deliberate cancellation is never a failure.

A cancelled task never runs on. Cancellation takes effect at every suspension point and at checks the compiler inserts in every call and loop, so a task that only computes stops too. It waits while the task is inside an atomic block or update closure, an `ext` closure, a foreign call, or a drop or dispose handler, and takes effect when that finishes. Code whose changes must happen together already uses `atomic` (§9.5), which cancellation never splits.

### 10.5 Streams

A stream is a one-to-one pipe between two tasks: one producer, one consumer and a bounded buffer. Multi-party communication uses hubs (§10.6).

```
pub opaque type Sink[T](handle: RuntimeStream)
pub opaque type FiniteSink[T](..Sink[T])
pub opaque type Source[T](handle: RuntimeStream)
pub opaque type Finite[T](..Source[T])
pub opaque type Infinite[T](..Source[T])

pub distinct type Sent
pub distinct type Full
pub distinct type Closed
pub type Abandoned(..Closed)

pub fn stream[T](capacity: Int) -> (sink: FiniteSink[T], source: Finite[T])
pub fn infiniteStream[T](capacity: Int) -> (sink: Sink[T], source: Infinite[T])
```

Operations:

- `put(s: Sink[T], v: T) -> Sent | Closed` suspends while the buffer is full.
- `tryPut(s: Sink[T], v: T) -> Sent | Full | Closed` never suspends. What to do with a value that does not fit is program behavior.
- `putAll(s: FiniteSink[T], items)` puts every item of an iterable, stops early on `Closed`, and closes the sink at the end.
- `next(s: Finite[T]) -> T | Closed` and `next(s: Infinite[T]) -> T | Abandoned` suspend while the buffer is empty.
- `close()` on a FiniteSink or on any source ends the stream deliberately.

The kind of a stream is chosen where it is made, and each end's type carries it. Only a `FiniteSink` can end a stream normally; the sink of an infinite stream can put but not close, so when its task ends the source reads `Abandoned` (§10.5.2). A consumer can always stop: `close()` on a source makes the producer's next `put` return `Closed`. `Finite[T]` and `Infinite[T]` fit where a `Source[T]` is expected, and `FiniteSink[T]` where a `Sink[T]` is; `next` on a plain `Source[T]` returns `T | Closed`.

Only the buffer is intrinsic: `RuntimeStream` and its operations (create, put, take, close, dispose) are body-less `fn` declarations implemented by the runtime's scheduler (§19.2). `stream` and `infiniteStream` are ordinary standard-library functions that wrap one handle in the right pair of opaque types. The runtime never knows whether a stream is finite; it only knows whether an end was closed or disposed.

Every source fits `Iterable`, so `for` works on both kinds; a loop over a source ends when it reads `Closed`.

#### 10.5.1 Backpressure

A capacity is always given; there are no unbounded streams. A full buffer suspends the producer, an empty one the consumer. `capacity: 0` makes a hand-off in which the producer runs only when the consumer asks, which is demand-driven pull without a separate request protocol.

#### 10.5.2 Ending

A stream carries values only, never errors. Each side handles its own failures; a failed side's error travels in its combinator result.

- An end closed with `close()` makes the other side read `Closed`.
- An end disposed without `close()`, because its task failed, trapped or was cancelled, makes the other side read `Abandoned`. As a subtype of `Closed`, it is caught by a `Closed` arm unless matched first.
- An `Infinite` source cannot end normally; it can only be abandoned.
- Collectors that need an end, such as `toList` and `count`, take a `Finite` source and stop at `Closed`, which includes `Abandoned`. They do not report truncation; a program that needs to know emits a signal from the failing side (Ch. 11). `take(n)` turns an `Infinite` source into a `Finite` one.

```
case s.next() {
  line: Str -> process(line)
  Abandoned -> rollback()
  Closed -> commit()
}
```

#### 10.5.3 Ownership and rules

- Stream ends are bindings-only, like refs. Each end is captured by exactly one branch or task; capturing it in two is a compile error. Within its task an end may be passed as a parameter.
- A stream does not outlive the scope that uses it.
- `put` and `next` are suspension points. They are forbidden in `atomic` blocks and update closures. Cancellation takes effect at them, as at the other points of §10.4.
- I/O reads are not streams: files and connections are read directly, with errors in the read result (Chapter 15). A producer task that reads a file handles its errors and puts the values into its sink.
- `Seq.toSource()` gives a pull source that computes each element on `next`, with no task and no buffer.

```
let (sink:, source:) = stream[Str](capacity: 16)
let done = all(
  producer: { -> sink.putAll(file.lines()) },
  consumer: { -> for line in source { process(line) } },
)
```

### 10.6 Hubs

A hub is a shared channel whose producers and consumers join and leave at runtime. There are two kinds, differing only in distribution:

```
pub opaque type FanOut[T](handle: RuntimeHub)  // each value to exactly one consumer
pub opaque type Broadcast[T](handle: RuntimeHub)  // each value to every consumer
```

- `fanOut[T](capacity: Int) -> FanOut[T]` and `broadcast[T](capacity: Int) -> Broadcast[T]` create a hub. Like `stream`, they are ordinary functions that wrap a runtime handle; the opaque types' constructors stay hidden.
- `hub.sink()` joins as a producer and returns a new `FiniteSink[T]`. `hub.source()` joins as a consumer and returns a new `Finite[T]`. Each end has one owner, as for streams; closing it leaves the hub without ending it.
- `hub.seal()` admits no further producers. Consumers read `Closed` once the hub is sealed and every producer has closed.
- A producer that vanishes without closing is removed like one that left, and the others carry on. Consumers then read `Abandoned` at the end instead of `Closed`.
- `FanOut` hands each value to whichever consumer asks first: a work queue, or fan-in when there is one consumer. `release(n)` makes `n` waiting consumers read `Closed`, which is how workers are scaled down.
- `Broadcast` keeps a buffer per consumer; `put` waits for the slowest, and `tryPut` reports `Full` if any buffer is full. A consumer that joins late receives values from its join point on.
- A hub is bindings-only but may be captured by several tasks, since sharing is its purpose.

Ends are requested before `seal()` and handed to exactly one task each, so membership is deterministic:

```
let jobs = fanOut[Image](capacity: 64)
let done = all { g ->
  let feed = jobs.sink()
  g.start { -> feed.putAll(images) }
  jobs.seal()
  for _ in 1..4 {
    let src = jobs.source()
    g.start { -> for img in src { save(resize(img, width: 256)) } }
  }
}
```

## 11 Signals and lifecycle

Signals are the type-safe way to move effects such as logging and notifications out of scopes where I/O is forbidden. A signal is emitted as a value and handled later, outside the forbidden scope.

### 11.1 Signal types

1. Every signal type must spread a parent signal type, so handlers can use the parent in a catch-all clause, as `case` does for errors.
2. Field-less category parents such as `Signal` and a module’s own signal parent are `distinct`, so only types that explicitly spread them belong to them.
3. Signal types must be `Solid` (§3.11): closures only if they are Pure and capture only Solid values, validated at compile time, never a runtime error.
4. `Secret` values can never appear in a signal.
5. The standard signal types live in the standard library.

```
pub distinct type ShopSignal(..Signal)
type OrderPlaced(..ShopSignal, orderId: Str, total: Fixed[2])
```

### 11.2 Emitting

`emit` sends a signal. Qualifiers choose when it is delivered relative to the surrounding block:

| Form | Delivered when |
| --- | --- |
| `emit ok S` | The block commits successfully |
| `emit fail S` | The block fails; works in any block that can fail, including tasks, not only atomic blocks |
| `emit retry S` | A transaction attempt is discarded and rerun |

```
atomic {
  stock.update { s -> s.remove(item) }
  orders.update { o -> o.add(order) }
  emit ok OrderPlaced(orderId: order.id, total: order.total)
  emit retry Contention(resource: "stock")
}
```

An unqualified `emit S` is delivered as soon as it is safe: immediately outside transactions, and on commit inside an `atomic` block or update closure, never from a discarded attempt. `ok` and `fail` bind to the innermost block that can succeed or fail, including tasks. Most code needs no qualifier.

### 11.3 Signal handlers

A signal travels up the scope tree, including across task boundaries, to the nearest enclosing handler for its type. A signal handler is a statement `on S { s -> … }` with a signal type `S`. It covers the rest of its block, including everything called from there and every task started there. Unlike a trap handler (§8.3.1) it returns `()` and the emitting code continues: signals carry domain or logging information, and a block may emit any number of them.

```
fn dashboard(id: Str) -> Dash | LoadError {
  on CacheMiss  { s -> metrics.count(s.key) }
  on Contention { c -> log(c) }
  let d = all(
    user: { -> loadUser(id) },
    posts: { -> loadPosts(id) },
  )
  Dash(user: d.user, posts: d.posts)
}

fn checkout(cart: Cart) -> Receipt | PaymentError {
  on OrderPlaced { s -> mailer.confirm(s.orderId) }
  placeOrder(cart)
}
```

Rules:

- A parent signal type catches its subtypes. When several handlers of one block match, the most specific wins.
- Handlers may do I/O. A handler runs in the emitting task at delivery time, so order is kept and a slow handler slows its emitter. To decouple them, a handler forwards into a hub with `tryPut`.
- Inside a handler, `emit s` passes the signal on to the next outer handler.
- Signals from an `atomic` block go to the handlers of whatever encloses it.
- A signal that no handler takes reaches the root, whose default handler writes it to stderr with its automatic `Show`. `main` may install its own handlers to replace this.
- Emitted signal types never appear in signatures, and the compiler does not prove that every signal is handled. Matching happens at runtime by the signal's type. Library code can emit without changing its callers' types; the root default keeps unhandled signals visible.

> **Hint.** `emit retry` exists so that contention from rerun transactions is visible, for example in logs.

### 11.4 Lifecycle handlers with on

`on H f` attaches a lifecycle handler to a type: the runtime or standard library calls `f` at a point in the value's life. Lifecycle handlers are never used for I/O conditions such as a closed connection (§15.2).

1. The declaring type must be nominal: `distinct`, or `opaque`, which implies it. Structural types merge, and a merged type must not end up with two handlers.
2. Each lifecycle kind `H` is a standard-library type spreading the distinct parent `LifecycleHandler`. Its `HandlerForm[…]` constraint prescribes the form its handler must have, including the return type.

   The type arguments of a form may end with an `is` clause, which requires the markers of whatever the form constrains: in `HandlerForm[(T) -> Bytes, is Pure]` the handler must be `is Pure`.
3. The compiler infers `H`'s type parameter from the declaring type; a handler that does not fit the form is a compile error.
4. A lifecycle kind's form may be a union of function types. A type declares at most one handler per kind, and the handler must fit exactly one member (§3.6); an overloaded handler name fitting several members is a compile error (§5.6.1).
5. New lifecycle kinds are new standard-library types, never new syntax.

```
pub distinct type LifecycleHandler
pub distinct type Dispose[T](..LifecycleHandler) where HandlerForm[(T) -> ()]
pub distinct type Encode[T](..LifecycleHandler) where HandlerForm[(T) -> Bytes, is Pure]
pub distinct type Decode[T](..LifecycleHandler) where HandlerForm[(Bytes) -> T | DecodeError, is Pure]
pub distinct type Embed[T](..LifecycleHandler)
  where HandlerForm[((Bytes) -> T | EmbedError) | ((Str) -> T | EmbedError), is Pure]
```

`Embed` accepts either handler form; a type declares exactly one. A `Str` handler receives the resource only after the compiler has validated it as UTF-8, so text parsers never handle encoding (§18.4.1).

### 11.5 Dispose\[T\]

When a value is removed, the runtime runs `Dispose[T]` handler. A type declares its cleanup with an `on Dispose` clause that names a function or a closure.

```
pub opaque type Db(handle: CPtr[DbHandle])
  on Dispose closeDb

fn closeDb(db: Db) -> () { sqlite3_close(db.handle) }
```

The compiler infers `T` from the declaring type; naming a handler for the wrong type is a compile error. Cleanup concerns the typed value (the `Db`), not the raw pointer. There is no `drop` keyword.

### 11.6 Debugging

Debug output is not I/O that bypasses the rules. The `debug` module collects debug information and routes it, using the same deferral mechanisms as signals.

## 12 Collections and strings

Lists, maps and 2D grids are the basic collections. They get literal syntax and compiler support, and all are immutable, persistent structures.

### 12.1 Lists

```
let xs = [3, 1, 2]
let ys = xs.append(4)  // xs is unchanged
let sorted = xs.sort()
```

Indexing a list or grid out of range traps. `get` returns an `Option` instead.

```
let xs = [1, 2, 3]
xs.get(5)  // ⇒ Empty
xs[5]  // trap: index out of range
```

### 12.2 Maps

```
let ages = ["ada": 36, "alan": 41]
let none: Map[Str, Int] = [:]
let a = ages["ada"]  // Option[Int]
let older = ages.set("ada", 37)
```

- Map indexing returns an `Option`.
- Merging two `SortedMap`s requires an explicit comparator.
- `Map` iteration order is unspecified. `SortedMap` iterates in key order, given by the `Ordered` form or by an optional comparator.
- `Set` and `SortedSet` mirror the two map types. There is no set literal; a list literal becomes a set by context, as in `let s: Set[Int] = [1, 2]`.

### 12.3 Grids

A `Grid[T]` is a strictly two-dimensional matrix. Rows are separated by `;` in literals. Rows and columns are both list-typed (columns are strided lists), so every list function applies to them.

```
let m = [1, 2, 3;
         4, 5, 6]
let row0 = m.row(0)  // List[Int]: [1, 2, 3]
let col1 = m.column(1)  // List[Int]: [2, 5]
```

> **Hint.** Grids are intentionally never more than 2D. Crag is not a scientific language; n-dimensional arrays belong in a library.

### 12.4 Slices

A slice is a view that shares storage with its source. Since values are immutable, sharing is invisible to the program.

```
let middle = xs.slice(1..2)
```

### 12.5 Strings

`Str` is UTF-8 text. It has no integer indexing and does not implement the list form. Positions are obtained from explicit index functions and used with substring functions.

```
let s = "Grüße, Crag"
let i = s.indexOf(",")  // Option of a string index, not an Int
let head = i.then { at -> s.substring(before: at) }
```

### 12.6 Bytes and code points

Conversion between byte data and `Str` works in both directions; decoding checks UTF-8 validity and returns an error on failure. `CodePoint` represents one Unicode scalar value and can be examined and constructed.

`Bytes` has typed accessors for binary formats for every sized integer type (§3.1.3), such as `readUInt32(at:, endian:)` and the matching `write…` functions.

### 12.7 Implementation note

Maps and the primitives for linked structures live in the runtime, outside the reference-counted heap. The standard library builds its common collection forms on these optimized primitives (Chapter 13).

Collections iterate by pushing each element to a closure. The body of a `for` and the closures passed to collectors are inlined, so iteration compiles to a plain loop. `zip` and indexed traversal are runtime primitives.

## 13 Memory model

Memory is managed automatically by reference counting. Programs never free memory explicitly.

### 13.1 Reference counting

Reference counting is sufficient for Crag because values are immutable (so ordinary values cannot form cycles), refs cannot be stored in data structures, and typical programs are not pointer-heavy.

Counting is scope-based: a binding holds its reference until the end of its scope, and the optimizer removes redundant count operations. Counts are always atomic, so a value crosses tasks without conversion.

A closure the compiler infers does not escape lives on the stack, and is inlined into known higher-order calls such as collection functions. Escaping closures are heap-allocated and counted.

### 13.2 Runtime-managed structures

Maps and linked structures are built from runtime primitives whose memory lives mostly outside the reference-counted heap. The standard library layers its collection forms on these primitives.

Map nodes are reference-counted inside the runtime; no part of Crag uses tracing collection.

Linked and cyclic data uses arena primitives: nodes live in one flat store and link to each other through typed handles, so a whole structure carries a single count. Handles are generational. Dereferencing a handle whose node was removed traps; `get` returns `T | Empty`.

```
var level = Graph[]  // name provisional
let door = level.add(Door)
level = level.remove(door)
level.get(door)  // ⇒ Empty
level[door]  // trap: stale handle
```

The runtime has no cycle collection. Cyclic data belongs in arenas; refs cannot form cycles, since no stored value can hold a ref or a closure that carries one (§3.12).

### 13.3 Disposal

When the last reference to a value goes away, the runtime runs the type’s `on Dispose` handler, if any (§11.5). Values of `Secret` types have their memory wiped on dispose.

Two markers decide when the handler runs:

| Marker | Handler runs |
| --- | --- |
| `Immediate` | At the drop, on the thread that dropped the last reference |
| `Deferred` | Later, during deferred teardown (§13.5), possibly on a background thread; the handler must be thread-safe |

```
pub opaque type File(fd: Int) is Immediate on Dispose closeFile
```

1. A type with a dispose handler and neither marker is `Deferred`. Standard library resource types *should* be `Immediate`.
2. A type containing an `Immediate` value is `Immediate`, decided per generic instantiation: `List[File]` is `Immediate`, `List[Int]` is not. This silently overrides a declared `Deferred`.
3. An `Immediate` structure is never queued for deferred teardown.
4. A trap unwinding to its handler (§8.3.1) still runs the `Immediate` handlers of the values it drops.
5. A trap inside a dispose handler emits a trap signal (§8.3), and teardown continues. A type whose release can fail *should* offer an explicit `close` that reports errors; the handler is then a fallback.

### 13.4 Persistent versions

“Updating” a collection or record creates a new version that shares unchanged structure with the old one. The compiler may update in place when it proves the old version has no other user.

A rebinding of the form `v = f(v, ...)`, or `v = v.f(...)` with UFCS, releases the variable's reference before the call, so a uniquely held value is updated in place. Any other update copies the changed path.

```
var xs = [1, 2, 3]
xs = xs.append(4)  // in place: xs held the only reference
let ys = xs
xs = xs.append(5)  // copies: ys shares the old version
```

> **Hint.** Because sharing is invisible, write code as if every update copies; the compiler and runtime make it cheap.

### 13.5 Allocation and teardown

The runtime allocates from per-thread heaps with free lists split by object size, in the style of mimalloc. Freeing from another thread stays cheap.

Dropping a large structure that is not `Immediate` queues its teardown, which runs gradually or on a background thread, so a single drop never stalls the program. `Deferred` handlers inside it run during that teardown. The size threshold is implementation-defined.

### 13.6 Stacks and limits

Crag has no runtime options or static limits for memory. The heap grows until the operating system intervenes, as in any POSIX process; running out of memory ends the program and is not a trap.

Task stacks are growable, following Go's measurements:

| Property | Value |
| --- | --- |
| Initial size | 2 KB, adapted to observed average use |
| Growth | Copied into a stack twice the size when a function needs more room |
| Maximum | 1 GB on 64-bit systems; reaching it traps (§8.3) |

Because stacks move, nothing outside a stack may point into it. Foreign calls therefore run on a separate fixed-size system stack.

## 14 Modules and packages

### 14.1 Modules

1. Each file is one module. Directories are only namespaces; a subdirectory holds submodules.
2. Everything is private by default. `pub` exports a declaration.
3. A function lives only in its own module, but can be imported into other namespaces.
4. Import cycles are not allowed.
5. A `pub` signature must not mention a private type.

**Module paths.** A dotted path names a file: `a.b.c` resolves to `a/b/c.crag`, and `a.b.c.d` to `a/b/c/d.crag`. Resolution walks the segments from the left. A segment that names a directory descends into it; the first segment that names a file is the module; any segment after it names an element of that module (`a.b.c.area` is the element `area` of `a/b/c.crag`). A path that ends on a directory is the directory shorthand of §14.2.

A module file and a directory in the same directory may not share a name: `a/b/c.crag` beside `a/b/c/` is an error. So every path has exactly one reading.

### 14.2 Imports

| Form | Effect |
| --- | --- |
| `import geo.shape` | All public elements of module `shape` enter the current namespace |
| `import geo.shape.area` | Only `area` |
| `import geo.shape.area as surface` | `area`, renamed to `surface` |
| `import geo.shape.{area, perimeter}` | A selection |
| `import geo` | Shorthand for importing every module directly in directory `geo` (non-recursive) |
| `import geo.{shape, point}` | Selected modules of a directory |

There are no module-qualified references: `import foo as bar` does not exist, and renaming applies only to individual elements.

### 14.3 Merging and collisions

With structural typing, names mostly serve the reader. When imports meet:

- Indistinguishable types (same name and fields) merge silently. `distinct` types are the exception.
- Functions with the same name but different signatures merge into one overload set.
- Overloads from different modules are never ranked against each other (§5.6.1). A call with viable candidates from several modules is a compile error that names every candidate and its module; the importing module fixes it with a selective import or a rename.
- The same name with an identical signature is a clash and must be resolved with `as` at import.
- Importing the same element more than once from the same module is not a collision. It is one element, and the repeated import is a no-op.
- Every other collision is a compile error.

> **Hint.** A new function in a dependency that creates a clash is expected to arrive with a new module version, so collisions surface at upgrade time, not by surprise.

### 14.4 Uniform call syntax across modules

Every visible function whose first parameter accepts a type is callable on values of that type with `.`, without a module prefix (§6.3). Completion and auto-import are REPL features, not part of the module system.

### 14.5 Packages

A package is a visibility boundary. It declares what it exports and what it imports.

1. A package may export only modules it owns.
2. Versions follow semantic versioning: a breaking change is a major bump. Patch levels are optional.
3. Every package import states the exact version it requires.
4. A package, including the application, may import only one major version of a given package.
5. Different major versions of one package may coexist in an application only through transitive dependencies; each package sees only the major it declared.
6. The application settles on one version per major.
7. Every package must state the runtime version it requires.
8. Each dot in a package name is a directory level: the package `acme.geo` lives under `acme/geo/`, and its modules resolve below that path (§14.1). A package has no root module, because that would be a file beside its own directory.
9. The package names `std` and `std.*` are reserved. `std` is bundled with the runtime and resolved from the runtime's installation, never from a registry (§19.9).

#### 14.5.1 The manifest

Every package, including an application, has a manifest named `package.crag` at its root. It uses the words and selection syntax of module imports (§14.2) and allows only the declarations below: no expressions and no logic.

```
package shop 2.1
runtime 1.4

name "Shop"
summary "Carts, orders and payments"
description """
    A storefront toolkit with typed money,
    atomic stock updates and pluggable payment providers.
    """

export shop.cart
export shop.{order, payment}

import http 3.2.1
import json 1.8
import billing 1.2 from "git:…"
import dev testkit 0.9
```

| Declaration | Meaning |
| --- | --- |
| `package N V` | The package's name and version. Module paths start with the name. |
| `runtime V` | The runtime version the package requires. |
| `name`, `summary`, `description` | Optional text: a display name, a short description and a long description. |
| `export M` | A module the package owns and makes visible to importers. |
| `import P V` | A package dependency stated as the exact version `V`. The build may settle on a higher version of the same major (see Resolution). Its exported modules become importable by code. |
| `import P V from "…"` | The same, from a given source instead of the registry. |
| `import dev P V` | A development or testing dependency, visible only to test and tool modules and never shipped. |
| `main M` | For an application: its entry module. An application exports nothing. |

**Resolution.** Within each major version, the application settles on the highest version any manifest requires. The result follows from the manifests alone, so the same manifests always give the same build and no lock file is needed. The SBOM records the content hash of every resolved package (§16.7); the build verifies each package against the committed SBOM and refuses on a mismatch until the SBOM is regenerated on purpose.

## 15 Runtime I/O

The runtime provides powerful, abstract I/O primitives. Most programs never touch the FFI for I/O.

### 15.1 Abstract I/O types

Programs see abstractions, not operating-system objects. Sockets, pipes and descriptors exist only inside the runtime implementation.

| Type | Abstraction of |
| --- | --- |
| `Connection` | A bidirectional byte stream (TCP, TLS, pipe, …) |
| `Listener` | A source of incoming connections |
| `Datagram` | Message-oriented endpoints (UDP and similar) |
| `File` | A file in a file system |
| `Process` | A child process and its streams |

Each is an ordinary Crag type with markers, value conditions and lifecycle handlers.

### 15.2 End of stream

A peer closing a connection is a normal result of a read, not an event. There is no `on Closed` handler: `on` clauses on a type are reserved for lifecycle (§11.4), and `on` statements handle only signals (§11.3) and traps (§8.3.1).

```
case conn.read() {
  bytes: Bytes -> handle(bytes)
  Closed -> finish()
  pass
}
```

### 15.3 Cryptography

TLS and all other standard cryptographic protocols are runtime primitives, not libraries bound through the FFI. Keys, tokens and passwords should use `Secret` types (§3.11).

### 15.4 Cancellation

What happens to pending I/O when a task is cancelled depends on the execution semantics of the enclosing combinator (§10.4).

Cancellation also stops work that never suspends (§10.4), so `within` (§19.5) bounds computation as well as I/O.

### 15.5 Where I/O is forbidden

I/O is never allowed inside ref update closures or atomic blocks. Use signals (Chapter 11) to perform effects after the block commits or fails.

### 15.6 Standard input, output and error

`std.io` serves two kinds of program.

- **Simple programs** use `print(text: Str)` and `printLine(text: Str)`, which write to standard output and return `()`. Each call is atomic, so lines from concurrent tasks never interleave. Failing to write, for example to a closed pipe, is a `Fault` trap (§8.3): an environment condition, not a domain outcome.
- **Programs that must handle failure** use the byte-stream handles `stdin()`, `stdout()` and `stderr()`, whose functions return error values: `write(o, bytes) -> () | IoError`, `writeLine(o, text) -> () | IoError`, `readLine(i) -> Str | Closed | IoError`.

```
import std.io.printLine

fn main() {
  printLine("Hello, world!")
  printLine("Second line, no error handling needed")
}
```

## 16 Foreign function interface

The FFI binds C libraries. It is deliberately narrow in the first version: C symbols come in through `import`, foreign state is held in `ext` bindings, and cleanup is tied to typed values.

### 16.1 Binding C symbols

C functions are bound with `import`; there is no separate `foreign` keyword. The standard module `std.c` provides the C-level types. Their names carry a `C` prefix (`CInt`, `CStr`, `CPtr[T]`, `COut[T]`, `CF32` and the other narrow types), so they never clash with prelude types such as `Int` and `Str`; Crag has no module-qualified references (§14.2).

```
import cLib("sqlite3").{
  sqlite3_open(path: CStr, db: COut[CPtr[DbHandle]]) -> CInt,
  sqlite3_exec(db: CPtr[DbHandle], sql: CStr) -> CInt is Errno,
  sqlite3_close(db: CPtr[DbHandle]) -> CInt,
} is ThreadSafe
```

### 16.2 Pointers

`CPtr[T]` is a pointer tagged with a phantom type `T`, so handles of different libraries cannot be mixed. Plain `CPtr` is `void*`.

### 16.3 Parameters and results

- `COut[T]` parameters come back as fields of a result record; the C return value is the field `result`.
- `errno` capture is opt-in with the marker `is Errno` after a function's signature in the import (§16.1). It applies to that function only.
- `CF32` and other narrow numeric types require explicit conversion; narrowing a value out of range traps.

```
let r = sqlite3_open(CStr(path))  // Out params are omitted at the call; r: (result: CInt, db: CPtr[DbHandle])
```

### 16.4 Threading

Each foreign library carries a thread-safety marker:

| Marker | Meaning |
| --- | --- |
| `ThreadUnsafe` | Default. Calls are never made concurrently. |
| `ThreadSafe` | Calls may run on any thread concurrently. |
| `ThreadBound` | All calls must happen on the thread that created the state. |

The marker follows the closing brace of the `cLib` import (§16.1); without one, the library is `ThreadUnsafe`. Thread safety belongs to the library, not to one import, so every import of the same library must state the same marker, a missing one counting as `ThreadUnsafe`. A mismatch is a compile error naming both imports.

### 16.5 Foreign state and cleanup

Handles to mutable foreign state are held in `ext` bindings (§9.6). Cleanup is declared on the Crag type that wraps the handle with `on Dispose` (§11.5).

```
pub opaque type Db(handle: CPtr[DbHandle])
  on Dispose closeDb

fn openDb(path: Str) -> Db | DbError {
  let r = sqlite3_open(CStr(path))
  if r.result == 0 { Db(handle: r.db) } else { DbError(code: r.result) }
}
```

> **Hint.** `.then` applies only to `Option[T]` (§6.8). Fluent chaining for other results, such as C call records, is deferred (Appendix C).

### 16.6 Callbacks

In the first version, only capture-free top-level functions can be passed to C as callbacks.

### 16.7 Native library versions

1. The version of each native library is checked at build time and again at program start, since the host may differ.
2. An application may optionally declare an allow list of native dependencies.
3. Crag tooling produces an SBOM (software bill of materials), which can serve as that allow list.

## 17 The REPL

The REPL follows exactly the same language rules as source files. It adds discovery and a controlled way to redefine things.

### 17.1 Same rules, no exceptions

An ad-hoc definition that clashes with an imported name is an error in the REPL, just as in a module; choose a different name.

### 17.2 Discovery

After typing `p.`, the REPL lists every available function that takes the type of `p` as its first argument (§6.3). Completion and auto-import are REPL features.

```
crag> let p = Point(x: 1, y: 2)
crag> p.
  distance(b: Point) -> Float        geo.point
  translate(dx: Int, dy: Int) -> Point  geo.point
  x: Int                              field
  y: Int                              field
```

Values of `Secret` types are hidden when printed or inspected.

### 17.3 Redefinition and `rebind`

Names are not versioned. Redefining one of your own session definitions requires an explicit rebind operation, which also rebinds every definition that depends on it. Rebinding exists only in the REPL.

```
crag> fn tax(x: Fixed[2]) -> Fixed[2] { x * 0.19 }
crag> fn gross(x: Fixed[2]) -> Fixed[2] { x + tax(x) }
crag> fn tax(x: Fixed[2]) -> Fixed[2] { x * 0.07 }
error: tax is already defined in this session; use :rebind
crag> :rebind fn tax(x: Fixed[2]) -> Fixed[2] { x * 0.07 }
rebound tax (1 dependent: gross)
```

## 18 Introspection and code transport

Crag generates code without macros that invent syntax or names. Reflection happens only at compile time, generated code never introduces names, and code travels between processes as checked data.

### 18.1 Principles

1. **A ladder of power.** Each rung is used only when the one below cannot do the job: generic functions over fields (§18.2), type functions (§18.3), compile-time evaluation (§18.4). Quote and splice (§18.5) is deferred until real code demands it.
2. **Names are written by humans.** Generators may produce type shapes and function bodies. Every name that enters a module scope appears literally in source. Field names produced by a type function are scoped to their type, not the module. Mass-producing names is a job for the REPL, which writes ordinary source.
3. **Reflection is compile-time only.** A running program cannot ask a value for its type's fields. Values produced at compile time, such as a kept type descriptor or a reified closure, are ordinary `Solid` data at runtime.
4. **Compile-time evaluation is implicit.** The compiler evaluates whatever it can. A type position forces compile-time evaluation; a type expression that cannot be evaluated is a compile error, never a runtime fallback.
5. **Generated code obeys every rule.** Its output is type-checked after expansion and is subject to import clashes, forbidden forms, `pub` visibility, and the ban on private types in public signatures.

With structural typing, per-type generated code fights type identity: two packages deriving `show` for the same-shaped record would clash (§14.3). One generic function specialized by the compiler avoids this.

### 18.2 Generic functions over fields

Where `Fields[R, F]` holds (§4.5), `r.fields` is the sequence of `R`'s fields. Each element has a `name` and a `value` of that field's concrete type. The sequence exists only at compile time: iteration over it is always unrolled when the function is specialized for a concrete `R`, so dispatch stays static.

```
pub fn show[R](r: R) -> Str where Fields[R, Show] {
  r.fields.map { f -> "{f.name}: {f.value.show()}" }.join(", ")
}
```

This rung covers the usual derivations: `Show`, `Eq`, `Hash`, `Ordered`, encoding and debug views. A type that forbids a form (`is not Show`) never satisfies `Fields[R, Show]` for a record containing it, so the ban holds without extra rules.

Outside its module, an `opaque` type exposes no fields, so `Fields` never holds for it there.

### 18.3 Type functions

A type function is an `is Pure` function from types to types, evaluated by the compiler. It generalizes the type mapping functions of §8.4. Its results are ordinary structural types: they merge and compare exactly like hand-written ones.

Types are values of the compiler-owned type `Type`, which exists only at compile time. A function whose parameters or result involve `Type` is a type function: it is implicitly `is Pure` and runs only in the compiler.

- The right side of `type X[…] =` is a type or a compile-time expression of type `Type`. Syntax tells them apart: a type never has a name followed by `(` (Appendix D.6), so `Option[Int]` is a type and `sqlRow(schema)` an expression.
- Inside such an expression, type parameters are `Type` values. `R.fields` is the list of fields `typeInfo` describes (§18.4), each with a `name`, a `type` and an optional `default`. Bracket application on `Type` values yields a `Type`: `Option[f.type]`.
- `std` provides the builders `record(fields)` and `union(types)`, and accessors such as `members(T)` for a union and `.result` for a function type.
- Where a `Type` is expected, a type name denotes the type itself, not its constructor.
- A type function is applied with brackets to types (`Partial[User]`) and with parentheses to values (`sqlRow(schema)`).

```
type Partial[R] = record(R.fields.map { f ->
  (name: f.name, type: Option[f.type], default: Empty)
})
type UserPatch = Partial[User]
let p = UserPatch(email: "ada@example.org")  // the other fields are Empty

embed schema: Str from "schema/user.sql"
type UserRow = sqlRow(schema)

pub fn sqlRow(sql: Str) -> Type {
  record(parseColumns(sql).map { c -> (name: c.name, type: sqlType(c.kind)) })
}

fn sqlType(kind: Str) -> Type {
  case kind {
    "INTEGER" -> Int
    "TEXT" -> Str
    "REAL" -> Float
    _ -> Bytes
  }
}
```

The name of the resulting type is always written in source. Only its shape is computed.

### 18.4 Compile-time evaluation

Any `is Pure` function whose inputs are known at compile time may run in the compiler. The evaluator doing this is the REPL's evaluator. Compile-time code performs no I/O, without exception. External data enters a program only through `embed` declarations (§18.4.1), which are resolved as source, before evaluation.

`typeInfo[T]` is a `Solid` descriptor of `T`: its name, fields (name, type, default), parent spread, markers, conditions, and whether it is `distinct` or `opaque`. Outside an `opaque` type's module, the descriptor shows the name and markers but no fields. A descriptor costs nothing at runtime unless the program keeps it, in which case it becomes a constant.

Compile-time evaluation is bounded by a step limit. Running out is a compile error at the expression that started the evaluation.

#### 18.4.1 Embedding resources

`embed` declares a module-level binding whose value comes from a resource. It is a special `let`: immutable, `Solid`, and typed by its annotation.

```
embed schema: Str from "schema/user.sql"
embed cfg: Toml from "config/limits.toml"
embed logo from "assets/logo.png"  // Bytes by default

let limits: Limits = !! cfg.decode[Limits]()
```

1. `embed` appears only at module level. `from` is a contextual keyword, meaningful only after `embed`.
2. The source is a string literal, never computed. A relative path names a file in the module's package, resolved against the module's file; paths outside the package are a compile error.
3. The compiler reads the source as part of the module's source text. Compile-time code never performs the read, so it stays Pure.
4. The annotated type decides how the resource becomes a value. Without an annotation it is `Bytes`. `Str` requires valid UTF-8. Any other type must declare an `on Embed` handler (§11.4).
5. The handler runs at compile time under the compile-time step limit. An `EmbedError` is a compile error at the `embed` line and may carry a line and column inside the resource.
6. Every source is visible to parsing alone, so the SBOM, build tooling and REPL find all resources without evaluation. Changing a resource is a source change: the REPL rebinds dependents and body hashes change.

Format types keep parsers reusable: any module may declare one, such as `Toml`, and ordinary compile-time evaluation converts it to a domain type. A domain type with one canonical file format may declare `on Embed` itself. Whether embedded bytes reach the binary is left to the optimizer.

### 18.5 Quote and splice (deferred)

Crag does not yet have typed code values. If real code demands them, they must follow §18.1: a `Code[T]` value is a typed, hygienic expression, checked against `T` after expansion. A function body may be spliced under a hand-written signature. A generator never introduces a name.

```
pub fn encode(u: UserRow) -> Bytes = binaryEncoder[UserRow]()
```

### 18.6 Transporting code

`Expr[F]` is a reified function of type `F`. A closure literal becomes an `Expr` when its parameter type asks for one, by context typing as with literals (§2.6). A named top-level `pub` function may also be passed; it travels as a reference.

```
fn remoteFilter[R](node: Node, p: Expr[(R) -> Bool]) -> List[R] | RemoteError

node.remoteFilter { u -> u.age >= minAge }
```

At the closure literal, the compiler requires:

1. the body is `is Pure`, so transported code performs no I/O;
2. every capture is `Solid` and not `Secret`; capturing a `ref`, `ext` or a plain closure is an error.

Locally, an `Expr[F]` is usable anywhere an `F` is expected.

An `Expr` value holds:

- **the tree:** the body as `Solid` data, with calls to `pub` functions as references (package, major version, module, name, signature, and a hash of the callee's body);
- **bundled helpers:** non-`pub` functions the body calls, attached as definitions, because a receiver may never resolve another module's private names;
- **captures:** the values of the capture slots;
- **a content hash** of the normalized tree, which receivers may use to cache compiled forms.

`Expr` is `Solid`: holding a tree cannot fail, and running one reports policy failures as values (§18.7), while a trap in the body behaves as anywhere else (§8.3.1). Records may therefore carry code, for example `type Job(name: Str, select: Expr[(Row) -> Bool])`.

### 18.7 Receiving code

A tree is data, and data can be forged. A receiver trusts nothing the sender claims. Before running an `Expr`, it:

1. resolves every reference against its own loaded packages;
2. re-type-checks the tree against the type it expects;
3. re-verifies `is Pure` and `Solid` captures, including bundled helpers;
4. runs the body under step and memory limits.

Correctness requires only that types match. Which code a receiver accepts is its own policy:

```
type Accept = Exact | SameMajor | Signature

fn run[A, B](e: Expr[(A) -> B], input: A, policy: Policy)
  -> B | Unresolved | IllTyped | Impure | StepLimit | MemoryLimit
```

| `Accept` | A reference resolves when |
| --- | --- |
| `Exact` (default) | the callee's body hash matches the sender's |
| `SameMajor` | the package major version matches |
| `Signature` | module, name and signature match and the types check |

`Policy` bundles `Accept` with the step and memory limits. Each resolution accepted despite a body-hash mismatch emits a signal, so divergence is visible in logs. Results must be `Solid`, because they travel back. Termination and cost are never proven by types; limits are runtime policy, and exceeding them is a value, not a trap.

`distinct` and `opaque` types are nominal, so a tree using one needs its declaring module on the receiver under every policy. Otherwise `run` returns `Unresolved`.

### 18.8 Transporting values

A value can travel if and only if its type is `Solid` and not `Secret`, and it holds no closures other than Expr trees. Code is one kind of value that qualifies.

| Travels | Does not travel |
| --- | --- |
| Records, collections, primitives | Plain closures (compiled code, not trees) |
| `distinct` types | `ref` and `ext` (bindings, never values) |
| `opaque` types with a codec (§18.9) | Types with `on Dispose` (runtime or foreign handles) |
| `Expr` values | `Secret` values |
| Signals |  |

```
fn decode[T](bytes: Bytes, policy: Policy) -> T | Unresolved | IllTyped | Invalid | DecodeError | StepLimit | MemoryLimit
```

Value conditions are re-checked on arrival. `decode` checks each value's `where` conditions (§3.10.1) before constructing it, so a forged value that violates a condition yields `Invalid`, never a trap.

### 18.9 Codecs for opaque types

The generic codec cannot see an `opaque` type's fields outside its module (§18.2). An opaque type therefore travels only if its own module declares a codec, as a pair of lifecycle handlers (§11.4):

```
pub opaque type Token(raw: Bytes, issued: Time)
  on Encode encodeToken
  on Decode decodeToken
```

- `Encode` and `Decode` come as a pair; declaring one without the other is a compile error.
- Both handlers are `is Pure`. `Decode` sees untrusted bytes, so it runs under the receiver's policy limits and must build its result through the constructor.
- An opaque type without a codec is not transportable.

Dispose, Encode and Decode are one family: the value leaving existence, leaving the process, and entering one. Plain structural types always use the generic standard-library codec.

### 18.10 Implementation layers

Transport follows the pattern of refs and collections: compiler-owned types, runtime primitives, and a standard library written in Crag.

| Layer | Owns |
| --- | --- |
| Compiler | `Expr[F]`, reifying closure literals, bundling private helpers, inferring `Pure` and `Solid`, `typeInfo`, the canonical tree normalization and hash |
| Runtime primitives | Resolving references and re-type-checking trees; metered evaluation (step and memory limits) |
| Standard library | `Policy`, `Accept`, the error types, `run`, `encode` and `decode` as generic functions over `Fields`, transport over the abstract I/O types (§15.1) |

A program carries the checker at runtime only if it uses `run` or `decode`. Writing the codec in Crag tests the design: if the standard library cannot express its own codec with §18.2–18.4, those rungs are too weak.

> **Provisional.** `Expr`, `Policy`, `run` and `decode` are working names.

### 18.11 Translation vocabularies

A translator turns an `Expr` tree into another language, such as SQL. It is ordinary Crag code in a library, walking the tree as data. Its vocabulary is the set of `pub` functions it can express in its target.

```
let sql = Vocabulary[SqlNode](
  equals: binary("="),
  compare: comparison,
  and: binary("AND"),
  startsWith: { a, b -> like(a, concat(b, "%")) },
  lower: call("LOWER"),
)

type SqlExpr[F] = Expr[F] where sql.accepts(this)

fn filter[R](t: Table[R], p: SqlExpr[(R) -> Bool]) -> Query[R]

users.filter { u -> u.age >= minAge and u.name.startsWith(prefix) }
```

Rules:

- A vocabulary is a Solid value mapping `pub` function references to target constructs. Field access on a row type becomes a column; literals become target literals. It is extended without new syntax: `sql.with(isVip: call("is_vip"))`.
- Captures always become bind parameters, never text spliced into the target. Injection is impossible by construction.
- A call outside the vocabulary is inlined when its target is a bundled helper or a `pub` function whose body uses only the vocabulary; the body hash guarantees it is the body the sender meant. Any other call is untranslatable.
- A parameter declares its vocabulary with a conditioned alias (§3.10.1). A closure literal is checked at compile time, and a failure names the offending call. An `Expr` arriving at runtime is converted explicitly, `SqlExpr(e)`, which returns `Invalid` if the tree is untranslatable.
- A translator returns a structured target tree with its parameters, such as `SqlQuery`. Rendering to text is the driver's last step.
- Semantic differences between Crag and the target, such as string ordering or overflow, are the translator author's responsibility.

## 19 The standard library

The standard library, `std`, is part of the language. The compiler relies on names it declares, it is versioned with the runtime, and its prelude module std.core is visible in every file.

### 19.1 Compiler-owned, runtime-owned and declared types

Every standard type belongs to one of three kinds. The kind decides who defines the type, never how a program uses it: all three reach programs the same way, through `std`.

| Kind | Types | Meaning |
| --- | --- | --- |
| Compiler-owned | `Int`, `Int8`, `Int16`, `Int32`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Float`, `Fixed[S]`, `Str`, `CodePoint`, `Bytes`, `()`, `Ref[T]`, `Lazy[T]`, `Expr[F]`, `Type`, `Fields[R, T]` | Cannot be written in Crag. The compiler alone knows the representation, types literals by context, folds constants and validates UTF-8. |
| Runtime-owned | `List`, `Map`, `Set`, `Grid` | Storage lives in runtime primitives outside the reference-counted heap (§13.2). The compiler supports their literals and inlines their iteration. |
| Declared in `std`, compiler-known | `Bool`, `True`, `False`, `Option[T]`, `Empty`, the markers, `Signal`, Error, Trap and its family, TrapSignal, `LifecycleHandler`, `Dispose[T]`, `Embed`, `EmbedError` | Ordinary Crag declarations. The compiler refers to them by name for `if`, map indexing, `is`, `emit`, `on` and `embed`. |

### 19.2 Functions on standard types

The types of the first two kinds are owned by the compiler and runtime, but their functions are not. `add(a: Int, b: Int) -> Int`, `equals`, `compare`, the index and substring functions and the collection functions are ordinary `std` declarations whose bodies call compiler intrinsics or runtime primitives. Intrinsics are never visible to user code.

An intrinsic is declared as a `fn` without a body; only `std` may declare one. Every other function has a body, except the signatures in forms (§4.1) and `cLib` imports (§16.1).

The runtime handles inside opaque standard types, `RuntimeGroup`, `RuntimeStream` and `RuntimeHub`, are intrinsic types in the same sense: compiler-owned and visible only inside `std`.

This keeps the operator rule uniform (§6.2): `a + b` always resolves `add`, whether the operands are `Int` or a user's `Vector`.

> **Hint.** This is the layering used for refs, collections and transport (§18.10): compiler-owned types, runtime primitives, and a standard library written in Crag.

### 19.3 The prelude

The module `std.core` is the prelude. The runtime defines it and imports it into every file and every REPL session. Source never needs to name it, but may, for example to rename an element with `as`. No other module is implicit.

- There is no opt-out. `if`, operators, map indexing, `emit`, `on` and traps all depend on the prelude, so a file without it could not express a real program.
- Collisions are errors (§14.3), so prelude names are effectively reserved: a declaration that clashes with one must use a different name.
- A type belongs to the prelude only if a language construct produces or requires it: a literal, a keyword, an operator, a clause, a prefix or `for`. Every standard function on a prelude type belongs to it too: a function whose first parameter is a prelude type and whose other parameters and result are built only from prelude types, type parameters and function types. There are two exceptions: the functions of `std.math`, and functions with the `io` effect (§3.14), such as `print` in `std.io`. Nothing else is in the prelude.

| Group | Contents | Required by |
| --- | --- | --- |
| Numbers | `Int`, `Int8`, `Int16`, `Int32`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `Float`, `NaN` and `number`, `Fixed[S]` with `roundHalfEven`, `roundHalfUp`, `roundUp`, `roundDown`, `floor` and `ceil`; `Int.trunc`, `Int.round`, `Int.floor`, `Int.ceil` | Numeric literals; explicit rounding of fixed-point products and quotients (§3.1.2); float-to-integer conversion |
| Text and bytes | `Str`, `CodePoint`, `Bytes` | String literals; the default type of `embed` (§18.4.1) |
| Collections | `List`, `Map`, `Set`, `Grid` | List, map and grid literals; sets by context (§12.2) |
| Tags and unions | `Bool`, `True`, `False`, `Option[T]`, `Empty`, `.then`; `Ordering`, `Less`, `Equal`, `Greater` | `if`, `case` guards, `and`/`or`/`not`; map indexing, `get`, `?.`; the `Ordered` form |
| Forms and operators | `Eq`, `Ordered`, `Show`, `Hash`, `Iterable`; `add`, `equals`, `lessThan`, `compare` and the other operator functions | Operators (§6.2); `for` and collectors |
| Ranges | `Range[T]`, `RangeFrom[T]`, `Discrete`, `next` | `a..b` and `a..` (§7.4) |
| Type mappings | `discard`, `check`, `expect` and their prefixes | Prefixes (§8.5) |
| Shared state | `Ref[T]`, `update`, `use`, `swap`, `empty` | `ref` and `ext` bindings and their sugar (§9.3) |
| Laziness | `Lazy[T]` | `lazy` (§6.10) |
| Markers | `Solid`, `Pure`, `Secret`, `Immediate`, `Deferred` | `is` clauses |
| Signals, traps and lifecycle handlers | `Signal`, Error, Trap and its family, TrapSignal, `LifecycleHandler`, `Dispose[T]`, `Embed`, `EmbedError` | `emit`, traps, `on`, `embed` |

### 19.4 Module layout

`std` is one package. Files are modules and directories are namespaces (§14.1).

`std` is bundled with the runtime and resolved from the runtime's installation, never from a registry; the package names `std` and `std.*` are reserved (§14.5). The runtime declares which module is the prelude: `std.core` (§19.3). `import std` imports every module directly in the `std` directory (§14.2), including `std.core`, whose repeated import is a no-op (§14.3); `import std.{math, io}` imports a selection.

| Module | Contents |
| --- | --- |
| `std.core` | The prelude (§19.3) |
| `std.math` | Mathematical functions (trigonometry, logarithms, powers, roots) and constants; the one exception to the prelude's function rule (§19.3) |
| `std.time` | Durations, monotonic instants, UTC time, civil dates and times, zones, sleep and timeouts (§19.5) |
| `std.random` | Seeded, reproducible generators (§19.6) |
| `std.env` | Arguments, environment variables, working directory, exit codes, platform constants (§19.7) |
| `std.path` | Absolute and relative paths as structured values (§19.8) |
| `std.coll` | `SortedMap`, `SortedSet`, `Seq[T]`, arena primitives for cyclic data, and conversions from prelude collections to these |
| `std.task` | The combinators `all`, `allDone`, `first`, `firstDone`, `firstResult`, and `Group` with `start` (§10.2) |
| `std.stream` | `stream`, `infiniteStream`, `Sink[T]`, `FiniteSink[T]`, `Source[T]`, `Finite[T]`, `Infinite[T]`, `Sent`, `Full`, `Closed`, `Abandoned`, `FanOut[T]`, `Broadcast[T]` (§10.5, §10.6) |
| `std.signal` | Helpers for routing signals from `on` handlers, such as forwarding into a hub (§11.3) |
| `std.debug` | Collecting and routing debug information (§11.6) |
| `std.io` | `Connection`, `Listener`, `Datagram`, `File`, `Process` (§15.1); file functions take `Path` values (§19.8) |
| `std.crypto` | TLS and the other standard cryptographic protocols (§15.3); secure random bytes as `Secret` values (§19.6) |
| `std.c` | `CInt`, `CStr`, `CPtr[T]`, `COut[T]`, `CF32` and the other C-level types, `cLib`, `ThreadUnsafe`, `ThreadSafe`, `ThreadBound`, `Errno` (Ch. 16) |
| `std.transport` | `run`, `encode`, `decode`, `Policy`, `Accept`, `Encode`, `Decode`, `Unresolved`, `IllTyped`, `Invalid` (Ch. 18) |
| `std.test` | Assertions for `test` declarations |

### 19.5 Time

`std.time` keeps measuring elapsed time apart from telling the date.

| Type | Meaning |
| --- | --- |
| `Duration` | A signed span in nanoseconds. Arithmetic traps on overflow, like `Int`. Built with `nanos`, `millis`, `seconds`, `minutes` and `hours`. |
| `Instant` | A reading of the monotonic clock; `Instant - Instant` is a `Duration`. Meaningful only inside one process, so it is opaque with no codec and never travels (§18.9). |
| `UtcTime` | Wall-clock time as nanoseconds since the Unix epoch, in UTC. Leap seconds are smeared, never represented. Solid and transportable. |
| `Date`, `TimeOfDay`, `LocalDateTime` | Civil values in the proleptic Gregorian calendar, with no zone. An impossible date such as February 30 fails its value condition. |
| `Zone` | A time zone from the runtime's time-zone database, encoded by its IANA name |
| `ZonedTime` | A `UtcTime` together with a `Zone` |

- Reading a clock is an effect. `now() -> UtcTime`, `monotonic() -> Instant` and `localZone() -> Zone` are forbidden in ref updates, atomic blocks (§15.5) and compile-time code (§18.4).
- `sleep(d: Duration)` suspends the current task and is cancelled with it (§10.4).
- `within(d: Duration, f) -> T | TimedOut` runs `f` as a scope and cancels it when `d` elapses. It is an ordinary combinator, like those of §10.2.
- Placing a civil time in a zone is fallible and typed: `LocalDateTime.in(z: Zone) -> ZonedTime | Ambiguous | Skipped`. `Ambiguous` carries both candidates of a repeated hour; `Skipped` names the gap of a daylight-saving jump.
- `Zone.named(Str) -> Zone | UnknownZone` looks a zone up by IANA name.
- Formatting and parsing follow ISO 8601 and RFC 3339; parsing returns error unions.

### 19.6 Randomness

`std.random` provides reproducible randomness for simulations, tests and games. It is not for security.

`Rng` is an immutable, seeded generator. A draw returns the value and the next generator, so drawing is pure and allowed anywhere, including atomic blocks.

- `Rng.seeded(n: Int) -> Rng` is pure. `Rng.fromEntropy() -> Rng` reads the operating system and is an effect.
- Draws return a record: `r.int(1..6) -> (value: Int, next: Rng)`. `float`, `bool`, `pick` and `shuffle` work the same way; `pick` yields `Empty` for an empty list.
- `r.ints(1..6) -> Seq[Int]` and the matching forms for the other draws give an infinite lazy sequence (§6.10.1), so most code never threads the generator by hand.
- `r.split() -> (left: Rng, right: Rng)` gives concurrent branches independent generators without a ref.
- The algorithm is fixed for each major version of `std`, so a seed reproduces the same draws on every platform.
- Keys, tokens, nonces and salts come from `std.crypto`, which returns `Secret` values from the operating system's secure source. `Rng` is never `Secret`.

### 19.7 Environment

`std.env` reads the process's own context. Everything in it except the platform constants is an effect.

| Name | Meaning |
| --- | --- |
| `args() -> List[Str] \| NotUtf8`, `rawArgs() -> List[Bytes]` | Program arguments, without the program name |
| `env(name: Str) -> Str \| Empty \| NotUtf8`, `vars() -> Map[Str, Str]` | Environment variables; `vars` skips entries that are not UTF-8 |
| `workingDir() -> AbsPath` | The working directory |
| `programPath() -> AbsPath` | The running executable |
| `ExitCode` | `ExitCode(code: Int)` with `where code >= 0 and code <= 255`, the program's exit status (§19.7.1) |
| `os: Os`, `arch: Arch` | Compile-time constants, with `Os = Linux \| MacOs \| Windows \| FreeBsd` and `Arch = X64 \| Arm64`, so `if os == Windows` folds away |

The environment is read-only. There is no `setVar` and no `changeDir`: both would mutate process-wide state that other tasks and foreign code read without synchronisation. A child process gets its own variables and working directory through `Process` options (§15.1).

#### 19.7.1 The entry point

The manifest's `main` names an application's entry module (§14.5.1), which declares `fn main()`. It takes no parameters; arguments come from `args()`. Its return type decides the exit status:

| `main` produces | Exit status |
| --- | --- |
| `()` | 0 |
| `ExitCode` | its code |
| an error value (§8.1) | 1, after writing the error to stderr with its `Show` |

A trap that no handler takes is written to stderr with its stack, and the process exits with 70 (`EX_SOFTWARE`), so scripts can tell a reported failure from a crash. `main` may install `on` handlers (§8.3.1, §11.3) like any block; they replace the root's default output for what they take.

```
pub type ExitCode(code: Int) where code >= 0 and code <= 255
```

### 19.8 Paths

`std.path` models file-system paths as structured values. It never touches the file system; `File` in `std.io` does.

| Type | Meaning |
| --- | --- |
| `Segment` | One path component: non-empty, with no separator or NUL, and never `.` or `..`. It holds the operating system's native bytes and is shown lossily when they are not UTF-8. |
| `AbsPath` | A root and a list of segments. The root is `/` on Unix, a drive or UNC share on Windows. |
| `RelPath` | Leading parent steps (`..`) and a list of segments |
| `Path` | `AbsPath \| RelPath` |

- Joining uses `/`, which is `divide` (§6.2): `AbsPath / RelPath -> AbsPath` and `RelPath / RelPath -> RelPath`. No overload takes an absolute right side, so joining onto an absolute path is a compile error rather than a silent replacement.
- Parsing text is validated: `Path.parse(Str) -> Path | InvalidPath`, with `AbsPath.parse` and `RelPath.parse` when one kind is required.
- An interior `..` is folded lexically when a path is built. That can differ from the file system when a segment is a symbolic link; `File.canonical` in `std.io` resolves links and is an effect.
- `AbsPath.parent() -> Option[AbsPath]`, since the root has no parent. `name`, `stem`, `extension`, `withExtension` and `relativeTo(a: AbsPath, base: AbsPath) -> RelPath` complete the set.

### 19.9 Versioning

`std` is versioned with the runtime. The runtime version a package requires (§14.5) pins `std` as well; `std` is never declared as a separate dependency.

## 20 Runtime and tooling

The tool `crag` is a single binary. Run without arguments, it opens the REPL, which is also the IDE: code editor, REPL, debugger, hot reload, project and package management in one terminal window. The shell commands (§20.6) build, run, test, package and publish; they are not a debugging interface.

### 20.1 Processes

A session runs three processes.

| Process | Role |
| --- | --- |
| Host | The terminal UI, the compiler service, the file watcher and the package tooling |
| App image | Runs the application. It keeps running across hot reloads (§20.2). |
| Scratch image | Evaluates REPL input. It sees unsaved editor buffers, so functions can be tried before they reach the app. |

- Images are separate processes. A fault in native code or a runaway task kills only its image; the host, the session history and the editor buffers survive. Each image runs the runtime version the project pins.
- `:target scratch` and `:target app` choose where REPL input runs; the default is the scratch image.
- `:pull name` copies a value from the app image into the scratch image over transport (Ch. 18). Values are immutable, so the copy behaves like the original. Pulling a ref copies its current value, not the binding. A value containing an `ext` resource cannot be pulled; that is a type error.
- `is Secret` values never leave their image.
- The scratch image is isolated from the app, not from the world: I/O done there is real.

### 20.2 Code views and hot reload

Code exists in three views: the editor buffers, the files on disk, and the code the app image runs. The scratch image, diagnostics and completion see the buffers laid over disk. The app changes only by a reload.

The compiler is an incremental query service shared by every tool. It holds the buffer view and the app's view in one cache. REPL input and development code run on a fast baseline tier, hot functions move to an optimizing tier, and release builds compile ahead of time (§20.7).

- `:reload` saves every changed buffer, then reloads the changed modules into the app. `:reload geo.shape` reloads only the named modules, together with the modules that depend on them.
- `:status` lists the modules whose buffers, disk files and app code differ.
- A reload is a transaction. The compiler checks every live root of the app (refs, `ext` bindings, running task frames, session bindings) against the new types, then swaps all code at once or rejects the reload with diagnostics. A rejected reload changes nothing: buffers stay as they are and the app keeps running.
- In development images, calls between modules go through an indirection table. A running frame finishes on its old code; a guaranteed tail call (§5.6.3) picks up the new code at its next call.
- Type identity is name and fields (§3.3), so unchanged types need no migration. A ref whose type changed needs a migration function `(Old) -> New` in the session, or a confirmed reset of that ref.
- A running frame of old code that will still use a ref being migrated blocks the reload, since its code expects the old type. The reload waits a bounded time, two seconds by default, for such frames to return or make a tail call, which lands in the new code with the ref already migrated. If time runs out, the reload is rejected, naming each blocking task and the line where it waits. Long-running loops that should survive type changes are therefore written as tail calls.
- A closure value keeps the code it was created with: a closure stored in a ref runs its old body until it is replaced. The reload preview lists closures of old code that are still alive.
- Module-level `let`s (§5.5) are recomputed.
- Saving a file does not reload the app. `:autoreload on` turns reload-on-save on: every save, including one from an external editor, reloads the saved module and its dependents, and saves that land close together are batched into one reload. A failed autoreload keeps the save; the app keeps its previous code. The setting is stored per user and per project in the user's settings directory (§20.8.3).

### 20.3 Debugger

The debugger acts on the image `:target` names.

- **Breakpoints.** `:break geo.shape:42` and `:break area` stop at a line or a function. A condition uses `where`, as in `case` guards: `:break area where s.r > 10`.
- **Signal and trap breakpoints.** `:break on Trap` stops where a trap happens, before it unwinds to its handler. Any trap or signal type works, and a parent type catches its whole family (§11.1).
- **Logpoints.** `:log area "r={s.r}"` writes to the `std.debug` output without stopping.
- **What stops.** By default a breakpoint pauses only the task that hit it; tasks waiting on it block, everything else runs on. `:debug-pause task` and `:debug-pause all` set the default, and `:break … all` overrides it for one breakpoint. When the whole image pauses, the runtime's clock for timeouts and timers pauses with it. Several tasks may be paused at once; `:task n` chooses the one the debugger acts on.
- **Inspection.** Locals are shown as they are; `let` bindings cannot change. `:eval expr` in a paused frame accepts only expressions without ref updates or I/O; `:eval! expr` allows effects. Inspecting a `Lazy` value does not force it (`:force` does). `is Secret` values show as `<secret T>`.
- **Watches.** `:watch expr` is re-evaluated at every pause. A watched ref updates live and shows a timeline of its commits, recorded by the debugger while the watch is open. The watch panel also shows rerun counts per `atomic` block, and for `ext` bindings the lock holder and its waiters. Tasks waiting on a paused task are marked as blocked by it, not as deadlocked.
- **Stepping.** `:step`, `:next`, `:out` and `:continue`. Development images keep a short log of tail calls, so the stack shows how many frames tail calls removed. A frame inside an `atomic` block shows its attempt number.
- **Restarting a frame.** `:restart-frame` re-enters the current function with its original arguments. It warns when the frame has already updated refs or done I/O, since those effects are not undone.
- A breakpoint in an optimized function moves that function back to the baseline tier.
- `:tasks` shows the live tree of structured scopes; `:pause <task>` pauses a task and its subtree.

### 20.4 Registries

A registry is a plain folder.

```
<registry>/
  registry.crag          # format version, registry name
  .staging/              # publishes in progress
  geo/
    1.1/
      package.crag       # the manifest as written
      src/               # modules
      res/               # embed sources
      api.crag           # generated public API surface
      sbom.crag          # generated SBOM
      content.hash       # hash over everything above
  acme/
    1.0/                 # package acme
    geo/
      2.0/               # package acme.geo
        yanked           # optional: the reason
```

- Each dot in a package name is a directory level (§14.5). Name segments start with a letter and version folders with a digit, so the two never collide.
- A version folder is named by the exact version (`1.1`, or `1.1.2` with a patch level). Packages are source only; compiled output lives in a local build cache keyed by content hash.
- A published version is immutable. Publishing writes into `.staging/` and then renames the folder into place, so no reader sees a partial package. A `yanked` file keeps existing builds working with a warning and refuses new imports of that version.
- A project may use several registries, but a package name must resolve in exactly one of them; otherwise the manifest names the source with `from` (§14.5.1).
- A folder registry has no accounts, so a name prefix such as `acme.` reserves nothing. The names `std` and `std.*` are reserved by the language.

### 20.5 Publishing

Publishing a package checks that:

- the manifest is valid and states a runtime version;
- every import, including transitive ones, resolves;
- every `test` declaration passes;
- the code contains no type holes (`???`, §6.11);
- no development import appears in the public API;
- every `embed` source lies inside the package.

The tool compares the new `api.crag` with the previous version in the same major line. A breaking change — a removal, a changed signature, a type losing fields or gaining a stricter `where` — requires a new major version. An addition requires at least a new minor version, because a new public name can collide in importers (§14.3). A public function gaining an effect (§3.14) is a breaking change too, and so is a parameter becoming escaping: api.crag records for every pub function which parameters it may store or return, since a caller may pass a bindings-only closure only where it does neither (§3.12, §6.4.1). An unchanged API allows a patch version.

### 20.6 Commands

Every command is implemented once and reached from two surfaces: the shell (`crag build`) and the REPL (`:build`).

| Command | Effect |
| --- | --- |
| `crag` | Opens the REPL in the current project |
| `new <name>` | Creates a project: manifest, `main` module, test module. `--lib` creates a library. |
| `add <package> [version]` | Adds an import to the manifest; without a version, the highest in the registries, written exactly |
| `remove <package>` | Removes an import; refused while code still uses the package |
| `upgrade <package> [version]`, `upgrade all` | Moves within the current major, or to the given version |
| `outdated` | Lists newer versions, newer majors separately |
| `deps` | Shows the resolved dependency graph |
| `sbom diff`, `sbom regenerate` | Shows or writes changes to the SBOM; `regenerate` prints the diff it writes |
| `build` | Builds; `--release` builds for release (§20.7) |
| `run` | Runs the application without the UI |
| `test [filter]` | Runs `test` declarations |
| `fmt <path>`, `fmt all` | Formats the named files or the whole project in place (§20.9) |
| `package` | Produces the distributable (§20.7) |
| `publish <registry>` | Packages and copies into the registry |

Commands that edit the manifest change only the lines they touch.

`crag lsp` starts the language server (§20.8) and `crag dap` the debug adapter (§20.8.7), each on standard input and output, for external editors. They are the only shell commands outside building, formatting, packaging and project management.

**Shell.** Arguments use `--` flags. Commands never prompt. A command that changes the project, a registry or an image does nothing when run bare and prints its usage instead, so exploring a command never changes the project. Exit codes are 0 for success, 1 for failures and 2 for usage errors; `--json` gives machine-readable output. Shell commands run standalone; with a session open in the same project they share only the compiler cache, under a file lock.

**REPL.** Arguments read like Crag: positional arguments first, a switch as a bare word, a value as `name: value` (`:build release`, `:publish team`, `:upgrade geo version: 2.0`). The mapping from the shell is mechanical: `--release` is `release`, `--registry=team` is `registry: team`. A bare word that is both a switch and a valid positional argument is an error naming both readings.

- There are no usage screens. `:help` lists the commands, `:help reload` explains one, and `:help area` shows a declaration's signature and documentation.
- A command that would lose work or state explains what will happen and asks `[y|N]`; Enter means no. It asks only when something would actually be lost. The switch `yes` skips the question, never the explanation; `yes` is always the switch, never a positional argument.
- `:autoreload on` is its own confirmation and never prompts.
- After `:add`, the scratch image can use the package at once; the app gets it at the next reload.

REPL-only commands: `:target`, `:pull`, `:restart scratch|app`, `:reload`, `:status`, `:autoreload`, `:rebind` (§17.3), `:edit`, the debugger commands (§20.3), `:debug-pause` and `:help`.

### 20.7 Release builds and packaging

A release build compiles the whole program ahead of time into one native executable.

- `std` is compiled together with the application; only what is used remains.
- Calls are direct; there are no reload tables and no debugger hooks. Line tables remain, so a trap that reaches the root prints a readable stack.
- The runtime is linked statically. The executable needs no Crag installation on the target.
- Compile-time `let`s are evaluated and `embed` resources inlined; the executable reads nothing from the project.
- The build is reproducible: the same sources, SBOM and runtime version give a bit-identical executable. No timestamps or build paths are embedded.
- The baseline tier is linked in only when the program can receive code through `std.transport` (§18.7).

**Static strings.** All static strings of a program, including literals, names and condition texts, are stored in one contiguous blob and referenced by offset and length. A static `Str` is a view into the blob, so using it needs no allocation or decoding.

- Each string is stored once, and a string that occurs inside another costs no bytes: its reference points into the longer one.
- The compiler builds a suffix automaton over all static strings, drops contained strings and overlaps the rest where one ends with the start of another. The merge order is greedy and deterministic, so builds stay reproducible.
- Strings read only on failure, such as condition texts, go into a second, compressed blob that is decompressed on first use.

`package` builds the distributable of an application:

```
dist/
  myapp-1.2-linux-x64/
    myapp            # executable
    sbom.crag        # packages, hashes, native libraries
    native.crag      # required C libraries and versions
  myapp-1.2-linux-x64.tar.gz
  myapp-1.2-linux-x64.tar.gz.sha256
```

Windows packages are `.zip` files. For a library, `package` writes the folder `publish` would place in a registry and runs every publishing check (§20.5).

`--target=<os>-<arch>` cross-compiles for the `Os` and `Arch` values of `std.env` (§19.7). Native library versions cannot be checked against another platform at build time; the check at program start remains.

**Native libraries** are never bundled and never linked statically: the shared libraries must be present on the host, which keeps their security updates with the host's package manager. `cLib("sqlite3")` stays platform-neutral; the runtime maps it to the platform's file name (`libsqlite3.so.*`, `libsqlite3.dylib`, `sqlite3.dll`). A missing library or a wrong version stops the program at start with a message naming the library, the version required, the file name and the places searched.

### 20.8 Editor and language server

The host runs a language server over the Language Server Protocol (LSP), on top of its compiler query service. The built-in editor is a client of that server like any external editor, so every editor feature is available to external editors as well, and nothing is built twice.

- The server holds the editor buffers, unsaved changes included; editors report changes through standard LSP messages. The scratch image compiles from the server's view (§20.2).
- Standard LSP covers completion (including the UFCS listing after `.`), hover, definitions, references, symbol search, diagnostics, inlay hints, code actions, semantic highlighting and formatting.
- Crag-specific requests are LSP extensions under the prefix `crag/`: evaluating in the scratch image, the reload status of modules, details of `???` holes, and `:pull`. External editors reach them through a small plugin.
- External editors start the server with `crag lsp` (§20.6).

The built-in editor is modeless. Basic navigation uses the arrow keys with modifiers; shortcuts use Ctrl and Alt, since Cmd never reaches a terminal program on macOS. Where the terminal supports an extended keyboard protocol, the editor uses it to receive every modifier combination, and falls back to a reduced set otherwise.

#### 20.8.1 Layout

```
┌ Buffers ───────┬ geo/shape.crag ─────────────────┬ Watches ──────┐
│● geo/shape     │ 12 │ pub fn area(s: Shape) ->   │ total   41.7  │
│◆ main          │ 13 │   case s {                 │ cache  3 hits │
│                │ 14 │     Circle(r:) -> pi * r * │               │
├ Files ─────────┤ 15 │     Rect(w:, h:) -> w * h  │               │
│▾ hello         ├────────────────────────────────┤               │
│  main.crag     │ scratch> area(Rect(w: 2, h: 3))│               │
│ ▸ geo          │ 6.0 : Float                    │               │
│▸ dependencies  │ scratch> █                     │               │
└ hello │ geo/shape.crag │ Editor │ Debug: 1 paused ──────────────┘
```

- **Centre column:** the editor on top and the REPL below; it always belongs to the code. There is no tab bar. Results from the scratch image appear dimmed at the end of a line.
- **Left panel, for navigation:** *Buffers* lists the open files, marked ● when unsaved and ◆ when they differ from the app; *Files* shows the project tree by module path, with dependencies read-only under their own node.
- **Right panel, for runtime:** watches, tasks, tests or problems, one view at a time. When a breakpoint hits, it switches to the task tree, the editor jumps to the paused line, and the REPL prompt shows the paused frame.
- **Small screens:** below a width threshold the side panels open as overlays above the code instead of taking columns; below a height threshold the editor and REPL share the centre one at a time.
- **Quick switch:** a modal picker in the centre, as in Helix, with one fuzzy search over open buffers and project files and a preview of the selection. Buffers rank first.
- **REPL:** the prompt names the target image (`scratch>` or `app>`). Enter evaluates complete input and otherwise starts a new line; Alt+Enter always inserts a line break. Results show their value and, dimmed, their type; long output is folded; a diagnostic's location leads into the editor.
- **Status bar:** the project, the current buffer, the focused element (Editor, REPL, Buffers, Files or the right panel's view) and the mode (Edit, Run, or Debug with the number of paused tasks).
- **Colours:** truecolor, 256 and 16 colours are detected and degrade in that order; without colour the interface uses bold and reverse video, and `NO_COLOR` is respected. Every state also has a symbol or a word, so nothing depends on colour alone.

#### 20.8.2 Keys

The default key map follows common editor conventions where a terminal allows them. Every key works without the extended keyboard protocol unless noted; any key can be remapped (§20.8.3), and `:keys` shows the current map.

| Area | Keys |
| --- | --- |
| Global | Ctrl+P quick switch · Ctrl+K command palette · F6 cycle focus · Alt+1 to Alt+4 left panel, editor, REPL, right panel · Ctrl+B left panel · Alt+B right panel · Esc close or cancel · Ctrl+Q quit |
| Editing | arrows, with Ctrl (Alt on macOS) by word · Home, End · Shift selects · Ctrl+S save · Ctrl+Z undo · Ctrl+Y redo · Ctrl+X, Ctrl+C, Ctrl+V clipboard · Ctrl+A select all · Ctrl+F find, Tab to replace · Ctrl+/ comment · Tab, Shift+Tab indent |
| Code | Ctrl+Space completion · F1 information on the symbol · F12 definition · Shift+F12 references · Alt+, and Alt+. back and forward · F8 next problem |
| REPL and running | Ctrl+E evaluate the selection or the expression at the cursor in the scratch image · Alt+R reload, with confirmation · in the REPL: Ctrl+R history search, Ctrl+L clear, Ctrl+C interrupt |
| Debugging | F9 breakpoint · F5 continue · Shift+F5 pause · F10 step over · F11 step into · Shift+F11 step out |

Ctrl+C copies when text is selected and otherwise interrupts. Where a terminal takes a key for itself, such as F11 for full screen, the matching command (`:step`) always works.

#### 20.8.3 Settings and caches

Settings and caches live in the user's home directory, in the place the host system's layout rules give: `~/.crag` on Linux, the application-support and cache folders on macOS, and the application-data folders on Windows. They hold the key map, user settings, per-project settings such as `:autoreload` and `:debug-pause`, and the compiler's build cache. A project directory contains only what belongs in version control.

The environment variable `CRAG_HOME` overrides this location for settings and caches alike, for CI machines, containers and isolated test setups.

#### 20.8.4 Renaming

Names are resolved statically, so most renames are exact: locals and parameters by scope; a function overload at exactly the call sites resolved to it, UFCS calls included; a type wherever its name resolves; a module by moving its file (§14.1) and updating every import. A rename that would collide, such as an overload with the same parameter types, is refused.

A field can reach other types structurally, so a field is renamed together with every field linked to it. Wherever a value of one type fits another (an argument, a return, a binding, a spread), the fields of the same name in both are linked; following the links from the chosen field gives a group that must keep one name.

- The rename changes the whole group: declarations, constructions, accesses, labels in field updates and patterns. A shorthand pattern keeps its local name: `Point(x:)` becomes `Point(left: x)`.
- It is all or nothing. If the group reaches a type that cannot be edited, from a dependency or `std`, the rename is refused and the link that pulls it in is shown.
- A preview lists every affected type and occurrence, grouped by type, and asks `[y|N]`.
- The preview warns when a type in the group derives `Encode` or `Decode`, since its data format changes, and when a public type of a library changes, which requires a major version (§20.5).

A generic function over `(name: Str, ..)` links the `name` fields of every type passed to it, so groups can be large. To rename one of them alone, make it `distinct` first.

#### 20.8.5 Structural refactoring

Refactorings are LSP code actions, so external editors have them too, and each shows a preview before it changes anything. Types and inferred effects decide what is equivalent.

**Extract to function** turns a selected expression or run of statements into a function.

- Every outside binding the selection uses becomes a parameter, with its inferred type written out; type parameters and bounds of the enclosing function come along where needed.
- A `var` assigned in the selection is returned and reassigned at the call site: `x = step(x)`, or a record such as `(x:, y:)` for several.
- A selection containing `return` is refused, since its meaning would change.
- The function goes at module level after the current one, or optionally becomes a local function (§5.6.4).

**Extract to `let`** names an expression in place.

**Inline** replaces a call with the function's body. An argument is substituted directly only if it is pure and used once; otherwise it is bound to a `let` first, so effects and costs happen once and in their original order. Recursive functions, functions containing `return`, and bodies using names the call site cannot see cannot be inlined. All call sites can be inlined at once, and the function deleted.

**Move to module** moves a function and updates every call site's imports, UFCS calls included. Private helpers used only by the moved function move with it; helpers that stay and are still needed must become `pub`, which the preview offers. The move is checked against the collision rules (§14.3) in the target module and at every call site that imports both modules. Moving a `pub` function of a library is a breaking change (§20.5), and the preview says so.

**Simplify** offers rewrites where they apply, never automatically, and only when types and effects prove them equivalent:

- `if c { True } else { False }` to `c`; `not (a == b)` to `a != b`;
- `{ x -> f(x) }` to `f`; `{ x -> x * 2 }` to `_ * 2`;
- `Point(x: p.x, y: 3)` to `Point(..p, y: 3)`;
- a `case` on an option with a fallback arm to `orElse`, using the `Lazy` overload when the fallback has effects or real cost;
- a `case` whose `Empty` arm only returns `Empty` to `let … else`;
- removing an `is T` test that always holds by type, and flagging an unused `let`.

#### 20.8.6 Language server features

Standard LSP requests and what they provide for Crag:

| Request | Provides |
| --- | --- |
| Document synchronisation | Incremental buffer changes, opening, saving and closing; changes on disk from external tools are watched |
| Completion | The UFCS listing after `.` (§17.2); an import added when the chosen function is not imported; named arguments |
| Hover | Inferred type, absorbed union members, effects (§3.14), markers and documentation |
| Signature help | Overloads, named and defaulted parameters |
| Definition, type definition, references, highlights | Exact targets, resolved statically |
| Implementation | The types that satisfy a form (Ch. 4) |
| Type hierarchy | Families of `Error`, `Signal` and `Trap` types and other spread parents |
| Call hierarchy | Incoming and outgoing calls |
| Document and workspace symbols | Declarations of the project and its dependencies |
| Diagnostics | Errors and warnings from the buffer view; every `???` hole as an information diagnostic with its expected type |
| Inlay hints | Results evaluated in the scratch image; optionally inferred types of bindings |
| Code actions | Quick fixes such as adding an import or missing `case` arms; the refactorings of §20.8.5 |
| Rename | §20.8.4, with the preview as a confirmed change |
| Formatting | Whole document or range, as `fmt` |
| Semantic tokens | Types, functions, fields, bindings, refs, `ext` bindings and prefixes, each distinct |
| Folding and selection ranges | By syntax; expanding the selection works with evaluation (Ctrl+E) |
| Code lens | Run or debug above each `test` declaration |

Crag-specific requests use the prefix `crag/`:

| Request | Provides |
| --- | --- |
| `crag/evaluate` | Evaluates text or a range in the scratch or app image; returns value, type and effects |
| `crag/moduleStatus` | Per module, whether buffer, disk and app differ |
| `crag/reload` | Runs the reload transaction (§20.2), with its preview and diagnostics |
| `crag/hole` | For a `???` hole: expected type, bindings in scope with their types, and functions that would fit |
| `crag/pull` | Copies a value from the app image into the scratch image (§20.1) |
| `crag/test` | Runs tests by filter and streams their results |

#### 20.8.7 Debug adapter

The debugger (§20.3) is served over the Debug Adapter Protocol (DAP). The host runs the adapter, and the built-in editor is a client of it like any external editor, so breakpoints, stepping, watches and variables work in external editors without a plugin.

| DAP | Crag |
| --- | --- |
| Launch, attach | Run the app image, or attach to the app image of a running session |
| Breakpoints | Line and function breakpoints; conditions are `where` expressions; log messages are logpoints (`:log`) |
| Exception breakpoints | Signal and trap breakpoints (`:break on T`), one filter per family |
| Threads | Tasks; pausing one task or all follows `:debug-pause` |
| Stack trace | Frames, with the number of frames removed by tail calls |
| Scopes and variables | Locals; `Lazy` values unforced; `is Secret` values hidden. Values cannot be set: bindings are immutable |
| Evaluate | Pure expressions in the paused frame; effects only on explicit request (`:eval!`) |
| Step in, over, out; continue | As `:step`, `:next`, `:out`, `:continue` |
| Restart frame | `:restart-frame`, with its warning about effects |

Crag-specific views are custom requests under `crag/`: the structured task tree (DAP threads are flat), the commit timeline of a watched ref, rerun counts and attempt numbers of `atomic` blocks, `ext` lock holders and waiters, and forcing a `Lazy` value.

External editors start the adapter with `crag dap` (§20.6).

### 20.9 Formatting

The formatter (`fmt`, and LSP formatting) has one canonical format and no options, so every Crag file looks the same and diffs show only real changes. It is idempotent, never changes meaning (the result must give the same syntax tree), and never reorders declarations; imports are the only thing it reorders.

**Layout.** Indentation is two spaces, never tabs; a continuation line is one level deeper. The line length threshold is 100 columns: a construct is broken only when it does not fit. `{` stays on the line that opens it, and `} else {` on one line. Exactly one blank line separates top-level declarations; inside a block at most one is kept, and none directly after `{` or before `}`.

**Breaking.** When a construct exceeds the threshold:

- an argument list, record, list or map puts one item per line, each followed by a comma, with the closing bracket on its own line; on a single line there is no trailing comma;
- a method chain puts each `.call` on its own line, starting with the `.` (§2.3);
- a binary expression is wrapped in parentheses, unless it already is or stands in an argument list, and broken before each operator; inside parentheses newlines are whitespace (§2.3);
- the clauses of a type declaration (`is`, `where`, `on`) go on their own indented lines;
- a `case` arm breaks after `->`, and its body starts on the next line, one level deeper.

```
let total = (subtotal
  + shipping
  - discount)

case r {
  Order -> "order {r.id}"
  Rejected(code: 404, reason: "resource permanently removed by its owner") ->
    "gone for good: {r.reason}"
}
```

**Spacing.** Spaces surround binary operators, `=` and `->`; none go inside parentheses and brackets; one follows `,` and a label's `:`. A prefix is followed by one space, since it applies to the whole expression after it: `!! cfg.decode[Limits]()`. Unary `-` and a spread stay attached: `-x`, `..p`. One-line closures have spaces inside the braces: `{ x -> x * 2 }`. Nothing is aligned vertically.

**Imports** are grouped `std`, then packages, then the project's own modules, with a blank line between groups, and sorted within each group and within `import x.{…}`.

**Untouched:** string contents, how numbers are written, and comments, which keep their place; a trailing comment gets two spaces before its `//`.

## Appendix A Glossary

| Term | Definition | See |
| --- | --- | --- |
| Anonymous record | A record type identified by its field names and types only, e.g. `(x: Int, y: Int)` | §3.4 |
| Atomic block | A transaction updating several refs together; no I/O allowed | §9.5 |
| Bracket application | The single `e[...]` syntax for indexing and generic type arguments | §6.5 |
| Combinator | A function that runs closures as concurrent branches: `all`, `allDone`, `first`, `firstDone` | §10.2 |
| Distinct type | A nominal type that never merges with a same-shaped declaration | §3.9 |
| `ext` | A binding to mutable external state, updated under a lock (pessimistic) | §9.6 |
| Form | A structural requirement set over one or more types, satisfied automatically | Ch. 4 |
| Marker | A named constraint with no definition, attached with `is` (e.g. `Solid`, `Secret`) | §3.11 |
| Narrowing | Refining a binding’s type after `if x is T` or in a `case` arm | §7.1 |
| Opaque type | A type whose structure and constructor are hidden outside its module | §3.9 |
| Package | A versioned visibility boundary declaring its exports and imports | §14.5 |
| Parent type | The single type a named type spreads into its field list; makes it a subtype | §3.8 |
| `pass` | The `case` arm that propagates all unhandled alternatives to the caller | §8.2 |
| Prefix | A token applying a type mapping function to the following expression | §8.5 |
| `ref` | A binding to shared state, updated atomically and optimistically | Ch. 9 |
| Rebind | REPL-only redefinition that also rebinds dependents | §17.3 |
| Signal | A `Solid` value emitted to defer effects out of restricted scopes | Ch. 11 |
| Sink / Source | Producer and consumer ends of a stream | §10.5 |
| Solid | Property of types whose values can never cause a runtime error | §3.11 |
| Spread | `..x` in a field list (parent) or constructor (update) | §3.8, §6.7 |
| Structured concurrency | Every task is started and awaited by a scope; no detached tasks | §10.1 |
| Tag type | A field-less type with a single value, e.g. `type Done` | §3.2 |
| Trap | A runtime or machine condition (e.g. overflow) that ends the code raising it and travels to the nearest trap handler | §8.3 |
| Type mapping function | A function that transforms its argument’s type, e.g. `discard` | §8.4 |
| UFCS | Uniform function call syntax: `x.f(a)` means `f(x, a)` | §6.3 |
| Value condition | A `where` clause on a type that every value must satisfy | §3.10.1 |

## Appendix B Reserved words and standard markers

### B.1 Keywords

| Group | Keywords |
| --- | --- |
| Bindings | `let` `var` `ref` `ext` `embed` (`from` is contextual after `embed`) |
| Declarations | `type` `form` `fn` `test` |
| Modifiers | `pub` `opaque` `distinct` |
| Clauses | `is` `where` `on` |
| Control | `if` `else` `case` `pass` `for` `in` `return` |
| Effects | `emit` `atomic` `lazy` |
| Modules | `import` `as` |
| Operators | `and` `or` `not` |

Contextual keywords are reserved only in their position: `ok`, `fail` and `retry` after `emit`; `prefix` at the end of a function signature; `this` in a value condition; `from` after `embed` and in manifest imports; and `package`, `runtime`, `name`, `summary`, `description`, `export`, `dev` and `main` in `package.crag`.

### B.2 Rejected or retired keywords

| Word | Status |
| --- | --- |
| `keep` | Dropped; closure escape is inferred |
| `scope` | Rejected as superfluous |
| `const` | Not needed; `let` covers constants |
| `with` | Retired as a clause keyword; replaced by `is` and `where` |
| `solid` | Replaced by the marker `Solid` |
| `drop`, `free` | Rejected; cleanup uses `on Dispose` |
| `foreign` | Rejected; C symbols use `import` |
| `interface`, `impl` | Replaced by `form`; satisfaction is structural |
| `fallthrough` | Rejected in favour of `pass` |
| `if let`, `??`, `?` propagation | Rejected |

### B.3 Standard markers and compiler-known types

| Name | Kind |
| --- | --- |
| `Solid`, `Pure`, `Secret`, `Immediate`, `Deferred` | Markers |
| `ThreadUnsafe`, `ThreadSafe`, `ThreadBound`, `Errno` | FFI markers |
| `Ref[T]` | Compiler-owned ref type |
| `Fields[R, T]` | Compiler-known form |
| `Signal`, `TrapSignal` | Standard signal types |
| `Error`, `Trap` and its family | Standard error and trap parents (§8.1, §8.3) |
| `LifecycleHandler`, `Dispose[T]`, `Encode[T]`, `Decode[T]`, `Embed[T]` | Standard lifecycle handler kinds (§11.4) |
| `Option[T]`, `Empty`, `Bool`, `True`, `False` | Standard unions and tags |
| `Int, Int8, Int16, Int32, UInt8, UInt16, UInt32, UInt64, Float, Fixed[S], Str, CodePoint, Bytes, Lazy[T], Expr[F], Type` | Compiler-owned types (§19.1) |

## Appendix C Open questions and provisional syntax

Tick an item once it is decided, and update the chapter it points to.

### C.1 Open design questions

- [x] How sequential statements are distinguished from concurrent tasks, and which statements yield a scope’s value (Ch. 10)
- [x] Whether tasks need to be defined in terms of fibers (Ch. 10)
- [x] Exact result types of `all`, `allDone`, `first`, `firstDone` (§10.2)
- [x] Creating sink/source pairs; how `Finite` and `Infinite` relate to `Source` (§10.5)
- [x] Ref access functions and their sugar: `update`, `use`, `swap`, `empty` (§9.3)
- [x] Signal subscription and routing; success and retry qualifier names for `emit` (§11.2, §11.3)
- [x] Semantics of `check` and `expect`; prefix characters for `discard`, `check`, `expect` (§8.4–8.5)
- [x] Formal definition of type mapping functions and how they declare prefixes (§8.5)
- [x] Opt-in syntax for accepting extra record fields (§3.8.1)
- [x] Whether closures that carry refs need a field marker: no, they are bindings-only (§3.12)
- [x] Package manifest syntax (§14.5)
- [x] Partial evaluation to recover dynamic-dispatch convenience (§4.6)
- [x] Translation vocabularies for providers that compile `Expr` to another language (SQL) (§18.11)
- [ ] Whether quote and splice (`Code[T]`) is needed at all, and if so for expressions only (§18.5)
- [ ] Sources for `embed` beyond package files: URLs and other schemes, with a pinned content hash fetched by the build tool and recorded in the SBOM; unknown schemes are a compile error until defined (§18.4.1)
- [x] Spelling of a lifecycle kind that accepts either of several handler forms: a union of function types (§11.4)
- [x] Overlapping union members (a parent and its subtype, or a generic member instantiated to another member's type): reject at declaration or instantiation, or allow for values and reject only where the chosen member changes behavior (§3.6)
- [x] Confirm the overload specificity rule: strict inclusion of requirements wins (§5.6.1)
- [x] Whether basic functions on prelude types (length, get, map, filter, substring) join the prelude or need an import of std.text and std.coll (§19.3)
- [x] Standard modules for time and clocks, randomness, environment and program arguments, and paths (§19.4)
- [x] The program entry point and how it returns an ExitCode (§19.7)
- [x] Standard input, output and error as std.io values (§15.6)
- [ ] Fluent chaining for results other than `Option[T]`, which `.then` alone covers (§6.8, §16.5)

### C.2 Placeholder syntax used in this draft

Two provisional names remain: the arena type name `Graph` (§13.2), and the transport names `Expr`, `Policy`, `run` and `decode` (§18.10).

## Appendix D Grammar

This grammar uses the notation of §1.3. It describes syntax only; types, name resolution and the rules of the chapters decide what a parse means. Where the chapters leave a point open, the production carries a comment and the point is listed in D.8.

### D.1 Tokens

```
name       = (letter | "_") (letter | digit | "_")*
intLit     = digit ("_"? digit)*
           | "0x" hexDigit ("_"? hexDigit)*
           | "0b" ("0" | "1") ("_"? ("0" | "1"))*
           | "0o" octDigit ("_"? octDigit)*
floatLit   = digits "." digits exponent? | digits exponent
digits     = digit ("_"? digit)*
exponent   = ("e" | "E") ("+" | "-")? digits
strLit     = '"' (strChar | escape | "{{" | "}}" | "{" expr "}")* '"'
           | '"""' NL (any text, interpolation and escapes as above) NL ws* '"""'
bytesLit   = "b" '"' (strChar | escape | "\x" hexDigit hexDigit)* '"'   // no interpolation
codeLit    = "'" (strChar | escape) "'"
escape     = "\n" | "\t" | "\r" | "\0" | "\\" | '\"' | "\'" | "\u{" hexDigit+ "}"
hole       = "???"
```

A newline ends a statement except where §2.3 says otherwise. The lexer turns each ending newline into the token `NL`; all other newlines are whitespace. Comments (§2.2) are whitespace. A prefix (§2.8) is a token declared by a type mapping function in scope; the longest matching prefix wins.

### D.2 Modules and declarations

```
module     = NL* (topDecl (NL+ topDecl)*)? NL*
topDecl    = import | typeDecl | formDecl | fnDecl | letDecl | embedDecl | testDecl

import     = "import" path ("as" name)?
           | "import" path "." "{" item ("," item)* ","? "}"
           | "import" "cLib" "(" strLit ")" "." "{" cSig ("," cSig)* ","? "}" isClause?   // §16.4
path       = name ("." name)*
item       = name ("as" name)?
cSig       = name "(" params? ")" "->" type isClause?

typeDecl   = "pub"? ("opaque" | "distinct")? "type" name typeParams? typeBody clauses
typeBody   = ε                                        // tag type, §3.2
           | "(" fields? ")"                          // record type, §3.3
           | "=" type                                 // alias, §3.5; or "=" expr, a computed type, §18.3
fields     = spread ("," field)* ","? | field ("," field)* ","?
spread     = ".." type
field      = name ":" type ("=" expr)?
clauses    = (NL? whereClause)? (NL? isClause)? (NL? whereClause)? (NL? onClause)*
whereClause = "where" (expr ("," expr)* | "{" itemList "}")   // requirements or value conditions, §3.10
isClause   = "is" (marker | "{" marker (("," | NL) marker)* "}")
marker     = "not"? type
onClause   = "on" type expr
itemList   = NL* expr ((("," | NL) NL*) expr)* NL*   // named conditions: D.8 (12)

formDecl   = "pub"? "form" name typeParams (whereClause? "{" NL* (formFn NL+)* "}"
                                           | "=" type ("|" type)*)
formFn     = name typeParams? "(" params? ")" "->" type

fnDecl     = "pub"? "fn" name typeParams? "(" params? ")" ("->" type)? (NL? whereClause)?
             prefixClause? block?                     // no body: intrinsics in std only, §19.2
prefixClause = "prefix" strLit
params     = param ("," param)* ","?
param      = name ":" type ("=" expr)?                // a defaulted parameter is passed by name
typeParams = "[" typeParam ("," typeParam)* "]"
typeParam  = name (":" type)?

letDecl    = "let" pattern (":" type)? "=" expr ("else" (block | closure))?   // §7.1.1
varDecl    = "var" name (":" type)? "=" expr
refDecl    = ("ref" | "ext") name (":" type)? "=" expr
embedDecl  = "embed" name (":" type)? "from" strLit
testDecl   = "test" strLit block                      // D.8 (7)
```

A type and a declaration may be preceded by a comment that documents it (§2.2). Two `where` clauses in a type declaration are told apart by their content: requirements name forms, value conditions are `Bool` expressions.

### D.3 Statements and blocks

```
block      = "{" NL* (stmt (NL+ stmt)*)? NL* "}"
stmt       = letDecl | varDecl | refDecl | assign | forStmt | emitStmt | returnStmt | onStmt | fnDecl | expr                                   // local fn: §5.6.4
assign     = name "=" expr                            // var only, §5.2
forStmt    = "for" pattern "in" expr block
emitStmt   = "emit" ("ok" | "fail" | "retry")? expr
returnStmt = "return" expr?
onStmt     = "on" type closure                       // signal or trap handler, §8.3.1, §11.3
```

### D.4 Expressions

The levels follow §6.2.1.

```
expr       = orExpr | lazyExpr
lazyExpr   = "lazy" (block | expr)                    // binds loosest, §6.10
orExpr     = andExpr ("or" andExpr)*
andExpr    = notExpr ("and" notExpr)*
notExpr    = "not" notExpr | cmpExpr
cmpExpr    = rangeExpr (("==" | "!=" | "<" | "<=" | ">" | ">=") rangeExpr | "is" type)?
rangeExpr  = addExpr (".." addExpr?)?                // Range or RangeFrom, not an operator, §7.4
addExpr    = mulExpr (("+" | "-" | "+%" | "-%") mulExpr)*
mulExpr    = unary (("*" | "/" | "%" | "*%") unary)*
unary      = (prefix | "-") unary | postfix
postfix    = primary suffix*
suffix     = "(" args? ")" closure?                   // call, with optional trailing closure
           | closure                                  // trailing closure, empty parentheses dropped
           | "[" args "]"                             // bracket application, §6.5
           | "." name | "?." name
args       = arg ("," arg)* ","?
arg        = expr | label ":" expr | ".." expr
label      = name ("." name)*                         // dotted paths in field-update lists, §6.7

primary    = intLit | floatLit | strLit | bytesLit | codeLit | hole | name | "_"
           | "(" expr ")" | record | list | map | grid
           | closure | block | ifExpr | caseExpr | atomicExpr
record     = "(" ")" | "(" arg ("," arg)* ","? ")"    // at least one label or spread
list       = "[" (expr ("," expr)* ","?)? "]"
map        = "[" ":" "]" | "[" expr ":" expr ("," expr ":" expr)* ","? "]"
grid       = "[" expr ("," expr)* (";" expr ("," expr)*)+ "]"
closure    = "{" cParams? "->" NL* (stmt (NL+ stmt)*)? NL* "}"
cParams    = cParam ("," cParam)*
cParam     = pattern (":" type)?
ifExpr     = "if" expr block (NL? "else" (ifExpr | block))?
caseExpr   = "case" expr "{" NL* (arm NL+)* arm? NL* "}"
arm        = pattern ("where" expr)? "->" (expr | block) | "pass"
atomicExpr = "atomic" block
```

- A `{` that begins `{ ->` or `{ params ->` starts a closure; any other `{` starts a block. So a trailing closure is recognized without lookahead into the call, and `if xs.any { x -> x > 0 } { … }` parses as intended.
- The arguments of a bracket application may be types or expressions (`List[Int]`, `xs[0]`, `Fields[R, () -> _]`); the parser accepts both and name resolution decides (§6.5).
- `_` as an argument makes a partial application (§6.6). `Point(x: 1)`, `Float(n)` and `f(x)` are all calls; a type name decides construction or conversion (§5.6).

### D.5 Patterns

```
pattern    = altPat ("|" altPat)*
altPat     = name ":" altPat                          // bind and match, n: Int
           | "_" | name | literal (".." literal)?          // range pattern, §7.4
           | name typeArgs                             // Empty[Int], List[Str]
           | name typeArgs? "(" patFields? ")"         // Circle(r:), Point(a, b)
           | "(" patFields ")"                         // anonymous record, by name
           | "[" (listPat ("," listPat)* ","?)? "]"
patFields  = patField ("," patField)* ","?
patField   = name ":" pattern? | pattern
listPat    = pattern | ".." name?
literal    = intLit | floatLit | strLit | codeLit | bytesLit
```

Whether a bare `name` is a type or a binding is decided by position (§6.9).

### D.6 Types

```
type       = fnType | unionType
fnType     = "(" (type ("," type)*)? ")" "->" type    // everything after -> is the result, §3.7
unionType  = atomType ("|" atomType)*
atomType   = name typeArgs? | "_" | "(" ")" | "(" type ")" | recordType
typeArgs   = "[" typeArg ("," typeArg)* ("," isClause)? "]"   // trailing is: §11.4
typeArg    = type | intLit                            // Fixed[2]
recordType = "(" recEntry ("," recEntry)* ("," "..")? ","? ")"
recEntry   = ".." type | name ":" type
```

### D.7 Manifest

```
manifest   = NL* (mDecl NL+)* mDecl? NL*
mDecl      = "package" path version | "runtime" version
           | ("name" | "summary" | "description") strLit
           | "export" path ("." "{" name ("," name)* "}")?
           | "import" "dev"? path version ("from" strLit)?
           | "main" path
version    = digit+ "." digit+ ("." digit+)?   // one token; a manifest has no float literals
```

### D.8 Open points

Writing the grammar showed where the chapters are silent or disagree:

1. **Zero-parameter closures.** Resolved: a closure without parameters is written `{ -> … }` (§6.10 corrected).
2. **Bare names in patterns.** Resolved: §6.9 and §7.2.
3. **Type-qualified calls.** Resolved: §6.3.
4. **Qualified names in `std`.** Resolved: intrinsic handle types (§19.2).
5. **Type-level code.** `type Partial[R] = map R { … }` and `type UserRow = sqlRow(schema)` (§18.3) Resolved: §18.3.
6. **Literal details.** Resolved: §2.6.
7. **Tests.** Resolved: §5.7, and `test` is a keyword in B.1.
8. **FFI markers.** Resolved: §16.3 and §16.4.
9. **`lazy` precedence.** Resolved: §6.10.
10. **Function declarations.** Resolved: §8.5 places `prefix` last in the signature; §19.2 restricts body-less `fn` to intrinsics; §1.3 explains body-less signatures in this document.
11. **`expect` in §18.4.1.** Resolved: the example uses `!!`.
12. **Clause groups.** Resolved: §3.10.
13. **Contextual keywords.** Resolved: listed after B.1.
14. **Local functions.** Resolved: §5.6.4.
15. **`is` in type arguments.** Resolved: a form's type arguments may end with an `is` clause (§11.4).
