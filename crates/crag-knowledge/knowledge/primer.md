# Crag primer

Where Crag differs from the languages coding agents know best. Each entry
links the section of the specification that states the rule, readable as
`crag://spec/<section>`.

## `pass`, not `?` (§8.2)

A fallible function returns a union of its success and error types, and
the compiler infers that union; there are no exceptions and no `?`
propagation operator. A result is handled exhaustively with `case`, and
`pass` inside it hands every alternative not handled so far to the
caller.

```crag
fn greet(id: Str) -> Str | NotFound {
  case lookup(id) {
    u: User -> "Hello {u.name}"
    pass  // NotFound flows to the caller
  }
}
```

## The prefixes `~`, `?` and `!!` (§8.4)

`~ e` (discard) drops a value but keeps its errors to handle; `? e`
(check) keeps the success and turns errors into `Empty`, when only
success matters; `!! e` (expect) turns errors into a trap, for tests,
scripts and true invariants. `!!` is not negation, and a single `!`
means nothing: *not* is spelled `not` (§2.5).

## Named records, no tuples (§3.3, §3.4)

There are no positional tuples; every field has a name.
`type Point(x: Int, y: Int)` declares a named record, `(x: 1, y: 2)`
builds an anonymous one, and arguments are matched to parameters by
name, not by position (§5.6.2).

## Map literals (§12.2)

`["ada": 36]` is a map and `[:]` an empty one. Indexing gives an
`Option`: `ages["ada"]` is `Option[Int]`. Values never change;
`ages.set("ada", 37)` is a new map.

## No integer string indexing (§12.5)

`Str` is UTF-8 text with no `s[0]` and no list functions. Positions
come from index functions and go to substring functions:
`s.indexOf(",").then { at -> s.substring(before: at) }`.

## `case` and `where` guards (§7.2)

`case` must be exhaustive, and the first matching arm in source order
wins. A guard is written `where`, as in `k: Int where k > 0 -> "plus"`,
and never makes an arm cover a later one.

## `and`, `or`, `not` (§2.5)

The boolean operators are the words `and`, `or` and `not`. `&&`, `||`
and `!` do not exist.

## Refs are bindings only (§9.2)

`ref hits = 0` declares mutable state as a binding. A ref is never
stored in a data structure, returned or captured by an escaping
closure, and its name alone never denotes its value: every access is an
atomic call such as `hits.update { n -> n + 1 }` or `hits.use()`
(§9.3).

## UFCS (§6.3)

`x.f(args)` means `f(x, args)`: there are no methods, and every visible
function whose first parameter accepts `x` is callable with a dot.
`T.f(args)` picks the overloads of `f` whose success type is `T`, as in
`Int.parse("42")`.

## `.then`, `orElse` and `let … else` (§6.8, §7.1.1)

There is no `if let` and no `??`. `a?.b` gives `Empty` when `a` is
`Empty`; `.then { v -> … }` applies a closure to a result's successes
and passes its errors and `Empty` through; `orElse` gives an option a
fallback; and `let v: Int = e else { return d }` binds or leaves.
