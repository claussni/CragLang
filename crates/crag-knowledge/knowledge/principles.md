# Design principles

The design goals of the specification (§1.1), each with its rationale.
They decide API questions before taste does: when two designs work, the
one that follows the principles is the one Crag takes.

## 1. Immutable first (§3, §12)

Values never change; an update produces a new version backed by
persistent data structures. Code that holds a value holds it forever,
so sharing needs no copies and no defensive cloning, and equality means
what it says.

## 2. Mutation is visible (§5.1, §9, §21)

Every mutable thing is a distinct binding kind — `var`, `ref`, `ext`,
`dur` — that the reader and the type system see. Nothing mutates behind
a plain name, so the places state can change are exactly the places one
of those words appears.

## 3. Structural and static (§3, §4.6)

Types are identified by structure, with `distinct` and `opaque` as the
explicit exceptions (§3.9), and dispatch is resolved at compile time
from inferred concrete types. What a value can do follows from its
shape, and the cost of a call is decided before the program runs.

## 4. Correct values (§3.10, §8)

Type conditions, the compiler and the runtime enforce valid values, in
that order: a condition the compiler can decide is a compile error when
it fails, and one it cannot is checked when the value is built. Errors
are ordinary values in inferred unions (§8.1), signals carry
information up the scope tree (Ch. 11), and traps end a block for
runtime conditions (§8.3); each channel has one job.

## 5. Maximal, structured concurrency (§10)

Every task lives inside a scope that awaits it; there are no detached
tasks. Nothing outlives its scope, so cancellation, errors and cleanup
follow the block structure of the code.

## 6. REPL-friendly (§17)

The same rules hold in the REPL as in files; the REPL adds discovery,
not exceptions. What is learned at the prompt is true in a module, so
exploration carries over.

## 7. Not a scientific language (§12)

Collections are practical — lists, maps, 2D grids — not n-dimensional
arrays. The library optimizes for programs that move records around,
not for numeric kernels.
