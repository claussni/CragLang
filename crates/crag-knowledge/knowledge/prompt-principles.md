Principles for writing Crag, from the design goals (the resource
crag://principles gives them with their rationale):

- Immutable first (§3): updates make new values; use the persistent
  collection functions (`set`, `append`) and never look for in-place
  mutation.
- Mutation is visible (§5.1): state lives only behind `var`, `ref`,
  `ext` or `dur`; prefer plain `let` and returning new values.
- Three channels, one job each (§8): an expected failure is an error
  value in an inferred union, handled with `case` and `pass`; a signal
  carries information up the scopes with `emit`; a trap ends a block
  for runtime conditions, and `!!` is for tests and true invariants.
- Structural typing (§3): types match by shape; use `distinct` only
  where identity must matter (§3.9).
- Effects are inferred (§3.14): keep `io` at the edges, so most
  functions stay callable from `is Pure` contexts and conditions.
- Names are written by humans: propose new public names and leave the
  choice to the user.

Read crag://primer before writing the first module, and check code with
the `check` tool instead of guessing.
