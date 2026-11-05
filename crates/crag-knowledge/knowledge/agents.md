# Working here with an agent

This is a Crag project. The toolchain speaks the Model Context Protocol:
`crag mcp` serves the compiler, the test runner and a scratch image, so
everything an agent learns comes from the toolchain as installed and
nothing drifts from the language.

- Read the resource `crag://primer` first. Crag differs from the
  languages you know best, and the primer lists exactly where, each
  entry with its section of the specification (`crag://spec/<section>`).
- Check code with the `check` tool instead of guessing. Every
  diagnostic carries a code; `explain` (or the resource
  `crag://diagnostic/<code>`) gives the rule, why it exists, a program
  it refuses and the same program fixed.
- `typeOf` gives an expression's type and effects, `members` and
  `searchStd` find functions, and `eval` tries snippets in the scratch
  image without touching the project.
- Run `test` after each change, and `fmt` before finishing.
