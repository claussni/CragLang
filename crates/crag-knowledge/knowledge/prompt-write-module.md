Write the module {module}, then make it clean:

1. Read crag://primer if you have not, and look up functions with
   `searchStd` and `members` instead of inventing them.
2. Write the module file, with a doc comment above each `pub`
   declaration (§2.2).
3. Run `check` on the whole project. For every diagnostic, read its
   explanation first: the `explain` tool or crag://diagnostic/<code>.
4. Write its tests under `test/` with the assertions of std.test, and
   run the `test` tool until they pass.
5. Finish with the `fmt` tool, so the file keeps the canonical layout.

Try uncertain snippets with `eval` in the scratch image; it leaves the
project untouched.
