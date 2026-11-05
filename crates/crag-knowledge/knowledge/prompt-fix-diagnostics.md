Fix the diagnostics of {target}:

1. Run `check`. Each diagnostic names its code, such as E0301.
2. Read the code's explanation before changing code: the `explain`
   tool, or the resource crag://diagnostic/<code>. It states the rule,
   why it exists, a refused program and the same program fixed.
3. Fix the cause the explanation names, not the first symptom; prefer
   the smallest change that follows the rule.
4. Run `check` again, then the `test` tool, until both are clean.

When a diagnostic seems wrong, say so instead of working around it.
