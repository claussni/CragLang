# Crag

Compiler, host and runtime for the Crag language, written in Rust.

- [The Crag Language Specification](https://claude.ai/artifact/F6igCJwVvKV8YEpCjbAeYt)
  defines the language; its second tab, Compiler architecture, records how
  the toolchain is built.
- [The Crag Implementation Plan](https://claude.ai/artifact/8pd9u6ieT65wez3S2hiU5N)
  lists the milestones and components.

The documents live as Claude Docs documents and are edited there.

## Layout

| Crate | Components |
| --- | --- |
| `crates/crag-runtime` | Fiber runtime, stack growth, side stack, sentinel, stress harness, allocator, reference counting and the queue of disposals, lists and maps, the scheduler, the I/O poller and timers, scopes and cancellation, streams and hubs, refs, transactions, ext locks, signals of blocks, lazy cells and deferred teardown, strings and bytes, traps |
| `crates/crag-abi` | Constants shared by generated code and the runtime |
| `crates/crag-codegen` | Cranelift facade |
| `crates/crag-loader` | Code loader |
| `crates/crag-db` | Salsa facade |
| `crates/crag-store` | Artifact store: content-hashed artifacts, the file lock, project roots and garbage collection (M6) |
| `crates/crag-syntax` | Lexer, parser and syntax tree (M1) |
| `crates/crag-hir` | Item trees, names and imports, and HIR lowering (M1) |
| `crates/crag-types` | Types and core inference (M1) |
| `crates/crag-mir` | MIR builder (M1) |
| `crates/crag-backend` | Code generation from MIR (M1) |
| `crates/crag-driver` | The `crag` command: `run`, `test` and `fmt`, diagnostics (M1); the UI with the built-in editor, the app image, hot reload, the debugger, the language server `crag lsp` and the debug adapter `crag dap` (M5) |
| `crates/crag-session` | Session manager: image processes, their protocol and supervision (M3) |
| `crates/crag-eval` | Compile-time evaluation of constants, `embed`s among them, in the metered tier (M3) |
| `crates/crag-fmt` | The formatter: the canonical layout of source files (M5) |
| `crates/crag-package` | Packages: manifests, versions, folder registries, resolution and the SBOM (M6) |
| `std` | The standard library: the prelude `std.core` with its functions on text, bytes and collections, `std.time`, `std.task`, `std.stream`, `std.io`, `std.env` and `std.test` |
| `examples` | Small programs to run and explore: hello world, reading a file, loading a web page |

## Build

The toolchain is pinned in `Dockerfile` (Rust 1.99 with rustfmt and clippy).
The `./cargo` wrapper builds that image on first use and runs cargo inside it,
so only Docker is needed on the host.

    ./cargo build
    ./cargo test
    ./cargo clippy --all-targets
    ./cargo fmt

Three settings stress the runtime: `CRAG_TORTURE=1` moves a fiber's stack
at every stack check, `CRAG_JITTER=<seed>` adds random delays at every
suspension point and wake, and the loom models check the lock-free parts
under every interleaving that matters:

    CRAG_TORTURE=1 ./cargo test
    CRAG_JITTER=7 ./cargo test
    RUSTFLAGS="--cfg loom" CARGO_TARGET_DIR=target/loom \
        ./cargo test -p crag-runtime --release --lib loom_model

The `crag` command works on the project in the current directory, a
directory with a `package.crag` naming the package and its `main` module:

    ./cargo build -p crag-driver
    cd my-project
    /path/to/target/debug/crag run [argument...]
    /path/to/target/debug/crag test [filter]
    /path/to/target/debug/crag fmt [--check] [all | - | file...]

`crag run` passes what follows it to the program, which reads it with
`args()` of `std.env`. A test checks with the assertions of `std.test`;
`crag test` reports every one that failed, at its line, and the test goes
on after it.

`crag fmt` formats every module of the project in place, or the files
named; `-` formats standard input to standard output, and `--check` only
lists the files that are not formatted.

`examples/` holds small projects to start from: `hello`, `files`, which
prints a text file, and `web`, which loads a web page. Its README tells
how to run them and explore them in the editor and the REPL.

Packages come from folder registries, which `registries.crag` in the
settings directory (`$CRAG_HOME`, else `~/.crag`) lists:

    registry team "/srv/crag"

`crag registry new <name> <folder>` makes an empty registry and adds it
there; `crag registry add <name> <folder>` adds one that exists, such as a
team's shared folder. `crag registry list` and `crag registry remove
<name>` show and edit the list; removing leaves the folder as it is.

`crag new <name> [--lib]` creates a project; `crag add <package>
[version]`, `remove`, `upgrade <package> [--version=V] | all`, `outdated`
and `deps` manage its imports. Each major of a package settles on the
highest version any manifest requires; the committed `sbom.crag` pins the
content hash of every package, and a build refuses a mismatch until `crag
sbom regenerate` accepts it on purpose. `crag sbom diff` shows the change.

`crag publish <registry>` checks a library and places it into a registry:
its tests pass, it has no type holes, and its `api.crag`, the public
declarations with their inferred errors, effects and escaping parameters,
needs no larger version step than the one taken since the previous
version of its major. `crag package` builds the same folder in
`target/package/` without publishing it. In the REPL, `:add`, `:remove`,
`:upgrade`, `:outdated`, `:deps`, `:sbom`, `:package` and `:publish` do the
same, and the session can use an added package at once.

Compiled code is kept in the settings directory's `cache/`, so a second
run, `crag test` or a new session compiles only what changed;
`CRAG_CACHE_STATS=1` prints how much was reused.

`crag lsp` is the language server, for editors that speak the Language
Server Protocol: diagnostics as you type, hover, go to definition,
references, rename, completion, formatting and the outline. An editor
starts it in the project's directory, or names the project as its root.

With `CRAG_MIR=1`, `crag` also writes the MIR of what it compiles to
standard error, with what code generation does not support yet.

Without arguments on a terminal, `crag` opens the UI: the editor over the
REPL, buffers and files on the left, problems, tasks and watches on the
right. Ctrl+P switches files, Ctrl+K lists commands, F1, F12 and Shift+F12
tell about, go to and find a name, Ctrl+E evaluates the line in the
scratch image, F9 sets a breakpoint, Alt+R reloads the app and Ctrl+Q
quits. The line at the bottom shows the keys that matter where the focus
is, and the command palette names the key of each command. Without a
terminal, `crag` is the plain REPL.

`:help` lists the REPL's commands. In a project,
`:start` runs the app in an image of its own; after editing its files,
`:reload` swaps the changed code into the running app, which keeps its
state and connections, and `:stop` ends it. `:break file:line` stops the
app's tasks at a line; `:paused`, `:locals`, `:step`, `:next`, `:out` and
`:continue` inspect and drive them.

`crag dap` is the debug adapter, for editors that speak the Debug Adapter
Protocol: `launch` with `"project"` naming the project's directory runs
the app, with line breakpoints, stepping and locals.

    /path/to/target/debug/crag

## Use of Claude Code

Crag is designed and implemented with the help of
[Claude Code](https://claude.com/claude-code), Anthropic's coding agent. This
covers the specification documents as well as the code in `crates/`. Ralf
Claussnitzer directs the work, reviews the results and is responsible for
them.

## License

Copyright (C) 2026 Ralf Claussnitzer

Crag is free software: you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version. Crag is distributed without any warranty. See [LICENSE](LICENSE) for
the full text.
