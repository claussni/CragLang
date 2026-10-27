# Examples

Small programs to read, run and change. Each is a project of its own,
with a `package.crag`, its `main` module and tests under `test/`.

| Example | What it shows |
| --- | --- |
| `hello` | Printing a line, a function with string interpolation |
| `files` | Reading a text file and printing its lines numbered, handling each way it can fail |
| `web` | Loading a web page over HTTP: a connection, a request, reading the response until the server closes it |

Build the `crag` command first (see the main README), then go into an
example's directory.

## On the command line

    cd examples/hello
    crag run
    crag test

`crag run notes.txt` in `files` prints that file, and without an argument
`poem.txt`. `crag run example.org /` in `web` loads that page, and without
arguments `http://example.com/`; its test serves a page from a local
server instead, so it needs no network. The tests use the assertions of
`std.test`.

## In the editor and the REPL

`crag` without arguments opens the editor on the project. Ctrl+E
evaluates the line under the cursor in the scratch image, F1 tells what a
name is, and F12 goes to its definition. In the REPL (Alt+3), import the
module to use its functions:

    scratch> import std.io
    scratch> import hello.main
    scratch> greeting("Ada")
    "Hello, Ada!"
    scratch> printLine(greeting("Ada"))
    Hello, Ada!

`:start` runs the program's `main` in an app image, and what it prints
shows in the REPL. In `web`, try another page:

    scratch> import web.main
    scratch> fetch("example.com", 80, "/")

## Limits for now

- Only plain HTTP: TLS is not built yet, so a site that only answers on
  HTTPS sends a redirect.
- File functions take the path as a `Str` until `std.path` exists.
