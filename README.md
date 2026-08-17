# Fledge

Fledge is the stage-0 bootstrap compiler for [Kite](https://github.com/kitelang-io),
written in OCaml. It compiled the first native build of the Kite
compiler-in-Kite, producing the seed binary the self-hosted compiler bootstraps
from. Kite has since outgrown it, and Fledge is now frozen and archived; this
repository keeps it as a bootstrap-history reference and an independent frontend
oracle.

## What it implements

Kite's surface syntax is Kotlin-flavored and expression-oriented — `if`, `when`,
and `{ ... }` blocks all produce values. Fledge covers the bootstrap subset:

- **Lexer** — hand-written tokenizer with Go-style automatic terminator
  insertion (newlines end statements; no semicolons) and string interpolation
  (`"$name ${ expr }"`).
- **Parser** — recursive-descent for declarations and statements with a Pratt
  (precedence-climbing) core for expressions. Handles `fun`/`val`/`var`, structs,
  enums, traits/`impl`, `when`, lambdas, null-safety operators (`?`, `?.`, `?:`,
  `!!`), generics, and function types.
- **Semantic checker** (`kitec check`) — two M2 passes: name resolution (flags
  duplicate top-level definitions and unresolved value identifiers) and a
  deliberately lenient type checker that reports only definite mismatches and
  treats anything it cannot yet reason about as compatible.
- **AArch64 / Mach-O backend** — a self-contained native toolchain: its own
  machine-code encoder, its own Mach-O object writer, and its own linker
  (`write_executable` lays out the segments, resolves intra-image relocations,
  emits dyld chained-fixups bindings, and ad-hoc code-signs). No `as`, `ld`, or
  `clang` is involved — only dyld touches the produced binary at runtime. The
  backend lowers a monomorphic subset (Int functions, `val`/`var`, arithmetic and
  comparisons, `if`/`while`/`for i in a..b`, integer `when`, calls and recursion,
  and `print`/`println` via libc `printf`); `main`'s Int result becomes the
  process exit code.

## Build and run

Requires OCaml and dune.

```sh
dune build
dune exec bin/main.exe -- <command> <file.kite>
```

Commands:

| Command | Description |
| --- | --- |
| `version` | print the compiler version |
| `lex <file>` | tokenize and print the tokens |
| `parse <file>` | parse and print the AST |
| `check <file>` | name resolution + type check |
| `asm <file>` | emit AArch64 assembly for the codegen subset |
| `obj <file>` | emit a Mach-O `.o` directly |
| `exe <file>` | self-link a runnable Mach-O executable |
| `run <file>` | self-link a native binary and run it |

`reseed.sh` reproduces Fledge's role in the Kite repo: it compiles the Kite
compiler sources into the bootstrap seed. Point `KITE_ROOT` at a Kite checkout.

## Status

Frozen. The self-hosted Kite compiler moved to method-call syntax that Fledge no
longer parses, so it is retired from the bootstrap path — the committed seed is
now the sole bootstrap. It is preserved here as a record of how Kite first came
up, and its parser and checker remain a useful second, independent implementation
of the Kite frontend to diff the self-hosted one against.
