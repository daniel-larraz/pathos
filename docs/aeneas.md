# The compiled checker in Lean: how it is translated

`pathos` checks a cvc5 proof with a checker that Ethos's `rust-meta` stage
compiles from logos's signature ([pathos-cpc.md](pathos-cpc.md)). The plan
is to prove with [Charon](https://github.com/AeneasVerif/charon) and
[Aeneas](https://github.com/AeneasVerif/aeneas) that this checker computes
what logos's checker computes. Charon turns the Rust crate into a file of
its own format (LLBC), and Aeneas turns that into Lean definitions that a
proof can be about. Aeneas takes only a part of Rust, so the first question
was whether the compiled checker can be written in that part and what it
costs. Milestone 28 answered it: it can, and the checker got faster. Nothing
is proved yet.

This document says what is translated and what is assumed, what the
generator and the runtime avoid for the two tools, and how to run the
translation again.

## What is translated

The crate is `generated/cpc-checker`, written by
`scripts/generate-cpc` and never by hand. Its parts, for the translation:

| Part | Files | In the Lean |
| --- | --- | --- |
| The runtime that the generated code rests on: terms and their table, constructors, native operations, the operators on literals, the caches | `lib.rs`, `native.rs`, `lit.rs`, `kind.rs`, `bitvec.rs`, `eostring.rs`, `table.rs`, `cache.rs`, `schema.rs` | Definitions |
| The generated functions, with the list operators and the entry points of checking among them | `generated_part0.rs` to `generated_part12.rs` | Definitions |
| Numbers, over `malachite` | `num.rs` | Axioms: 46 functions and the two types |
| What works on text: names of constructors, reading of constants and numerals, printing, and the thread the checker runs on | `front.rs`, `names.rs` | Axioms for the four functions the rest calls |

### What a proof would assume

These are all the axioms of the thirteen Lean files, apart from the
functions of other parts (see "The parts" below).

- **Numbers** (`num.rs`). The types `Integer` and `Rational`, and
  - of `Integer`: `zero`, `one`, `add`, `mul`, `neg`, `pow`, `sgn`,
    `fits_u32`, `to_u32`, `euclidean_qr`, `floor_div_quotient`,
    `floor_div_remainder`, `mod_by_pow2`, `multiply_by_pow2`,
    `extract_bit_range`, `one_extend`, `bitwise_and`, `bitwise_or`,
    `bitwise_xor`, `bitwise_not`, `hash_code`, conversion from `u32` and
    from `usize`, and its `clone`, `==`, `cmp` and `partial_cmp`;
  - of `Rational`: `from_integer`, `from_integers`, `numerator`,
    `denominator`, `add`, `mul`, `div`, `neg`, `pow`, `floor`, `sgn`,
    `hash_code`, and its `clone`, `==` and `partial_cmp`.

  `hash_code` only says where a search of the table of terms starts; the
  search compares the numbers, so nothing about its value needs assuming
  except that equal numbers have equal hashes.
- **Text** (`front.rs`), four pure functions: `parse_int` and `parse_rat`
  (the numerals written in the generated code), `native_literal` (a native
  constant written as text, by its number in a generated list) and
  `constant_name` (the names `@u.n` and `@c.n`).
- **Printing**, which no checking function calls: the `Debug` of
  `Integer`, `Rational`, `Constructor` and `CheckError`, the `Display` of
  `CheckError`, and one function of the standard library that the derived
  `Debug` of `TermData` uses.
- Two declarations that Aeneas always writes and nothing uses (`!=` on
  `bool`, the type `MaybeUninit`).

No function of the standard library that a checking function calls is an
axiom: where Aeneas's library has no model (for example `Vec::pop`,
`retain`, `?` on an `Option`, `==` on an `Option`), the runtime has code of
its own.

Outside the translated crate altogether, and so outside any proof: the
front end of `crates/pathos` that reads a proof and builds the checker's
input.

### Overflow

The Lean that Aeneas writes fails where Rust's arithmetic overflows, as a
debug build panics. A release build wraps instead, unless told otherwise,
and would then be another program than the translated one exactly there.
So the checker crate is built with overflow checks in release builds too
(`[profile.release.package.pathos-compiled-checker]` in `Cargo.toml`): an
overflow in it is a panic. What is proved about the Lean
([proofs/](../proofs/)) is about builds with that setting;
`scripts/proofs-build --no-build`, which CI runs, fails without it. The
setting is for that one package. It costs nothing that can be measured:
with and without it, in turn, the 400 proofs took 9.1 s, 9.2 s, 9.2 s
against 9.4 s, 9.2 s, 9.2 s, and the 39 large ones 137.0 s, 136.2 s
against 136.7 s, 139.0 s (2026-11-18), every verdict the same. The two
hash functions multiply with `wrapping_mul`, which is not an overflow.

## What the code avoids

The checker was rewritten for the two tools, in the generator and the
runtime of Ethos (`plugins/rust_meta`), over five rounds. What turned out
to matter, as rules:

**For Charon**

- No `?` inside an arm of a `match` that more code follows. Charon's output
  tripled with each one; ten in a row needed more than 4 GiB.
- No function with hundreds of fallible calls in a row: its reconstruction
  of the control flow nests once per call and stops with "stack depth limit
  exceeded".
- A pattern given to `--opaque` or `--exclude` that matches nothing is
  accepted without a word. What is opaque is checked in the LLBC.

**For Aeneas**

- No comparison of text in the translated part. A `match` on a `&str` is a
  chain of comparisons whose translation grows as about N^2.7; constructors
  and operations are enums, and names live in `front.rs`.
- No closure that captures `&mut`, no labelled block, no `break` or
  `continue` to an outer loop, no function pointer as a parameter, no `dyn`.
- An early return in a loop only where the loop is the last thing of its
  function or keeps its result in a variable.
- No `match` on a borrowed value inside a loop: the match is a function
  called from the loop.
- Aeneas follows every path through a function and joins paths only at
  loops. A long function with tests in a row is expensive, so functions are
  short and many. Reading the discriminant of an enum splits a path once
  per variant: two `Constructor`s (1,054 variants) are compared by a
  generated number, not by `as u32` or the derived `==`.
- No `&'static str` in a type with derived `Clone`, `PartialEq` or `Debug`.
- Aeneas translates the functions of its input in parallel on every core
  but one, with no option for that number, and its memory is what its
  workers hold at once, not the size of its input. On 20 cores parts of CPC
  need more than 8 GiB; on 4 cores (`taskset`) the largest needs 2.

**For the Lean that Aeneas writes** (constraints of Aeneas and Lean that
the generator and the runtime work around. Issue drafts for some of them
exist; none is filed)

- A variant must not have the name of a Lean type that Aeneas prints:
  `Lit::Boolean` and `Lit::Str`, not `Bool` and `String`. Inside the
  definitions about `Lit`, `Bool` would mean the constructor `lit.Lit.Bool`.
- A local variable must not have the name of a module of the crate: the
  runtime has modules `lit` and `kind`, and `lit.Lit.hash_code lit` would be
  read as a field of the variable.
- Nesting: the rest of a function is nested once more at each fallible call
  and each pattern, and at about seventeen levels Aeneas's printer breaks a
  pattern over two lines where Lean cannot read it. A generated body is cut
  after 12 statements and goes on in a further function; cases are tried in
  groups of four.
- A loop must not be in a function that is called again from inside the
  loop, if the loop is written with Aeneas's `loop` combinator (its
  default): Lean cannot show the definition monotone. 21 of the 65 programs
  of CPC that are compiled to a loop are like that, so Aeneas is run with
  `-loops-to-rec`, which writes every loop as a recursive function.
- The three largest groups of functions that call each other (`$eo_typeof`
  with the list operators, `$run_evaluate`, `$eo_to_smt`: 220 to 270
  definitions in one `mutual` block each) need more of Lean's work than
  Aeneas's default limit allows: `-max-heartbeats 20000000`.

## The parts

The generated functions are about 124,000 lines, and Aeneas's time grows
with what it is given, so they are in modules, `generated::part0` to
`part12`. The generator makes them from the call graph of the functions it
writes:

- functions that call each other, directly or through others, are in one
  module (the largest such group is `$run_evaluate`, 3,975 lines when this
  was measured);
- a module calls only itself, earlier modules and the runtime;
- a module is closed when the next group would take it past 10,000 lines.

The list operators and the entry points of checking are runtime code that
calls generated functions (`$eo_typeof`, `$eo_nil`, `$eo_is_list_nil`;
`$eo_checker_is_refutation` and the translation functions). The generator
places them in the same graph, so they are in `part0` and in the last part,
and the runtime beside them calls no generated function.

One run of the tools translates the runtime and one part, the others
opaque. In that part's Lean file a function of another part is an axiom
under the name it has in its own file, for example
`generated.part0.eo__24eo_5ftypeof`. Since a part calls only earlier parts,
the files can be put together in their order, each importing the earlier
ones in place of its axioms.

**Putting them together is not done.** Each file repeats the runtime's
definitions (about 27,000 lines), and is built on its own, as it is. Making
one development of them (the runtime once, the axioms replaced by imports)
belongs to the work on the proofs.

## Running it again

```
scripts/aeneas-setup DIR          # Charon and Aeneas at pinned commits, in DIR
scripts/aeneas-translate DIR      # every part of generated/cpc-checker
```

`scripts/aeneas-setup` clones and builds Aeneas `1dc8ad31` with the Charon
it pins (`454586e9`) in an opam switch of its own; Charon needs the Rust
nightly its `rust-toolchain` names. `scripts/aeneas-translate` runs, for
each part, Charon and then Aeneas (`-backend lean -loops-to-rec
-max-heartbeats 20000000`, under `taskset -c 0-3`), each under an 8 GiB
cap, and checks that

- both end without an error and Aeneas writes a Lean file;
- in Charon's output no function of `front`, of `num` or of another part
  has a body;
- every axiom of the Lean file for a generated function names an earlier
  part. The generator checks the same from the calls it finds in its own
  text; a use of a function that is not written as a call would show only
  here.

It prints the table below and writes it to `target/aeneas/parts.tsv`; the
Lean files are in `target/aeneas/part<k>/lean/`.

To compile the Lean: Aeneas's library is `backends/lean` of its checkout,
at Lean `v4.36.0-rc2` (logos is at `v4.34.0`), with Mathlib. In that
directory `lake exe cache get` and `lake build` (158 s, 4.3 GiB here); then
a Lake project that requires it by path and holds the thirteen files as
modules, built one at a time (`lake build Parts.Part0`, ...) under the cap.

### The measurement

On the development machine (20 cores), the crate generated from Ethos
`cc027fc` (branch `m28-aeneas` of the fork) and logos `a3232131`; every run
under an 8 GiB cap, one at a time; Aeneas on 4 cores.

| Part | Rust lines | Charon | LLBC | Aeneas | Lean lines | Axioms: numbers, text, other parts | Lean build |
| --- | --- | --- | --- | --- | --- | --- | --- |
| 0 | 9,995 | 43 s, 1.6 GiB | 67 MiB | 61 s, 1.5 GiB | 59,009 | 46, 4, 0 | 245 s, 4.7 GiB |
| 1 | 9,994 | 8 s, 1.5 GiB | 76 MiB | 75 s, 1.6 GiB | 59,648 | 46, 3, 9 | 114 s, 3.7 GiB |
| 2 | 10,004 | 8 s, 1.5 GiB | 84 MiB | 85 s, 1.7 GiB | 60,286 | 46, 4, 26 | 103 s, 3.6 GiB |
| 3 | 9,989 | 9 s, 1.5 GiB | 104 MiB | 108 s, 1.9 GiB | 63,321 | 46, 3, 23 | 106 s, 3.7 GiB |
| 4 | 9,996 | 8 s, 1.5 GiB | 95 MiB | 104 s, 1.9 GiB | 64,497 | 46, 3, 20 | 117 s, 3.8 GiB |
| 5 | 9,977 | 8 s, 1.6 GiB | 79 MiB | 81 s, 1.7 GiB | 61,182 | 46, 4, 40 | 104 s, 3.6 GiB |
| 6 | 9,998 | 9 s, 1.6 GiB | 107 MiB | 102 s, 2.0 GiB | 62,259 | 46, 4, 13 | 97 s, 3.5 GiB |
| 7 | 10,000 | 9 s, 1.7 GiB | 115 MiB | 116 s, 1.9 GiB | 63,856 | 46, 3, 9 | 99 s, 3.5 GiB |
| 8 | 9,981 | 9 s, 1.7 GiB | 111 MiB | 108 s, 2.0 GiB | 61,937 | 46, 3, 10 | 96 s, 3.5 GiB |
| 9 | 9,998 | 9 s, 1.6 GiB | 106 MiB | 103 s, 2.0 GiB | 62,029 | 46, 3, 11 | 96 s, 3.5 GiB |
| 10 | 7,784 | 8 s, 1.5 GiB | 79 MiB | 78 s, 1.5 GiB | 53,016 | 46, 4, 10 | 92 s, 3.4 GiB |
| 11 | 9,344 | 7 s, 1.5 GiB | 68 MiB | 57 s, 1.4 GiB | 54,010 | 46, 4, 58 | 212 s, 4.5 GiB |
| 12 | 6,875 | 7 s, 1.5 GiB | 50 MiB | 48 s, 1.3 GiB | 50,463 | 46, 2, 111 | 292 s, 4.5 GiB |

Every run ends without an error. Aeneas takes 19 minutes in all and the
Lean builds 30. (The first run of Charon also compiles the crate's
dependencies.) The rows of parts 0, 11 and 12 are of a last run of
`scripts/aeneas-translate` as it is here, with `-max-heartbeats`, and of
the Lean builds of the files it wrote. The other ten are of the run before
it, without that option; they compile with Aeneas's default limit, which is
the only thing the option changes in a file.

For comparison, the checker as it was before this work (Ethos `d83d2ab6`):
Charon ran out of 16 GiB on the crate within a minute, and Aeneas ran out
of 16 GiB on the runtime alone.

What the rewrite did to the checker itself is in
[pathos-cpc.md](pathos-cpc.md), "Measurements": it is faster and uses less
than half the memory, mostly from the runtime's own table of terms.
