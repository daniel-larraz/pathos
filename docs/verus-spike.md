# A Verus feasibility spike

Milestone 17 of [brief.md](brief.md). [Verus](https://github.com/verus-lang/verus)
proves Rust code against specifications with an SMT solver. This spike
verifies two small parts of pathos and measures what that cost, so that a
decision can be made on going further. It does not show that pathos is sound.

## Summary

- **Both parts verify.** Verus checks 165 functions and proofs in
  `pathos-term` with no errors, in about 30 seconds.
- **Literal operators.** `Lit::evaluate` meets a specification written with
  mathematical integers and reals for the twelve operators the milestone
  names, and cannot panic on any operator.
- **Term store.** Every handle the store returns is a handle of the store,
  two terms with the same tree are the same term, and the store's
  term-making and reading functions cannot panic. The snapshot reader and
  writer are not verified.
- **No dependency was added.** The specifications sit in the shipped source
  behind a `cfg` that only Verus sets. `Cargo.toml` gains one lint entry;
  `Cargo.lock` and the binaries' dependencies are unchanged.
- **The code had to change in about twenty places**, none of which changes
  what pathos prints. They are listed under "What had to be rewritten".
- **The cost was about two lines of specification and proof for each line
  of code in scope**: 955 lines of specification and 931 of proof against
  about 940 lines of code.
- **Verification found no bug** in the two parts.
- **`malachite` is trusted**, through the 38 functions of `num.rs` that wrap
  it, whose specifications are assumed. About 35 other statements are
  assumed too. All are listed under "What is assumed".

What needed a decision is under "For Daniel".

The spike was milestone 17. The work continues on the branch `verus`
(see "The `verus` branch" in [brief.md](brief.md)), and each later
milestone adds a section at the end of this file:

- [Milestone 18: matching cannot panic](#milestone-18-matching-cannot-panic)
- [Milestone 19: matching is correct](#milestone-19-matching-is-correct)
- [Milestone 20: the snapshot reader cannot panic](#milestone-20-the-snapshot-reader-cannot-panic)

## The setup

**The release.** Verus `0.2026.11.02.8bf68ee`, the newest release that is not
a prerelease when the spike was made, for Linux x86-64. `scripts/verify`
pins the version, the SHA-256 of the archive and the Rust toolchain.

**The toolchain.** That release runs on Rust 1.99.1, which is also pathos's
`rust-version` and today's stable. Verus needs the toolchain installed under
its full name (`1.99.1-x86_64-unknown-linux-gnu`); `scripts/verify --setup`
installs it with `rustup`.

**How verified code sits in the workspace.** The code that ships is the code
that is verified; there is no second copy. Three mechanisms make that work
without a dependency:

- Verus sets `cfg(verus_keep_ghost)` when it runs. Every specification is an
  attribute `#[cfg_attr(verus_keep_ghost, verus_spec(...))]` on the function
  or loop it describes, and every specification function and proof is inside
  `#[cfg(verus_keep_ghost)] verus! { ... }`. A Cargo build never sees them.
- Proof steps inside function bodies are written `proof! { ... }` and
  `proof_decl! { ... }`. In a Cargo build these are two `macro_rules!` macros
  in [lib.rs](../crates/pathos-term/src/lib.rs) that expand to nothing.
- Verus is run directly on `crates/pathos-term/src/lib.rs`, not through
  Cargo, and brings its own copy of its library (`vstd`). `scripts/verify`
  first builds `malachite` with Cargo and the pinned toolchain, and passes
  those builds to Verus.

**Running it.** `scripts/verify` (add `--setup` the first time). It exits 1
if a proof fails, and also if Verus checked fewer than 165 items, which
would mean specifications were removed.

**The CI job.** `verify` in
[ci.yml](../.github/workflows/ci.yml) runs `scripts/verify --setup` on
`ubuntu-24.04` on every push to `main` and every pull request, and uploads
the log. It has not run yet: the reviewer pushes and starts CI runs.

## What was verified

Verus checked 165 items with no errors. An item is a function, a proof, or a
specification function whose termination had to be shown.

### Literal operators

The specification is `eval_spec` in
[lit.rs](../crates/pathos-term/src/lit.rs). It maps an operator and its
arguments to one of three answers: evaluates to this value, does not
evaluate, or not specified here. `Lit::evaluate` is proved to agree with it
wherever it specifies something. A literal's value is a `Val`: a numeral is
an `int`, a rational or decimal is a `real`, a binary or hexadecimal is its
width and its value as an `int`.

| Operator | On | What the specification says |
| --- | --- | --- |
| `eo::add`, `eo::mul` | numerals; rationals or decimals | The sum or product of all arguments, as integers or reals. The result has the kind of the arguments. |
| `eo::neg` | numerals; rationals or decimals | The negation of the first argument. |
| `eo::zdiv`, `eo::zmod` | numerals | Euclidean division: the remainder is never negative. Does not evaluate when the divisor is 0. |
| `eo::qdiv` | numerals; rationals or decimals | The quotient as a real, always a rational literal, also for decimals. Does not evaluate when the divisor is 0. |
| `eo::and`, `eo::or`, `eo::xor` | binaries | Bit by bit, on arguments of one width; does not evaluate when widths differ. |
| `eo::not` | binaries | `2^width - 1 - value`. |
| `eo::concat` | binaries | Width `(w1 + w2) mod 2^32`, value `(v1 * 2^w2 + v2) mod 2^width`. `BitVec::concat` also proves nothing is cut off unless the width wraps. |
| `eo::extract` | binaries | Bits `i1 ..= i2`, with Ethos's rules: no bits if an index is negative, `i1` is past the width or the width is 0; `i2` is cut to `width - 1` only when it is greater than the width, so `i2 == width` reads one zero bit past the end. |

Three things hold for every operator, not only these twelve:

- All of the above also covers hexadecimal literals, which share the code.
- An operator whose arguments are of different kinds does not evaluate
  (except `eo::extract`, which takes a binary and two numerals).
- `Lit::evaluate` does not panic, given the trusted functions below.

The n-ary operators are specified as a fold from the left over all the
arguments, and the proof is a loop invariant for each kind of literal.

I checked that the proofs are not empty: eight wrong specifications, one
for each family above (for instance `x / y + 1` for `eo::zdiv`, or
`i2 >= width` in `eo::extract`), each fail to verify, and so does
`assert(false)` at the start of `evaluate`.

### The term store

The invariant is `TermStore::wf` in
[store.rs](../crates/pathos-term/src/store.rs). It says:

- **Handles are valid.** Every child of a compound term, every cached type
  and the four built-in terms are positions in the store, and a child comes
  before its parent. Child ranges lie inside the child pool; name and
  literal numbers lie inside their tables.
- **The tables are right.** Each hash table holds exactly the compound terms
  (or the literal terms), each at a slot that a lookup of its hash reaches
  before it reaches an empty slot.
- **No two terms are alike.** No two compound terms have the same kind and
  children, no two literal terms the same value, no two symbols the same
  name entry.

What is proved from it:

| Property | Where |
| --- | --- |
| `new` gives a store for which the invariant holds; `mk`, `mk_apply`, `mk_lit`, `mk_symbol` and `set_ty` keep it. | their `ensures` |
| The term a function returns is a term of the store (`has`). | their `ensures` |
| Terms made earlier are still there and unchanged (`extends`). | their `ensures` |
| Unless a size limit was hit, `mk` returns the term of that kind with those children, and `mk_lit` the term of that value. | `is_node`, `is_lit` |
| **The view is injective:** two terms of a store with the same tree are the same term. | `theorem_same_tree_same_term` |
| Making terms does not change the tree of an existing term. | `theorem_trees_are_kept` |
| None of these functions, nor `kind`, `children`, `child`, `data`, `lit`, `symbol_name`, `ty`, `is_ground`, `is_evaluatable` and the rest of the readers, can panic when called with terms of the store. | Verus checks every index, cast and arithmetic step |

The view (`TermStore::tree`) takes a handle to a `Tree`: a compound term is
its kind and its children's trees, a literal is its value, and a symbol is
itself, because every `mk_symbol` makes a new term, as in Ethos.

The hash table (`ConsTable`) is verified on its own: `find` returns a
matching handle or the empty slot where the probe ended having met no
match; `insert_new` and `grown` keep every handle reachable.

Eleven deliberate faults are each caught: `assert(false)` after each of the
store's mutations, comparing only the tag in `mk`, stepping the probe by
two, swapping the children of an application, not appending to the child
pool, not storing the literal, and dropping the overflow check of the child
range.

### What "cannot panic" leaves out

- **Preconditions are obligations on callers.** The store's functions
  require that the terms passed in are terms of this store, that `child(t,
  i)` has `i` below the number of children, and that `mk` is not asked for a
  symbol or literal kind. The callers are in other crates and are not
  verified.
- **Termination of the two probe loops is not proved.** They end because
  the table is never full; proving it needs a count of the terms against
  the table size, which I left out. Every other loop is proved to end.
- **Allocation.** Verus does not model running out of memory or a vector
  too large to allocate.
- **64-bit targets.** The proofs fix `usize` at 64 bits.

### Not verified

- `TermStore::read_from` and `write_to` (snapshots), about 200 lines. A
  store read from a snapshot is assumed to satisfy the invariant; its
  documentation says it checks exactly that, and a test damages every byte
  of a snapshot to look for a panic.
- `hash_node`, `tag_of`, `heap_bytes`, and everything about strings
  (`EoString`), printing and parsing.
- The operators outside the twelve: `evaluate` is proved not to panic on
  them, but nothing is said about their results, and `integer_floor_log`
  (`eo::log`) is trusted not to panic.

## What is assumed

Each line is something Verus takes on trust.

**`malachite`, through the wrappers in
[num.rs](../crates/pathos-term/src/num.rs).** Each of the 38 is marked
`external_body`: its `ensures` is assumed, and so is that it does not panic
when its `requires` holds. All but the parsing functions are one call into
`malachite` (two or three lines for `extract_bit_range` and `one_extend`).

| Wrapper | Assumed |
| --- | --- |
| `Integer::zero`, `one`, `From<u32>`, `From<usize>` | the value is 0, 1, the argument |
| `Integer::neg`, `add`, `sub`, `mul` | `-x`, `x + y`, `x - y`, `x * y` |
| `Integer::sgn` | -1, 0 or 1 by the sign |
| `Integer::gt` | `x > y` |
| `Integer::floor_div_quotient`, `floor_div_remainder` | for `y != 0`: the quotient rounded down, and `x - y * quotient` |
| `Integer::mod_by_pow2` | `x mod 2^e`, never negative |
| `Integer::multiply_by_pow2` | `x * 2^e` |
| `Integer::extract_bit_range` | `(x mod 2^(low + count)) / 2^low` |
| `Integer::bitwise_and`, `bitwise_or`, `bitwise_xor` | for `x, y >= 0`: the operation bit by bit |
| `Integer::bitwise_not` | `-x - 1` |
| `Integer::fits_u32`, `to_u32` | `0 <= x <= 2^32 - 1`, and then the value |
| `Rational::from_integers` | `None` exactly when `d` is 0, else `n / d` |
| `Rational::from_integer`, `neg`, `add`, `mul`, `div`, `sgn` | the same on reals; `div` requires a non-zero divisor |
| `Integer::pow`, `one_extend`, `length`, `parse`, `to_string_base`; `Rational::pow`, `floor`, `parse`, `from_decimal`, `is_integral` | only that they do not panic (they are outside the twelve operators) |

`Integer::euclidean_qr` is not in the table: it is verified against the two
floor-division wrappers.

**Equality and copying.** Verus does not look into derived trait
implementations.

- The derived `==` of `Lit`, `Kind`, `SymbolKind`, `LitKind`, `NodeKind` and
  `EvalOp` is equality of values (six statements). For `Lit` this includes
  that `malachite` keeps numbers in one form.
- `clone` of `Integer`, `Rational`, `BitVec`, `EoString`, `Lit` and `Term`
  gives an equal value (six).
- `same_terms`: `==` on two slices of terms is equality of the sequences.

**Hashing.**

- `hash_node` and `hash_lit` are functions of their arguments (they are not
  verified, and are trusted not to panic).
- `tag_of` gives different compound kinds different tags. The test
  `compound_kinds_have_different_tags` checks this for every kind.
- `HashKeys::random` and `RandomState::new` return.

**The standard library**, where Verus's library says nothing:

- `Option::filter` returns the value only if the closure accepts it.
- A `Vec<u32>` holds at most `2^61 - 1` elements (the limit of
  `isize::MAX` bytes).
- `EoString::default` returns.

**Other trusted functions.** `Term::first` is the handle at position 1.
`atomic_kind` holds the `panic!` of `mk` and requires `false`, so Verus
proves it is never reached from verified code. `BitVec::parse` gives a value
that fits its width. `EoString`'s eight functions: `len` and `code_points`
agree on the length; the rest only do not panic.

**Verus itself**, its library `vstd`, and Z3.

## Rust features: accepted, rejected, rewritten

### Accepted as written

Enums with data and `match` on them, including or-patterns, guards and slice
patterns such as `&[f, a]`; `matches!`; `let ... else`; `?` on `Option`;
early `return` from inside loops; `for` loops over slices, with invariants
that refer to the iterator's position; tuples, references, arrays, `Vec`,
slices and sub-slices; `NonZeroU32`; `u32::try_from`, `checked_add`,
`wrapping_add`; shifts and masks (proved with the solver's bit-vector mode);
`as` casts; closures passed to generic functions; private fields and
`impl` blocks spread over a module.

### What had to be rewritten

None of these changes what pathos computes. The gates below show the same
results as before.

| Construct | Problem | Now |
| --- | --- | --- |
| `.map(Lit::Rational)`, `.map(Term)` | A constructor cannot be used as a function value. | A `match`, or `?` and `Some(Term(n))`. Clippy then asks for the `map` back; one `#[allow(clippy::manual_map)]`. |
| `MInt::ONE`, `NonZeroU32::MIN` | Associated constants of foreign types are not supported. | `Integer::one()`; a function `Term::first()`. |
| `q += MInt::ONE; r -= &y.0` in `euclidean_qr` | Operators on a foreign type cannot be given a specification from outside Verus's library (Rust's orphan rule). | Written with pathos's own wrappers, which makes two temporaries. |
| `*i1 > dsize` on `Integer` | Derived `PartialOrd` has no specification. | `Integer::gt`. |
| `args.iter().any(\|a\| ...)`, twice | Accepted, but the closure's meaning is unknown to the caller without a specification on it. | Two helper functions with a loop each: `all_of_kind`, `all_of_size`. |
| `Option::zip(...).filter(\|...\| ...)` in `mk` | No specification for `zip`; same closure problem. | `let (Ok(start), Ok(len)) = ... else`, then an `if`. |
| `impl FnMut` in `ConsTable::find` and `grown` | A closure that may change state has no usable postcondition. | `impl Fn`; the closures never changed state. |
| The closures passed to `find` and `grown` | Their specifications are attributes, and stable Rust accepts an attribute on a closure only where it is a function argument. | Named through an identity function `closure(...)`, inlined away. |
| `self.slots.len().trailing_zeros() + 1` | No specification for `trailing_zeros` on `usize`. | `64 - self.shift + 1`, the same number by the table's invariant. |
| `self.len * 10 >= self.slots.len() * 7` | Could overflow for a table larger than any that can exist; proving the bound needs a count of the terms. | The same comparison in `u128`. |
| `self.mk_count += 1` | Overflows after 2^64 requests, or at once after a crafted snapshot in a debug build ([panics.md](panics.md)). | `wrapping_add(1)`, which is what a release build did. |
| `panic!` in `mk` | `panic!` is not supported. | In `atomic_kind`, which requires `false`. |
| `self.lit_at(i) == Some(&lit)` | `==` on `Option<&Lit>` goes through several trait layers. | A helper `lit_is`. |
| `self.children_at(cand) == children` | No specification for `==` on slices. | A helper `same_terms`. |
| `lit_hasher.hash_one(&lit)` | Not supported. | A helper `hash_lit`. |

Two more things cost time without changing code:

- **A specification can change how a closure captures.** Mentioning `lit`
  in a closure's `ensures` moved it into the closure, which then no longer
  compiled. The fix was to borrow it first.
- **`mk` needs a larger solver budget** (`rlimit(200)`, twenty times the
  default) because the whole invariant is in scope in one long function.

### Left outside

Anything that formats or parses text, `Display` implementations, iterator
chains (`as_chunks` in `hash_node`), and the snapshot codec were not put to
Verus. `read_from` uses iterators, closures and tuples heavily and would
need the most rewriting of anything in the crate.

## Lines

Counted without blank lines and comments, and without tests.

| File | Code before | Code now | Specification | Proof |
| --- | --- | --- | --- | --- |
| `num.rs` | 191 | 215 | 80 | 52 |
| `bitvec.rs` | 95 | 97 | 70 | 95 |
| `lit.rs` | 417 | 440 | 290 | 41 |
| `store.rs` | 643 | 687 | 443 | 743 |
| `kind.rs` | 424 | 425 | 52 | 0 |
| `eostring.rs` | 128 | 134 | 18 | 0 |
| `lib.rs` | 13 | 29 | 2 | 0 |
| Total | 1,911 | 2,027 | 955 | 931 |

Specification is every `requires`, `ensures` and invariant, the
specification functions, and the assumed statements. Proof is the lemmas
and the `proof!` blocks. The counting script is simple and the split
between the two is approximate.

The code in scope is smaller than the files: about 360 lines of `lit.rs`
(`evaluate` and its helpers), 97 of `bitvec.rs` and 490 of `store.rs`
(everything but the snapshot codec), about 940 lines. Against that:

- **Literals** (`lit.rs`, `bitvec.rs`, `num.rs`): about 480 lines of code,
  440 of specification, 190 of proof. The specification is as long as the
  code because it restates each operator; the proofs are short.
- **Store**: about 490 lines of code, 440 of specification, 740 of proof.
  The proof is long because every change to the store has to re-establish
  an invariant with seven parts.

## Verification time

`scripts/verify` on this machine (20 cores): 30 seconds for Verus, of which
about 20 are the store and most of that is `mk`. Building `malachite` first
takes about 25 seconds the first time and nothing after. The CI job will
also download Verus (130 MB) and a Rust toolchain.

## The dependency options

The constraint: no new dependency in the shipped binaries, and no change to
`Cargo.lock`, without Daniel's agreement.

What Verus's crates are, at this release:

| Crate | Kind | `unsafe` code | In a binary? |
| --- | --- | --- | --- |
| `vstd` | library | 34 lines in 7 files (cells, raw pointers, atomics, threads) | Linked. Ghost code is erased, so little of it would remain, and nothing pathos would call is `unsafe`; but it is a dependency with `unsafe` code. |
| `verus_builtin` | library | 54 lines in 1 file (ghost wrapper types) | Linked. |
| `verus_builtin_macros` | procedural macros | none of its own | No: it runs at build time. It brings `syn`, `quote`, `proc-macro2`, `verus_syn`, `verus_prettyplease`, `synstructure` and `convert_case` into `Cargo.lock`. |
| `verus_state_machines_macros` | procedural macros | not looked at | No. A dependency of `vstd`; brings `indexmap`. |

They are published on crates.io with a version per Verus release
(`0.0.0-2026-11-01-0251` here), so a pin would move with every release.

| Option | `Cargo.lock` | Binaries | Notes |
| --- | --- | --- | --- |
| **A. Depend on `vstd`** and write `verus! { ... }`, the usual way (`cargo verus`). | Four Verus crates and about ten others. | `vstd` and `verus_builtin` linked. | Best syntax and tooling. Needs agreement, and `docs/dependencies.md` would have to account for both crates. |
| **B. Depend on them optionally**, behind a Cargo feature. | The same entries, also when the feature is off. | Unchanged when the feature is off. | Still a change to `Cargo.lock`. |
| **C. No dependency; specifications behind `cfg(verus_keep_ghost)`; Verus run directly.** Used for this spike. | Unchanged. | Unchanged. | Specifications are attributes, which read worse than `verus!` syntax; needs the workarounds for closures and proof blocks described above; `scripts/verify` has to hand Verus the dependencies itself. |
| **D. A proc-macro crate of pathos's own** that erases the attributes. | One entry, a workspace member with no dependencies. | Unchanged. | Would remove the `cfg_attr` noise and the closure workaround. A change to `Cargo.lock`, though not a third-party one. |
| **E. A verified copy** kept equal to the shipped code by a check. | Unchanged. | Unchanged. | Free choice of syntax, but two copies, and the check that they are equal becomes part of what is trusted. Not needed: C works. |

C leaves everything as it is and was enough for this spike. If verification
goes further, D is the cheapest improvement and A the most comfortable.

One constraint comes with any option: pathos-term must compile with the
Rust version Verus is built on. Today that is the same as stable; when
stable moves ahead, the verified crates cannot use newer features until
Verus follows.

## An estimate for the evaluator, matching and step checking

These numbers come from one spike and are rough.

**What this spike cost.** About 940 lines of code took 1,900 lines of
specification and proof and twenty small rewrites, in one long working
session. The hard parts were finding out what Verus accepts, and the
store's invariant. A second piece of the same kind would go faster.

**The three parts are of a different kind.** The store and the literal
operators have obvious specifications: a hash-consed store is an injective
map to trees, and `eo::add` is addition. For the checker the specification
is the hard part:

- **There is no formal semantics of Eunoia to verify against.** "Every step
  follows from its premises by the rules of the signature" needs a
  definition of what a signature's rules mean: program evaluation, the type
  system, the roughly fifty `eo::` operators, attributes such as
  `:right-assoc-nil`. Ethos's manual describes them in prose. Writing them
  as Verus specification functions is writing a second, mathematical
  checker, and the theorem would be that pathos agrees with it.
- **Programs need not terminate**, so the evaluator's specification cannot
  be a plain recursive function. It would be a relation, or a function with
  a step bound, and the theorem "if `evaluate` returns `r`, the semantics
  allows `r`".
- **The code is iterative** (design decision 8). `evaluate` and typing run
  on explicit stacks, and the proof must relate a stack of frames to a
  recursive definition. That is the standard hard case, and `evaluate` is
  one function of about 200 lines.

| Part | Code | Panic-freedom and valid handles only | Agreement with a written semantics |
| --- | --- | --- | --- |
| Matching (`match_terms` in `typing.rs`, and the code that calls it for programs and rules) | about 200 lines | 400 to 600 lines | 800 to 1,200. The statement is clean: if matching succeeds, the substitution applied to the pattern gives the term. The injective tree view from this spike is what it needs. |
| The evaluator (`eval.rs`) | 985 lines | 2,500 to 3,500 lines | 8,000 to 12,000, plus the semantics itself, 2,000 to 3,000 lines. List operators and the explicit stack are most of it. |
| Step checking (`step.rs`, `typing.rs`, `build.rs`, `checker.rs`) | about 1,500 lines | 3,000 to 4,000 lines | 6,000 to 10,000. Depends on the evaluator and on a formal type system. |

In effort: the middle column for all three is perhaps four to six times this
spike. The right column is fifteen to twenty-five times, and most of the
risk is not Verus but agreeing on the semantics with the Ethos developers.

**What would get in the way**, from what this spike met:

- `pathos-check` uses hash maps, trait objects (the plugin), string
  formatting for error messages and many closures. Each needs a
  specification from Verus's library, a rewrite, or a trusted wrapper.
- The parser and `pathos-elab` build the terms the checker works on. Unless
  they are verified too, "pathos is sound" would mean "the checker is sound
  on the terms the parser built".
- Long functions with a large invariant strain the solver: `mk`, 110 lines,
  needed twenty times the default budget. `evaluate` would have to be split
  for verification.
- Verus releases weekly, the attribute syntax used here is its younger one,
  and each release is tied to one Rust version. Proofs will need upkeep.

**A cheaper next step**, if one is wanted: matching. It is small, its
specification needs no semantics of Eunoia, and it builds directly on the
store's view. It would show whether the explicit-stack style can be
verified at a reasonable cost before anything is committed to the
evaluator.

## Gates

After the changes, on this machine:

- `scripts/verify`: 165 verified, 0 errors.
- `scripts/full-check --quick`: every step passes. `tests` 230 of 230 agree
  with Ethos, `proofs` 400 of 400, `large` 43 of 43, `cli` 3,192 of 3,192,
  `snapshot` 6,300 of 6,300 (and its three proof runs, 400 each), `bignum` 7
  of 7, and `fuzz` has no finding that still differs. These are the numbers
  from before the milestone.
- `cargo fmt --check`, `cargo clippy --all-targets -- -D warnings` and
  `cargo test` in debug and release builds pass. One test was added
  (`compound_kinds_have_different_tags`).
- `Cargo.lock` is unchanged. `scripts/unsafe-reach` finds the same 17
  `unsafe` lines of dependencies in the binaries as before; three counts of
  lines that are not `unsafe` moved by a few
  ([dependencies.md](dependencies.md) has the new numbers).
- Speed: the five slowest proofs of the `large` gate, timed twice each
  before and after, one at a time: 331 s before and 328 s after for the
  slowest, and within 0.1 s of each other for the other four (123 s, 34 s,
  11 s, 10 s).

## For Daniel

1. **The dependency option.** The spike uses C. Nothing needs agreeing
   unless you prefer A or D for further work.
2. **The rewrites.** They are in shipped code. The ones that are more than
   cosmetic: `euclidean_qr` makes two temporaries; the growth test of the
   hash tables multiplies in `u128`; `mk_count` wraps. If any of them is
   unwelcome, the alternative is to mark that function trusted.
3. **Whether to go further**, and if so whether matching is the right next
   piece.
4. **The trusted list.** In particular the `malachite` wrappers: they are
   where a mistake in a specification would go unnoticed. The tests of
   `num.rs` check a few values of each.
5. **`docs/panics.md`** still gives line numbers from before this milestone
   for `pathos-term`; a note there says what changed. Verus now proves the
   "Safe" rows of the store (outside snapshots), of `bitvec.rs` and of
   `Lit::evaluate`.

## Milestone 18: matching cannot panic

### Summary

- **Matching is proved free of panics.** `match_terms` and `match_cases`
  (the loop that finds the case of a program matching its arguments) cannot
  panic, and every term they read, push or bind is a term of the store.
  Verus checks 2 functions in `pathos-check` with no errors in 2 seconds, on
  top of the 165 items of `pathos-term`.
- **It was much cheaper than estimated**: 49 lines of specification and 5 of
  proof for 83 lines of code, against the 400 to 600 lines I estimated. The
  store's contracts from milestone 17 did the work.
- **One precondition is not guaranteed by anything Verus checks:** that a
  program's cases are pairs. It is the "crafted snapshot" case that
  [panics.md](panics.md) already lists as open.
- **Rule steps are covered through programs.** A rule's premises, `:args`
  and conclusion are matched by the same two functions; the code in
  `check_step` that assembles them is not verified.
- **Correctness is not proved.** What it would state, and the lemmas it
  needs from the store, are below. One of them, about the `is_ground` flag,
  is not in the store's invariant yet.
- **Verifying a second crate works.** `scripts/verify` has Verus export
  what it proved about `pathos-term` and checks `pathos-check` against it.

### What was verified

The two functions are in
[matching.rs](../crates/pathos-check/src/matching.rs), a new module. They
take the term store, not the checker: matching reads nothing else. The
checker's `match_terms` method and `evaluate_program_internal` call them.

| Function | Requires | Proved |
| --- | --- | --- |
| `match_terms(s, a, b, ctx, visited)` | The store's invariant; `a` and `b` are terms of the store; every key and value of `ctx` is one. | No panic. Every pair on the work stack, and every key and value of `ctx` afterwards, is a term of the store. A binding already in `ctx` is still there, to the same term. |
| `match_cases(s, prog, children, new_ctx)` | The same, for `prog` and each of `children`; and `is_program(s, prog)`: every child of `prog` has at least two children. | No panic. `new_ctx` holds terms of the store. The body or the pattern returned is a term of the store. |

`match_cases` returns one of three answers: the body of the first matching
case, the pattern of a case with the wrong number of arguments, or no case.
The warning for the second, which formats terms, stays in the checker.

Where the three kinds of matching in the milestone go through this code:

- **A program's cases:** `evaluate_program_internal` calls `match_cases`.
- **A rule's premises, `:args` and conclusion:** `check_step` puts them in
  one argument list and applies the rule's program to it, so they are
  matched by `match_cases` too. `check_step` itself builds terms and
  evaluates, and is left for the evaluator's milestone.
- **Argument types against a function type** (`get_type_app`) and **the
  type of a nil terminator** (`evaluate_nil`) call `match_terms`. Their own
  code is not verified.

Seven deliberate faults are each caught: dropping the `is_program`
requirement, dropping the comparison of the numbers of children, running
the argument loop one too far, dropping the requirement that `b` is a term
of the store, reading a case's third child, dropping the arity check, and
`assert(false)` at the end of `match_terms`.

### The preconditions, and who meets them

The callers are not verified, so these are obligations on them:

- **Terms of the store, and a context of them.** Every caller passes terms
  it got from the store, and a context that is new or was filled by
  matching.
- **`is_program`.** The parser builds a program only from pairs of a
  pattern and a body. A snapshot is not checked for it: a forged snapshot
  whose program symbol points at another kind of term makes
  `child(case, 0)` panic. This is row "Crafted snapshot" of `eval.rs` in
  [panics.md](panics.md), and the first open question of
  [evidence.md](evidence.md). Verus turns it from a note into a stated
  precondition. Closing it means checking the shape when a snapshot is
  read, or in `match_cases`.

### What is assumed

One new statement: the derived order of `Term` is a total order that
agrees with equality (`axiom_terms_are_ordered`), which Verus's model of
`BTreeMap` asks for. Everything else is from milestone 17's list, plus
Verus's own specifications of `BTreeMap`, `HashSet` and `Vec`.

Termination of the loop of `match_terms` is not proved.

### Rust features

Accepted as written: `while let Some((x, y)) = stack.pop()`, `BTreeMap::get`
and `insert`, `HashSet::insert`, `continue`, `vec![...]`, and an enum
defined outside `verus!`.

Rewritten, with the same behaviour:

| Construct | Problem | Now |
| --- | --- | --- |
| `for (&cx, &cy) in s.children(x).iter().zip(s.children(y))` | A loop over a `zip` needs an invariant written against Verus's model of the zipped iterator. | A loop over an index into the two lists. |
| `children.iter().enumerate().skip(1)` | The same, for `enumerate` and `skip`. | `for j in 1..nargs`. Clippy asks for the iterator back; one `#[allow]`. |
| The body of the loop in `evaluate_program_internal` | It warns, through the checker, in the middle of matching. | `match_cases` returns `BadArity` and the caller warns. |

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `matching.rs` | 83 | 49 | 5 |

The code replaces 56 lines in `typing.rs` and `eval.rs`, which keep 8 lines that call it; the rest of the difference is the result type and the function signatures. Verus takes 1.8
seconds for `pathos-check`; `scripts/verify` as a whole takes about 33
seconds.

### Verifying a second crate

Verus is run on `pathos-term` with `--compile --export`, which writes the
compiled crate and a file of what was proved about it, and then on
`pathos-check` with `--extern` and `--import` pointing at those. The
specification functions that `pathos-check` uses (`wf`, `has`, `kids`,
`idx`) were already public. `scripts/verify` checks a minimum number of
verified items for each crate.

### What correctness would say

Not proved; this is the statement and what it needs.

**Instantiation.** For a store `s`, a substitution `σ` (the context) and a
term `x`, `inst(s, σ, x)` is a tree: if `x` is a parameter bound in `σ`,
the tree of the term it is bound to; if `x` is compound, its kind with the
instantiations of its children; otherwise the tree of `x`.

**The statement for `match_terms`.** If `match_terms(s, a, b, ctx,
visited)` returns true, then `inst(s, ctx', a) == s.tree(b)` for the
context `ctx'` it leaves, provided that for every pair `(x, y)` in
`visited` beforehand, `inst(s, ctx, x) == s.tree(y)`. That proviso is what
sharing `visited` between calls means, and it fails after a call that
returned false: a caller must not reuse `visited` then. Both callers that
share it stop at the first false.

**Completeness**, if wanted: if it returns false, no extension of `ctx`
instantiates `a` to the tree of `b`.

**For `match_cases`:** if it returns the body of case `i`, the patterns of
case `i` instantiated by `new_ctx` are the trees of the arguments, and (with
completeness) no earlier case matches.

Three things pathos does that the statement has to respect, because the
specification states what the code does: types of a parameter and the term
bound to it are not compared; equal non-ground terms are still traversed;
a non-ground term without children that is not a parameter (`eo::?`) never
matches.

**Lemmas needed from the store:**

| Lemma | Status |
| --- | --- |
| Two terms with the same tree are the same term (so `x == y` on handles decides equality of trees). | Proved: `theorem_same_tree_same_term`. |
| The tree of a compound term is its kind and the trees of its children. | True by definition, but `tree` is closed: needs a public lemma. Small. |
| `kind`, `children` and `num_children` return what the tree is made of. | Proved: their `ensures`. |
| **`is_ground(x)` holds exactly when no parameter and no `eo::?` occurs in `x`**, so that a ground pattern instantiates to itself. | **Missing.** The flags are not in the store's invariant: `mk` computes them from the children's, and nothing is proved about them. Adding it touches `mk`, `mk_symbol` and `new`. |
| A term of kind `PARAM` is a symbol, with no children. | Follows from `kind_of`; needs stating. |
| Instantiation does not change when the context grows, for a term whose parameters were all bound. | New, about `inst`; by induction on the term. |

It also needs Verus's model of `HashSet` for `visited`, which asks that the
derived `Hash` of `Term` agree with its equality (one more assumption), and
a loop invariant relating the work stack to the pairs still to be matched.

My estimate: 100 to 150 lines of specification and 300 to 500 of proof,
most of it the loop invariant and the flag lemma.

### The estimate, updated

The estimate of milestone 17 for panic freedom of matching was 400 to 600
lines; it took 54. Two reasons, and they cut both ways for what is left:

- **The store's contracts carry over.** Once `children` promises terms of
  the store, code that only reads the store needs almost no proof. The
  evaluator reads the store in the same way for much of its length.
- **Matching did not need the checker.** `Checker` holds hash maps, a
  plugin behind a trait object, a boxed closure and statistics. Matching
  was moved out of it. The evaluator cannot be: it reads attributes, counts
  programs, warns and calls the plugin. Getting Verus to accept `Checker`
  at all, or splitting what the evaluator needs from the rest, is the
  first cost of the next milestone and is still unmeasured.

So I would lower the panic-freedom column of milestone 17's table to
roughly a third for code that only reads the store, and leave it as it was
for code that builds terms and goes through `Checker`. The right-hand
column, agreement with a semantics, is unchanged.

### Gates

- `scripts/verify`: `pathos_term` 165 verified, 0 errors; `pathos_check` 2
  verified, 0 errors.
- `scripts/full-check --quick`: every step passes, with the numbers of
  milestone 17: `tests` 230 of 230, `proofs` 400 of 400, `large` 43 of 43,
  `cli` 3,192 of 3,192, `snapshot` 6,300 of 6,300, `bignum` 7 of 7, and
  `fuzz` has no finding that still differs.
- Formatting, Clippy with warnings as errors, and the tests in debug and
  release builds pass.
- Speed: the `large` gate, which matches more than anything else, took
  350.6 s against 350.1 s before the change.
- `Cargo.lock` is unchanged; no dependency was added. `scripts/unsafe-reach`
  gives the line counts of milestone 17.
- `.github/workflows/ci.yml` now also runs on pushes to `verus`.

## Milestone 19: matching is correct

### Summary

- **A match found is a match.** When `match_terms` returns true, the
  context it leaves, applied to the pattern as a substitution, gives the
  tree of the term. When `match_cases` returns a body, that holds for every
  argument of the case it chose. Verus checks 15 items in `pathos-check`
  and 178 in `pathos-term`, with no errors.
- **`match_terms` is proved to end.** Milestone 18 listed that as not
  proved; it is no longer on the list.
- **The store now says what `is_ground` means:** it holds exactly for terms
  whose tree has no parameter and no `eo::?`.
- **Ethos's quirks are in the specification**, as postconditions: types are
  not compared, a ground pattern matches only itself, and `eo::?` as a
  pattern matches nothing.
- **Cost:** about 140 lines of specification and 360 of proof, with no
  change to the code that runs. My estimate was 100 to 150 and 300 to 500.
- **Two new assumptions**, both about derived traits of `Term`.
- **Writing the precondition down found a quirk of Ethos's type checking**
  that pathos reproduces: a quoted argument rebinds a parameter that an
  earlier argument bound. See "What the callers must do".
- **Completeness is not proved:** that when matching fails, no match
  exists.

### The statement

All of this is in [matching.rs](../crates/pathos-check/src/matching.rs).

**Instantiation.** `inst(s, ctx, x)` is the tree of the pattern `x` with
the substitution `ctx` applied: a parameter that `ctx` binds becomes the
tree of the term it is bound to; a term with children is rebuilt, with its
own kind, from its instantiated children; anything else is its own tree.

**For `match_terms(s, a, b, ctx, visited)`**, with `ctx'` the context
afterwards:

| Postcondition | In words |
| --- | --- |
| `r ==> inst(s, ctx', a) == s.tree(b)` | A match found is a match. |
| `tree_is_ground(s.tree(a)) ==> r == (a == b)` | A ground pattern matches exactly itself. Because the store's view is injective, that is the same as: exactly the term with the same tree. |
| `!ground(a) && a has no children && a is not a parameter ==> !r` | `eo::?`, the only such term, matches nothing. |
| `ctx_kept(ctx, ctx')` | Bindings are only added. |

Types do not appear: `inst` is about trees, and the documentation of
`inst` and of `match_terms` says that the type of a parameter and the type
of what it is bound to are not compared, as in Ethos.

**For `match_cases`:** if it returns `Body(t)`, there is a case `i` of the
program such that `t` is its body, its pattern has as many children as
there are arguments, and for every argument `m` from 1 on,
`inst(s, new_ctx, pattern_child[m]) == s.tree(children[m])`.

### How it is proved

- **What the loop keeps true.** Every pair `(x, y)` in `visited` is *good*:
  `x` is not ground, and either `x` is a parameter bound to `y`, or `x` and
  `y` have the same kind and number of children and each pair of their
  children is on the stack, or in `visited`, or ground and equal. Each of
  the five ways through the loop body keeps this (`lemma_closed_step`).
- **When the stack is empty**, a good pair is a match, by induction on the
  pattern (`lemma_inst`). This is where the store's lemmas are used: the
  tree of a compound term is its kind and its children's trees, a ground
  pattern instantiates to itself, and a parameter has no children.
- **Sharing `visited` between calls** is the precondition `closed`: the
  pairs already in `visited` are good under the context passed in. After a
  successful call they still are, so the next call may share it.
- **Across the arguments of a case**, each argument has its own `visited`,
  and a pair that was matched stays matched when later arguments add
  bindings (`lemma_matched_kept`).

### Termination

The measure is the sum, over the stack, of the size of each pattern's
tree, counting a shared subterm each time it occurs. A turn of the loop
takes one pattern off and puts at most its children on, whose sizes add up
to one less. The measure is a mathematical natural number, so it does not
matter that it can be astronomically large for a term with much sharing;
`visited` only makes the loop end sooner.

A variant that pushes a pair back is rejected with "decreases not
satisfied".

### What was added to the store

In [store.rs](../crates/pathos-term/src/store.rs):

- **The flag invariant.** `wf` now includes, for every term: a parameter
  and `eo::?` are flagged not ground, other atoms ground, and a compound
  term is flagged not ground exactly when one of its children is. `mk`,
  `mk_symbol`, `mk_lit` and `new` are proved to keep it; in `mk` this is an
  invariant of the loop that ors the children's flags, proved in the
  solver's bit-vector mode.
- **`tree_is_ground`**, a predicate on trees, and the lemma that the flag
  agrees with it. `TermStore::is_ground` now ensures
  `r == tree_is_ground(self.tree(t))`.
- **Three public lemmas** for other crates, since `tree` is closed:
  children are terms made earlier and a term with children is compound
  (`lemma_children`); the tree of a compound term (`lemma_tree_compound`);
  the tree of a parameter (`lemma_tree_param`).

The snapshot reader is still not verified. It computes the flags as `mk`
does, and is assumed to give a store for which the invariant, now with the
flags, holds.

### What the callers must do

The callers are not verified. Besides milestone 18's preconditions,
`match_terms` now requires `closed`: the pairs in `visited` were matched
under the context passed in. Three callers:

- `match_cases` passes a new `visited` for each argument. Verified.
- `evaluate_nil` passes a new `visited` and a new context. Holds trivially.
- `get_type_app` shares `visited` and the context over the arguments of an
  application, and stops at the first failure. That is the intended use.
  **But for an argument whose type is `(eo::quote x)` it binds `x` with
  `ctx.insert`, which replaces a binding `x` already had.** If an earlier
  argument's type mentioned `x` and matching bound it, the pairs in
  `visited` were matched under the old binding, and the precondition does
  not hold for the arguments after.

  I probed it. With `:signature ((BitVec n) (eo::quote n)) (BitVec n)`,
  the single case `((p x 0) x)` and `a` of type `(BitVec 5)`, the
  application `(p a 7)` matches no case, so it stays as it is, and it
  type-checks with type `(BitVec 7)`, in Ethos and in pathos alike: the
  second argument rebinds `n` and nothing notices that the first
  disagreed. It shows only on an application that does not evaluate; one
  that does is replaced by its value before it is typed. pathos
  reproduces Ethos here, so no gate differs; it is recorded in
  [ethos-differences.md](ethos-differences.md) and reported as
  [cvc5/ethos#269](https://github.com/cvc5/ethos/issues/269).
  Whether it lets a wrong proof through depends on the signature. In the
  four program signatures with a quoted argument that a search of cvc5's
  signature files finds, the quoted parameter is in no other argument's
  type, so it does not arise there; I did not look further than that
  search. `get_type_app` is in scope for the evaluator's milestone, whose
  specification will have to state this.

### What is assumed

New in this milestone:

- The derived `==` of `Term` is equality (as milestone 17 assumed for the
  kinds and for `Lit`).
- The derived `Hash` and `Eq` of a pair of terms agree, which Verus's model
  of `HashSet` asks for (`axiom_term_pairs_are_keys`).

No longer assumed: termination of `match_terms`.

### What had to be rewritten

Nothing in the code that runs. Two things about Verus cost time:

- **A recursive predicate over a sequence of subtrees** (`tree_is_ground`)
  unfolds only when the solver sees the sequence as a field of the tree.
  One lemma, `lemma_ground_node`, spells that out, and everything else uses
  the lemma.
- **A local variable named like a specification function** hides it; the
  predicate is `is_match` because `match_cases` has a variable `matched`.

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `matching.rs` | 84 (was 83) | 151 (was 49) | 208 (was 5) |
| `store.rs` | 687 (unchanged) | 484 (was 443) | 901 (was 743) |

Verus takes 22 to 38 seconds for `pathos-term`, depending on the run, and 3
seconds for `pathos-check`.

Ten deliberate faults are each caught: `assert(false)` after the loop;
dropping the comparison of kinds; dropping the check of an existing
binding; accepting a ground pattern that is not the term; pushing the
children swapped; dropping the test for a parameter; returning a body
without a match; returning the pattern as the body; inverting the ground
test; and the non-terminating variant above.

### Not proved

- **Completeness:** that when `match_terms` returns false no extension of
  the context matches, and that `match_cases` returns the first case that
  matches. It needs the converse direction of the invariant.
- **That `visited` is only an optimization**, that is, that the result is
  the same without it.

### The estimate, updated

This milestone came in on its estimate, and the proof is of the kind the
evaluator will need: an explicit stack, a set of visited pairs, and an
invariant that says what is still owed. For `match_terms`, 40 lines of
loop took about 350 lines of specification and proof. `evaluate` has five
times the loop and builds terms as it goes, so on this evidence its
agreement with a written semantics is in the range milestone 17 gave
(8,000 to 12,000 lines), not below it.

### Gates

- `scripts/verify`: `pathos_term` 178 verified, 0 errors; `pathos_check` 15
  verified, 0 errors.
- `scripts/full-check --quick`: every step passes, with the numbers of
  milestone 18: `tests` 230 of 230, `proofs` 400 of 400, `large` 43 of 43
  (344 s, against 351 s), `cli` 3,192 of 3,192, `snapshot` 6,300 of 6,300,
  `bignum` 7 of 7, and `fuzz` has no finding that still differs.
- Formatting, Clippy with warnings as errors, and the tests in debug and
  release builds pass.
- `Cargo.lock` is unchanged; no dependency was added. The code that runs
  did not change (every added line is behind `cfg(verus_keep_ghost)` or
  inside a proof block), so the dependency trace was not rerun.

## Milestone 20: the snapshot reader cannot panic

### Summary

- **The store's reader is proved.** `TermStore::read_from`, `Lit::read_from`
  and the codec's `Reader` cannot panic on any bytes, and a store that
  `read_from` returns satisfies the whole invariant of milestones 17 and
  19. Verus checks 209 items in `pathos-term` and 18 in `pathos-check`,
  with no errors.
- **How:** the reader no longer copies a store out of the file. It builds
  the store again with `mk_symbol`, `mk_lit` and `mk`, which are already
  verified, and rejects the file if a term does not come out where the
  file has it.
- **All 23 "crafted snapshot" rows of [panics.md](panics.md) are closed.**
  The table below says, for each shape the checker relies on, whether it
  is checked by the reader or proved.
- **A snapshot pathos wrote reads as before.** The snapshot of cvc5's
  signature is byte for byte the same file, is still used, and loads in
  17.2 ms against 16.7 ms.
- **The first question for the Ethos developers can be withdrawn** as far
  as it is about panics; see the end of this section for the two
  conditions.
- **The checker's own tables are checked by ordinary code, not by Verus.**
  Verus reaches the functions that take the store alone; the image reader
  around them holds hash maps of the `Checker`.
- **The generic fuzzer is weak evidence here**: it found nothing on the
  old code either. The stronger evidence is the tests that forge each
  state.

### What Verus proves

In `pathos-term`:

| Function | Proved |
| --- | --- |
| `Reader::bytes`, `u8`, `bool`, `u32`, `u64`, `len`, `str`, `new`, `is_at_end`, `remaining` | No panic. `bytes(n)` gives `n` bytes; `len` gives a count that fits 32 bits. |
| `Lit::read_from` | No panic; a bit-vector it returns fits its width. |
| `TermStore::read_from` | No panic; a store it returns satisfies `wf`: valid handles, the tables, no two terms alike (so the injective tree view), and the flags. |
| `TermStore::term_with_id` | The term returned is a term of the store. |
| `NodeKind::takes` | Meets its specification. |

In `pathos-check`:

| Function | Proved |
| --- | --- |
| `read_term`, `read_opt_term` | No panic; the term read is a term of the store. |
| `is_program_term` | No panic; if it returns true, the term has the shape `match_cases` requires (`is_program`) and every case's pattern has a head. |

Five deliberate faults in the store's reader are each caught (not
checking that a term came out at its position, that a child range is
inside the pool, that a child is an earlier term, that a cached type is a
term of the store, that there is a name left).

### The reader, rewritten

`read_from` used to fill the store's vectors and tables directly, with its
own copies of the checks `mk` makes. Now, for each term of the file in
turn, it calls the constructor for that kind and requires the handle it
gets to be the next one. A term that is in the file twice, or a store that
is full, gives another handle, and the file is rejected. The tables are
made large enough beforehand, as before, so they do not grow.

The proof is then short: each constructor keeps the invariant, so the loop
does. The reader gained about 60 lines of specification and 30 of proof,
against the 740 lines of proof behind the constructors.

What is accepted is what was accepted before, plus the new checks listed
below, and the store built is the same store: same terms, child pool,
names, values, flags and table layout.

### The shapes the checker relies on

| What the checker relies on | Rows of panics.md | Now |
| --- | --- | --- |
| Every child and cached type is a term of the store; nothing is interned twice; table entries are in range. | (none: the reader checked these) | **Proved**: `read_from` returns a store satisfying `wf`. |
| A `LAMBDA` and a `PARAMETERIZED` term have two children; a `PROOF` and a `QUOTE_TYPE` term one; an `APPLY` and an `APPLY_OPAQUE` term at least one. | 9 | **Checked** by `read_from` with `NodeKind::takes`, for every term. Not an invariant of the store: `mk` builds any number of children, and the parser is what keeps to these. |
| A program is a list of cases, each a pair whose first element has a head (`is_program` of milestones 18 and 19). | 3 | **Checked** by the checker's `read_image` with `is_program_term`, which Verus proves gives `is_program`. |
| A builtin's kind is a compound kind, which `mk` takes. | 2 | **Checked** by `read_image`. |
| The builtin terms the checker holds handles to are terms of the store read, and the same terms. | 2 (11 places) | **Checked** by `read_image`: the store read must begin with the same terms as the checker's own, up to the last builtin one (`same_first_terms`). |
| A name or an output line is text with one character for a byte. | 3 | **Checked** by `Reader::str`, which every string goes through. |
| The counters do not overflow. | 4 | **Cannot fail**: `hash_counter`, the rule and program counts and the count of terms made per step now wrap, as `mk_count` has since milestone 17. |

The last row includes one place the inventory did not list: the number of
terms made during a step is a difference of `mk_count` values, which could
underflow in a debug build after the counter wrapped. It wraps now too.

### What is checked by ordinary code, and its tests

The checker's `read_image` and the state's `read_image` build hash maps of
`AppInfo`, names and lists. Verus is not run on them, because that needs
the `Checker`. They already returned `None` on anything they could not
read; the new checks are in the table above. Tests:

- `pathos-term`: a store with a term of the wrong shape is rejected, for
  each kind and number of children; a name that is not Latin-1 is rejected.
- `pathos-check`: a builtin of an atomic kind; a program that is not a
  list of cases, in three ways; a store without the builtin terms; a store
  with other terms in their place; counters at their maximum.
- `pathos-elab`, end to end: six states that no signature gives are forged
  through the library, written as snapshots and offered to a run of a
  proof that uses the forged name. All six snapshots are ignored. On the
  code before this milestone none was rejected: four were used without a
  panic by the proof I wrote for them, and two of the runs panicked (an
  application without a head, in `typing.rs`; a builtin of an atomic kind,
  in `store.rs`).
- A snapshot with one more ordinary term is still used.

### Fuzzing

The reviewer's `snapfuzz.py` mutates a snapshot (bit flips, edge bytes,
32-bit fields set to small or extreme values, swapped bytes), recomputes
the checksum, and runs pathos with it on a proof. The snapshot was that of
cvc5's signature (660 kB), with four proofs of the corpus.

| Build | Runs | Panics, crashes, timeouts |
| --- | --- | --- |
| This milestone, release | 60,000 (four seeds), then 12,000 on the final code | 0 |
| This milestone, debug | 10,000 (two seeds), then 2,000 on the final code | 0 |
| Before this milestone, release | 3,000 | 0 |
| Before this milestone, debug | 1,500 | 0 |

So 84,000 forged snapshots with a valid checksum, and nothing. But the
last two rows say how much that is worth: the same fuzzer finds nothing
on the code that is known to panic, because a random change almost never
produces the particular states the 23 rows need. It shows that the new
checks do not make the reader fall over on damaged input. That the 23
states are rejected is shown by the tests above, which forge them on
purpose. The first 70,000 runs were on a build without the last two
checks (the builtin terms being the same terms, and the per-step count);
the 14,000 after are on the final code.


### What is assumed

New in this milestone:

- `SymbolKind::from_index`, `LitKind::from_index`, `NodeKind::from_index`
  and `EvalOp::from_index` (a lookup in a constant table) do not panic.
- `latin1_text` (`str::from_utf8` and a scan of the characters) does not
  panic.
- As before, `Integer::parse` and `Rational::parse` do not panic. The
  reader hands them strings from the file, so this matters more than it
  did; milestone 14 ran them on random strings.

Not proved, and not needed for safety:

- **That reading gives back what was written.** The round trip is tested,
  not proved. One sign of it: dropping the check that the first four terms
  are `Type`, `Bool`, `eo::?` and the null term changes nothing for Verus,
  because the store is built with them whatever the file says.
- **That the checker's tables make sense**, beyond the shapes above.

### What had to be rewritten

| Construct | Problem | Now |
| --- | --- | --- |
| `u32::from_le_bytes(b.try_into().ok()?)` | No specification for either. | The four bytes combined with shifts. |
| `(cond).then_some(n)`, `(cond).then(\|\| ...)`, `.map(Some)` | No specification; a constructor as a function. | `if`. |
| `*SymbolKind::ALL.get(i)?` and the like | Associated constant tables are not supported. | `from_index` functions, trusted. |
| `raw.iter().enumerate()`, closures `bits` and `earlier` | As in earlier milestones. | Indexed loops; functions `table_bits` and `Term::earlier`. |
| `Vec::reserve` on the store's vectors before filling them | It made the invariant hard to carry across, for no behaviour. | Dropped; the vectors grow as they are filled. |
| One long function | The solver ran out of budget. | Three: `read_from`, `rebuild` (one term) and `set_cached_types`. |

A proof in `match_cases` that passed in milestone 19 stopped passing when
unrelated definitions were added to the file, and needed its last step
spelled out. This is the instability the estimate in milestone 17 warned
of; it cost a quarter of an hour.

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `store.rs` | 713 (was 687) | 548 (was 484) | 935 (was 901) |
| `codec.rs` | 104 (was 88) | 6 | 0 |
| `kind.rs` | 453 (was 425) | 72 (was 52) | 0 |
| `matching.rs` | 93 (was 84) | 164 (was 151) | 218 (was 208) |
| `snapshot.rs` (`pathos-check`) | 296 (was 271) | 9 | 0 |

Verus takes about 30 seconds for `pathos-term` on an idle machine and 3
for `pathos-check`.

### Can the first question be withdrawn?

The question on the evidence page is whether a snapshot is trusted like
the signature it was made from, because a forged one "can also hold a
term of a shape no signature produces, on which the checker stops with a
panic", in 23 places.

**Yes, as far as it is about panics**, on two conditions:

1. **The inventory was complete.** The 23 rows are closed. That closes the
   matter if milestone 14's inventory found every place a forged state
   could reach, which is what it set out to do; this milestone found one
   more such place itself (the count of terms per step). For the store,
   the answer no longer rests on the inventory: Verus proves it. For the
   checker's tables it still does.
2. **This work is on `main`.** It is on the `verus` branch, which does not
   merge into `main`. The checks and the rewritten reader do not depend on
   Verus and could be brought to `main` on their own.

What stays is not a question for the Ethos developers: a forged snapshot
can hold a rule that proves anything, exactly as an edited signature file
can. A snapshot has to be kept as safe as the signature; it no longer has
to be trusted not to crash the checker.

I did not edit `docs/evidence.md`: the question is Daniel's to withdraw.

### Gates

- `scripts/verify`: `pathos_term` 209 verified, 0 errors; `pathos_check` 18
  verified, 0 errors.
- `scripts/full-check --quick`: every step passes: `tests` 230 of 230,
  `proofs` 400 of 400, `large` 43 of 43 (351 s, as before), `cli` 3,192 of
  3,192, `snapshot` 6,300 of 6,300 and its three proof runs of 400 each,
  `bignum` 7 of 7, and `fuzz` has no finding that still differs.
- Formatting, Clippy with warnings as errors, and the tests in debug and
  release builds pass. Ten tests were added.
- `Cargo.lock` is unchanged; no dependency was added. `scripts/unsafe-reach`
  finds the same 17 `unsafe` lines of dependencies.
- The snapshot of cvc5's signature written by this code is identical, byte
  for byte, to the one written before, and a run with it takes 17.2 ms
  against 16.7 ms before and 37 ms without a snapshot.
