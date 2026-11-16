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
- [Milestone 21: the evaluator's operators cannot panic](#milestone-21-the-evaluators-operators-cannot-panic)
  (the design that was reviewed first is in
  [verus-eval-design.md](verus-eval-design.md))
- [Milestone 22: `evaluate` cannot panic](#milestone-22-evaluate-cannot-panic)
- [Milestone 23: typing cannot panic](#milestone-23-typing-cannot-panic)
- [Milestone 24: term building and step checking cannot panic](#milestone-24-term-building-and-step-checking-cannot-panic)
- [Milestones 17 to 24: what is proved, trusted and not covered](#milestones-17-to-24-what-is-proved-trusted-and-not-covered)

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

Verus takes about 43 seconds for `pathos-term` (it was 22 after milestone
19) and 3 for `pathos-check`.

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

## Milestone 21: the evaluator's operators cannot panic

### Summary

- **Scope, after the design review.** The design
  ([verus-eval-design.md](verus-eval-design.md)) was reviewed before any
  proof, and the milestone was cut in two. This one is everything in
  `eval.rs` except `evaluate`: program application, the `eo::` operators'
  entry point, `eo::nil`, the n-ary helpers, the list operators and the
  datatype operators. Milestone 22 is `evaluate`, its stack of frames and
  its two `unreachable!`.
- **Proved**: none of these 34 functions can panic, each keeps the
  checker's invariant, and every term one of them reads, builds or
  returns is a term of the store. Verus checks 215 items in `pathos-term`
  and 70 in `pathos-check` (18 before), with no errors.
- **The store now refuses a term of the wrong shape.** The check in
  `TermStore::mk` was measured, as asked: between -0.1% and +0.2% in instructions, and no slower in time on any corpus. It is kept. So
  "an application has a head" is part of the store's proved invariant,
  not an assumption about every builder of terms. **It is on this branch
  only**; whether it goes to `main` is under "For Daniel".
- **`evaluate` is trusted for one milestone**, and typing and the plugin
  for longer. Typing calls `evaluate`, so the proof assumes, one level
  down, what it proves; see "The circularity".
- **Behaviour is unchanged**: every gate agrees with Ethos, the order of
  warnings and statistics included (the `options` gate, which runs
  `--stats`, was run as well as the quick gates).
- **Cost**: about 700 lines of specification and proof for the 730 lines
  of the file after `evaluate`, against the 1,000 to 1,700 the design estimated for these parts.
  The estimate for `evaluate` stands.

### What Verus proves

Every function below is proved not to panic and to end, given that the
trusted functions it calls return. Each requires the checker's invariant
and that its arguments are terms of the store; each ensures the invariant
again, that the store still has every term it had, with the same kind and
children, and that a term returned is a term of the store.

| Functions | Also needed, or also proved |
| --- | --- |
| `evaluate_program_app`, `evaluate_program_internal` | Require the head: `args` is not empty. The context filled binds terms of the store. The program found has the shape `match_cases` requires, from the invariant. |
| `evaluate_literal_op`, `evaluate_literal_op_internal` | Require three arguments for `eo::ite`. The literals handed to `Lit::evaluate` are well formed, from the store's invariant. |
| `evaluate_nil` | `child(nil, 1)` of a parameterized terminator is in range, from the store's invariant. |
| `nary_step`, `get_nary_children`, `is_nary_list`, `get_nary_nth_tail`, `prepend_nary_children` | The loops over a list end: the tail is an earlier term. A list has at most 2^32 - 1 elements. |
| `evaluate_dt_constructors` | The loop to the head of an application ends. |
| `evaluate_list_op`, `evaluate_list_op_with`, `evaluate_list_singleton_intro` | `child(op, 1)` of a parameterized operator is in range. |
| `list_cons_or_concat`, `list_repeat`, `list_length`, `list_nth`, `list_find`, `list_erase`, `list_rev`, `list_setof`, `list_compare`, `list_diff_or_inter`, `list_singleton_elim` | The counts of `eo::list_meq` and the others cannot overflow, and the count that `eo::list_diff` decrements is at least one. |
| `compute_constructor_term` | Requires the head. |
| `missing_argument`, `mk_usize`, `all_ground`, `any_argument_evaluatable`, `all_literals`, `position`, `count_terms`, `counts_cover` | Helpers. |
| In `checker.rs`: `warn`, `mk_type`, `mk_true`, `mk_false`, `mk_bool`, `mk_list_cons`, `mk_numeral`, `app_info`, `attribute_kind`, `get_program`, `get_hash` | `get_program` returns a term with the shape of a program. |

Three deliberate faults are each caught: not using the shape of a
parameterized term before `child(nil, 1)`, testing for the wrong number of
children before `children[1]`, and removing a count at 2 instead of 1.

### The checker's invariant

`Checker::wf`, in `checker.rs`:

- the store's invariant (`TermStore::wf`);
- the builtin terms (`true`, `false`, `eo::self`, the list type and its
  constructors, the proof type, and -1 once it is made) are terms of the
  store;
- for every symbol with attributes, the term that goes with its attribute
  is a term of the store, and for a program it is a list of cases, each
  with a pattern and a body (what `match_cases` requires).

The verified functions prove that they keep it. The rest of the checker
(the parser, `build.rs`, typing, the snapshot reader) is **trusted** to
keep it. For the program clause that trust is: `define_program` is given a
list of pairs, which the parser builds and, since milestone 20, the
snapshot reader checks.

The store's own invariant gained two clauses, both proved:

- **shapes**: a term has a number of children that its kind can have
  (`NodeKind::takes`; lemma `lemma_shape`);
- **literals**: every literal in the store is well formed, that is, a
  bit-vector fits its width. `mk_lit` now requires it of its argument, and
  `lit` ensures it of its result. The unverified callers of `mk_lit` are
  trusted to pass one; they can only get a bit-vector from the functions
  of `bitvec.rs` (its fields are private), which Verus proves return
  well-formed ones, or for `BitVec::parse` assumes.

### The shape check: the measurement and the decision

The check is one `match` on the kind and a comparison, at the top of
`TermStore::mk`. A term that does not fit is not made: the store records
`Limit::Shape` and returns `eo::?`, as it does when it is full, and the
command ends with `Internal error: a term with a number of children that
its kind cannot have`.

Measured on `main` (9f55eac) with and without the check, same compiler,
release build:

| Corpus | Cases | Instructions | Time, best of several runs |
| --- | --- | --- | --- |
| Ethos's regressions | 230 | +0.16% (290.3 to 290.8 million) | 0.402 s both (best of 3) |
| cvc5 proofs | 400 | -0.11% (105.00 to 104.89 billion); the largest increase on one proof is +0.24% | 19.01 s to 18.93 s, -0.4% (best of 3) |
| Large cvc5 proofs | 43 | not counted (Valgrind would take hours) | 540.1 s to 534.2 s, -1.1% (best of 2) |

The outputs of the two binaries are the same on all 673 cases.

Instructions are counted with Valgrind (`perf` is not permitted on this
machine); they do not depend on what else the machine is doing, so they
are the number to read. The check adds about 0.2% where it shows at all; that the totals on the
proofs come out lower with it is the compiler laying out `mk` differently,
not the check being free. The times agree within their noise.

The `perf` gate itself was also run, on this branch with the check: over
the 629 cases both accept, Ethos takes 1,273 s and pathos 564 s (44%).
`docs/evidence.md` has 587 s for pathos on the same cases without it.

Under the 1% of the decision, so the check is kept, and:

- no input in the gates makes pathos try to build such a term: the outputs
  with and without the check are the same on every case, and every gate
  still agrees with Ethos;
- the snapshot reader's own shape check (milestone 20) is gone: it is the
  store's now;
- two tests that built wrong shapes through `mk` were rewritten: the
  store's test forges the bytes of a snapshot instead, and also tests that
  `mk` refuses; three cases of
  `a_snapshot_with_a_state_no_signature_gives_is_ignored` were dropped,
  because such a state can no longer be built.

### What is trusted

| Function | Contract |
| --- | --- |
| `evaluate` | Keeps the invariant; the store keeps its terms; returns a term of the store. **Until milestone 22.** |
| `type_of` (which is `get_type` without a message) | The same; a type returned is a term of the store. |
| `plugin_evaluate_program` (the plugin's `evaluate_program`) | The same; a term returned is a term of the store, and the context filled binds terms of the store. |
| `list_of` (which is `mk_list`, through `mk_expr`) | The same. |
| `arity_ok` (which is `check_arity`) | None: it returns a `bool`. |
| The nine functions that format a message (`msg_no_program`, ...) | None: they take `&self` and return a `String`. They are trusted not to panic on terms of the store. |
| `Warnings::emit`, `Stats::count_program` | None: each takes only the field it changes, so Verus knows the rest of the checker is as it was. |
| `reverse` | The list has the same terms, in reverse. |

Assumed besides, and new in this milestone: that the derived `Hash` and
`Eq` of term handles agree (`axiom_terms_are_keys`), which Verus's model
of `HashMap` and `HashSet` needs. The same was assumed of pairs of handles
in milestone 18.

The design listed `warn`, `count_program`, `get_program`, `app_info`,
`attribute_kind`, `get_hash` and the `mk_` functions as trusted. They are
verified instead: `AppInfo` turned out to be a type Verus accepts, so the
attribute table is in the invariant, not behind contracts.

#### The circularity

(Milestone 23 verified typing and milestone 24 term building, and this
assumption is gone: of the cycle only the plugin is trusted. See "The
cycle, closed" under milestone 24.)

`type_of` is trusted to keep the invariant and to return a term of the
store. But typing evaluates: `get_type` calls `evaluate`, and `evaluate`
calls the functions proved here. So the proof of, say,
`evaluate_list_op` assumes of the calls it makes into typing what is being
proved of `evaluate_list_op` itself, one level down. This is not a proof by
induction, and nothing here shows that the chain ends: a literal type rule
`(eo::typeof eo::self)` recurses until the stack is full, which
`docs/panics.md` lists under "Stack". The assumption goes away when typing
is verified, and the recursion then needs a measure or stays a stated
exception.

The same holds for the plugin, which is given the checker and may call
anything.

### The preconditions, and who meets them

| Precondition | Met by |
| --- | --- |
| `evaluate_program_app`, `evaluate_program_internal`, `compute_constructor_term`: the list of terms has a head | `build.rs` and `step.rs`, not verified: they pass the children of an application. `evaluate` (milestone 22) will have to prove it. |
| `evaluate_literal_op`, `evaluate_literal_op_internal`: an `eo::ite` has three arguments | `build.rs`, which checks the arity first. `evaluate` handles `eo::ite` itself and does not pass it on; milestone 22 will have to prove that. |
| Every term passed is a term of the store | There is one store, so every `Term` is one of its terms; Verus cannot know that of unverified callers. |

### What had to be rewritten

No behaviour changed. What changed in the code:

- **Two wrapper types**, `Warnings` and `EvalHooks`, around the boxed
  callback and the boxed plugin, which Verus does not accept as fields.
  `Checker::eval_plugin` is no longer a public field: `set_eval_plugin`
  sets it (one caller, in `pathos-elab`).
- **Iterator chains** with closures (`any`, `all`, `position`,
  `filter_map`, `enumerate`, `rev`) are loops, or small functions
  (`all_ground`, `any_argument_evaluatable`, `all_literals`, `position`).
- **`let` in a condition with `&&`** is nested `if`s.
- **`format!`** is not something Verus checks: each message is built in a
  function of its own, called where the message was built, so the order
  of warnings is the same.
- **The hash-map entry API** (`*map.entry(k).or_default() += 1`,
  `get_mut`) is `get` and `insert`: `count_terms`, and the loop of
  `eo::list_diff`. The `for` over a hash map is `counts_cover`.
- **`arg!`** is a macro of the module, and an argument is bound before the
  call that uses it: Verus does not take `self.f(arg!(1))` when `arg!` may
  return through `self`.
- **`evaluate_list_op` is one function per operator.** As one function of
  250 lines it was beyond the solver's budget, at ten times the default
  too. Split, the whole crate takes 5 seconds.
- `count_program` is a method of `Stats`, and `is_list_op` moved within
  `kind.rs`.

Accepted as written, which earlier milestones had not tried: `slice::get`
and `first`, `Option::copied`, `Vec::truncate`, `HashMap` with `get`,
`insert`, `remove`, `len` and `iter`, `HashSet::insert`, `let ... else`,
a `macro_rules!` that returns.

### What differs from the design

- Fewer functions are trusted (above).
- The contracts say that the store **keeps** its terms, with their kinds
  and children (`keeps`), not the stronger `extends` of milestone 19,
  which also keeps literals' values. `keeps` is what panic freedom needs,
  and it composes without a lemma at every call. A proof of correctness
  will want `extends` back.
- The store's invariant gained the clause on literals, which the design
  did not foresee.
- The loops are proved to end. The design expected nothing on
  termination; within these functions it came for one `decreases` clause
  a loop.

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `eval.rs` | 1,101 (was 839) | 388 | 121 |
| `checker.rs` | 284 (was 266) | 81 | 34 |
| `attr.rs`, `stats.rs` | 281 (was 279) | 18 | 0 |
| `store.rs` | 714 (was 713) | 562 (was 548) | 980 (was 935) |

`eval.rs` has 262 more lines of code: the headers of the functions that
`evaluate_list_op` became, the message functions and the helpers.

Verus takes about 36 seconds for `pathos-term` (the milestone 20 report
had 43) and 5 for `pathos-check` (3 before).

### The estimate, updated

| Part | Estimated in the design | Spent, or still estimated |
| --- | --- | --- |
| Making `Checker` visible, the contracts, shapes | 200 to 300 lines | about 190 (spent) |
| The operators and helpers | 300 to 500 | about 510 for both rows (spent) |
| The list operators | 500 to 900 | |
| `evaluate`, the frame stack (milestone 22) | 1,200 to 1,800 | 1,200 to 1,800 (unchanged) |

The operators cost half the estimate because panic freedom asks little of
them: "these are terms of the store" passes through a function almost
unchanged, and the store now gives the shapes. That is not true of
`evaluate`, where the two `unreachable!` need the invariant that says what
each frame still owes, as `match_terms` did at about nine lines a line. I
keep that estimate. Its risk is the solver's budget: a loop of 190 lines
with five kinds of step will need to be cut into functions, as
`evaluate_list_op` was, and the invariant restated at each cut.

For the rest, from the estimate of milestone 19 (unchanged in kind, firmer
in one way): typing and step checking for panic freedom should now cost
like the operators did, about one line of specification and proof a line
of code, since they too mostly pass terms along: 500 to 900 lines for
`typing.rs`, `build.rs` and `step.rs` (about 1,150 lines of code), if
`build.rs`'s desugaring has no invariant of the kind `evaluate` has.
Correctness with a semantics is a different piece of work and I have no
better number for it than milestone 19 gave.

### Gates

- `scripts/verify`: `pathos_term` 215 verified, 0 errors; `pathos_check`
  70 verified, 0 errors; 41 seconds in all.
- `scripts/full-check`, the whole of it and not only `--quick`: every
  step passes. `tests` 230 of 230, `proofs` 400 of 400, `large` 43 of 43,
  `cli` 3,192 of 3,192, `snapshot` 6,300 of 6,300 and its three proof
  runs of 400 each, `options` 6,300 of 6,300, `bignum` 7 of 7, `perf`
  673 of 673, and `fuzz` has no finding that still differs.
- Formatting, Clippy with warnings as errors, and the tests in debug and
  release builds pass. One test was rewritten and three cases of another
  dropped (see the shape check).
- `Cargo.lock` is unchanged; no dependency was added.
- CI has not run on this branch yet: the reviewer pushes.

### For Daniel

1. **The shape check and `main`.** It is on this branch only. Bringing it
   to `main` is four small changes (the check in `mk`, `Limit::Shape` and
   its message, `NodeKind::takes`, the test) and does not depend on Verus.
   It turns a class of possible panics in the whole checker, not only the
   evaluator, into an error message. Nothing was merged.
2. **The message** for a refused term is `Internal error: a term with a
   number of children that its kind cannot have`. It cannot be compared
   with Ethos, which has no such check. No input is known that produces
   it.
3. **Milestone 22** (`evaluate`) is next, with the estimate above.

## Milestone 22: `evaluate` cannot panic

### Summary

- **Proved**: `Checker::evaluate` cannot panic, keeps the checker's
  invariant, and returns a term of the store. With milestone 21 that is
  the whole of `eval.rs`. Verus checks 215 items in `pathos-term` and 89
  in `pathos-check` (70 before), with no errors.
- **The two `unreachable!` are proved unreachable.** They are now one
  function, `children_first`, whose precondition is `false`; Verus proves
  at both calls that every child has its value. The invariant that gives
  this is under "The invariant of a level".
- **`evaluate` was cut into four functions**, as the last report said it
  would be. The steps and their order are the same; see "What had to be
  rewritten".
- **Not proved: that evaluation ends.** A program may run for ever, in
  Ethos too. Eight functions are marked as not proved to terminate.
- **Behaviour is unchanged**: every gate agrees with Ethos. Against milestone 21 it
  executes 0.2% fewer instructions on the regressions and 0.9% fewer on
  the cvc5 proofs; see "Time".
- **Cost**: 566 lines of specification and proof, against the 1,200 to
  1,800 estimated. Why is under "The estimate, updated".

### What Verus proves

| Function | What |
| --- | --- |
| `evaluate` | The contract milestone 21 trusted: it keeps the invariant, the store keeps its terms, and the result is a term of the store. |
| `run_frame`, `visit_term`, `revisit_term` | Each keeps the checker's invariant, the invariant of the level it works on and that of the cache of program applications; a new level it asks for is in order. |
| `EvFrame::new`, `result`, `settle`, `all_values`, `values_or` | What they return, exactly. |

No index is out of range: `args[0]` of an application (the store gives
the head, `lemma_shape`), `cchildren[0..3]` and `children[1..3]` of an
`eo::ite` (the invariant says a pending one has three children), and the
stack of levels, which is no longer indexed.

The two preconditions that milestone 21 left to `evaluate` are proved at
its calls: the list passed to `evaluate_program_internal` has a head, and
`eo::ite` is not passed to `evaluate_literal_op_internal`. The same
preconditions are still left to `build.rs` and `step.rs`.

### The invariant of a level

A level (`EvFrame`) has a work list `visit` and a map `visited` from a
term to its value, or to `None` while its children are being evaluated
(the term is *pending*). `EvFrame::ok` says:

1. Everything the level holds is a term of the store.
2. A place of the work list is *open* when its term is pending and every
   term above it was made before it (has a smaller handle). Every pending
   term is at an open place.
3. For an open place, each child of its term has a value or is on the
   work list above the place. For `eo::ite`, this is said of the condition
   only, since the branches are put on the list later, and only if needed.
4. A pending `eo::ite` has three children.

When a pending term is on top of the list, (2) says its place is open:
another open place below would have this same term above it, which is not
older than itself. Then (3) says its children have values, since nothing
is above the top. That is `lemma_top_open`, and it is all `revisit_term`
needs.

The design had (3) with "above some occurrence of the term". That is not
enough by itself: a list `[x, c, x]`, with `c` a child of `x` that has no
value, satisfies it, and the top `x` would then be looked at again without
its child. What excludes it is that a subterm is made before the term,
which the store's invariant gives (`lemma_children`). So the invariant
speaks of handles, and needs no ghost state to remember where a term was
expanded: the open place is the only one with nothing newer above it.

Four lemmas keep it, one for each thing that happens to a level:
`lemma_settle` (the top gets a value and leaves), `lemma_grow` (children
of the top are put above it), `lemma_frame_kept` (the store grew) and
`lemma_same`. The levels that wait are only required to be in order; that
the term on top of a waiting level is the application the level above
computes, which the design listed, is not needed: handing the result down
is `lemma_settle` whatever that term is.

### What is trusted

New in this milestone:

| Function | Contract |
| --- | --- |
| `plugin_evaluate` (the plugin's `evaluate`) | Keeps the invariant; the store keeps its terms; a term returned is a term of the store. As `plugin_evaluate_program` in milestone 21. |
| `has_eval_plugin`, `is_fatal` | None: each reads one field and returns a `bool`. |
| `copy_of` (`to_vec`), `copy_of_ctx` (`clone`), `push_all` (`extend_from_slice`) | The copy has the same terms; the list has the terms added at its end. Each is one call of the standard library that Verus has no usable specification for. |
| `children_first` | Its precondition is `false`, and Verus proves that at each call; its body, the `unreachable!`, is not looked at. |

Assumed besides: that the `Hash` and `Eq` of a list of term handles agree
(`axiom_term_lists_are_keys`), for the cache of program applications. The
same is assumed of a handle and of a pair of handles.

`evaluate` leaves the list of trusted functions. What milestone 21 listed
is otherwise as it was: typing, `mk_list`, `check_arity`, the plugin, the
message functions.

#### The circularity, now

(Milestones 23 and 24 removed what is left of it: see "The cycle, closed"
under milestone 24.)

Within `eval.rs` there is no assumption left to discharge: `evaluate`
calls the operators, and one of them, `evaluate_nil`, calls `evaluate`
(as does `evaluate_program_app`, from outside). Verus checks the cycle as it
checks any recursion, each call relying on the contract of the function
called. Verus was told not to ask for a measure (the eight functions
marked `exec_allows_no_decreases_clause`), so this is a proof that no call
panics, not that the calls end.

The circularity through typing is as it was: `type_of` is trusted, and
typing calls `evaluate`.

### What had to be rewritten

`evaluate` was one function of 190 lines: a loop over the stack of levels
with a loop over the top level's work list inside, and three flags
(`evaluated`, `new_context`, `can_evaluate`) carried from one turn to the
next. It is now:

- `evaluate`: the loop over levels. The level at work is a local variable
  and the levels that wait are on the stack, where before the level at
  work was the top of the stack. A level is pushed when it has to wait and
  popped when the one above is done, so a level moves twice for each
  program application that needs a level of its own. (The proof wants
  this: Verus then knows that working on one level leaves the others
  alone.)
- `run_frame`: the loop over one level's work list.
- `visit_term`: a term that needs no evaluation, a parameter, the first
  visit, and a term that has its value already.
- `revisit_term`: the second visit.

`Step` says what a level does next: go on, wait for a new level, or stop
because the run is over. It replaces `new_context` and the `break`.
`can_evaluate` and `evaluated` are locals of `revisit_term`; neither was
read across turns except `evaluated` at the very end, where it was always
the result of the bottom level.

Rewritten for Verus, with the same meaning: the two
`.collect::<Option<Vec<Term>>>()` are `all_values`; the
`zip`/`map`/`collect` is `values_or`; closures and `while let` are
`match`; the `if let ... && let` is nested.

One thing is gone: the plugin was given a clone of the level's
substitution, and is now given a reference to it. The clone was not
needed.

### Time

The binary of this milestone against that of milestone 21 (`ab2bcb4`),
instructions counted with Valgrind as for the shape check:

| Corpus | Instructions | Largest increase on one case | Time, best of 3 | Outputs |
| --- | --- | --- | --- | --- |
| Regressions (230) | -0.22% | +0.69% | -0.3% | identical |
| cvc5 proofs (400) | -0.87% | +0.26% | -0.5% | identical |

The times were taken while other jobs ran; the instruction counts are the
figures to rely on. Where the saving comes from was not looked into; the
flags are gone, and the plugin's clone was never on this path.

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `eval.rs` | 1,178 (was 1,101) | 571 (was 388) | 504 (was 121) |
| `store.rs` | 714 | 562 | 981 (was 980) |

Verus takes about 35 seconds for `pathos-term` and 7 for `pathos-check`
(5 before).

### The estimate, updated

| Part | Estimated | Spent |
| --- | --- | --- |
| `evaluate`, the frame stack | 1,200 to 1,800 lines | 566 |

The estimate assumed the invariant would have to say what each level
owes the one below and to carry ghost state for where each term was
expanded, as `match_terms` needed a measure and a ghost stack. Neither
was needed: the order of handles says where a term was expanded, and a
waiting level needs nothing but to be in order. The proof is four lemmas
about one level and a few lines at each place the code changes it. The
risk named last time, the solver's budget, did not show once the function
was cut: no function needs a raised limit.

For what remains (typing, building and step checking, about 1,150 lines
of code), the estimate of milestone 21 stands: 500 to 900 lines of
specification and proof for panic freedom, if `build.rs`'s desugaring has
no invariant of this kind. After two milestones that came in under, I
would now expect the lower half of that range. Correctness with a
semantics is a different piece of work, and I have no better number for it
than milestone 19 gave.

### Gates

Run on this branch with `verus` at `7cd893f` merged in (the snapshot
reader's checks from `main`, harness pin `237b961`).

- `scripts/verify`: `pathos_term` 215 verified, 0 errors; `pathos_check`
  89 verified, 0 errors; 41 seconds in all.
- `scripts/full-check`, the whole of it: every step passes. `tests` 230 of
  230, `proofs` 400 of 400, `large` 43 of 43, `cli` 3,192 of 3,192,
  `snapshot` under every option set and with the three broken snapshots,
  `options` 6,300 of 6,300, `bignum` 7 of 7, `perf` 673 of 673 (Ethos
  1,249 s, pathos 554 s, 44%), and `fuzz` has no finding that still
  differs in either set of findings.
- Three deliberate faults in `evaluate` were each refused by Verus: an
  `eo::ite` let through with a number of children other than three, a
  second `pop` of the work list, and the arm for `eo::ite` given to another
  operator.
- Formatting, Clippy with warnings as errors, and the tests in debug and
  release builds pass. No test was changed.
- `Cargo.lock` is unchanged; no dependency was added.
- The CI job that runs Verus is now named for the evaluator too.
- CI has not run on this branch yet: the reviewer pushes.

### For Daniel

1. **The restructuring of `evaluate`.** It is more than moving lines: the
   level at work is held in a local, and the loop is four functions. No
   output and no count changed on any gate, and the time is in the table
   above. If you would rather have the old shape back on `main`, the proof
   depends on the new one.
2. **Termination is not proved**, and is not planned: it does not hold.
3. **What is next.** Panic freedom of typing, building and step checking
   would remove `type_of` from the trusted list, and with it the
   circularity; the evaluator's contract is the one they need.

## Milestone 23: typing cannot panic

### Summary

- **Proved**: nothing in `typing.rs` can panic, each function keeps the
  checker's invariant, and every type returned is a term of the store:
  `get_type` and its work list, `get_type_internal`,
  `get_type_app_internal`, `check_arity`, `get_literal_op_type`, and the
  literal type rules (`set_literal_type_rule`, `get_literal_type_rule`).
  Verus checks 215 items in `pathos-term` and 105 in `pathos-check` (89
  before), with no errors.
- **No design stop was needed for the traversal.** `get_type`'s loop is as
  it was. Two things are more than moving code, and neither changes what
  runs: the contract of matching was widened (below), and messages go
  through helper functions.
- **The evaluator no longer trusts typing.** `type_of` and `arity_ok` in
  `eval.rs` call the verified functions. See "The cycle".
- **Not proved: that typing ends**, as for `evaluate`, which it calls.
- **Behaviour is unchanged**: every gate agrees with Ethos, the text and
  order of type errors included (the `tests` and `cli` gates hold the
  cases that print them). Against milestone 22 it executes 0.5%
  fewer instructions on the regressions and 0.1% fewer on the cvc5
  proofs.
- **Cost**: about 245 lines of specification and proof for the 407 lines
  of `typing.rs`.

### The cycle

Typing evaluates: a literal's type rule and the return type of an
application are evaluated. The evaluator types: `eo::typeof`, `eo::nil`
and the list operators ask for types. Milestones 21 and 22 proved the
evaluator given a contract for typing that was trusted. Now both sides are
verified, with the same contract:

> given the checker's invariant and a term of the store, the function
> keeps the invariant, the store keeps its terms, and what it returns is a
> term of the store.

`evaluate` meets it and relies on `get_type` meeting it; `get_type` meets
it and relies on `evaluate` meeting it. Verus checks this as it checks any
recursion: each function is verified once, with the contracts of the
functions it calls as assumptions. That is sound for what is claimed, that
no call panics and that results are terms of the store, for every run
that ends. It says nothing of a run that does not end, and Verus was told
not to ask for a measure: fifteen functions carry
`exec_allows_no_decreases_clause`, the eight of milestone 22 and seven
more (`get_type`, `get_type_internal`, `get_type_app_internal`,
`get_literal_op_type`, `literal_type_rule`, and in `eval.rs` `type_of` and
`evaluate_dt_constructors`).
A literal type rule `(eo::typeof eo::self)` still recurses until the stack
is full, as `docs/panics.md` lists under "Stack".

(Milestone 24 removed the three functions named next: see "The cycle,
closed" there.)

What is left of the circularity is outside these two files. Three trusted
functions are in `build.rs`: `list_of` (which is `mk_list`, through
`mk_expr`), and the two new ones below. `mk_expr` types and evaluates, so
`list_of`'s contract assumes of typing and evaluation, one level down,
what is proved of them here. Milestone 24 removes that. The plugin is
given the checker and may call anything; that stays an assumption.

### The contract of matching, widened

`match_terms` (milestone 19) required that every pair seen before the
call was matched under the context it is called with (`closed`). The
evaluator's callers meet that: each starts from an empty set.
`get_type_app_internal` does not, and cannot. It keeps one set of pairs
for all the arguments of an application, and between two arguments it
binds the parameter of a quoted argument type to the argument itself. If
that parameter was bound already, by an earlier argument, the binding is
replaced, and a pair seen under the old binding is no longer a match under
the new one. This is the behaviour of Ethos that
[cvc5/ethos#269](https://github.com/cvc5/ethos/issues/269) is about, and
pathos reproduces it.

So the requirement was dropped, and what milestone 19 proves of a match is
now proved *under* it (`was_closed`): a caller that meets it gets exactly
what it had, and the two callers in the evaluator still verify unchanged.
Proved without it: matching does not panic, keeps the context a
substitution between terms of the store, only adds bindings, and a ground
pattern matches exactly itself. The change is in the specification and
the proof only; `match_terms` runs as before.

For typing this means: Verus proves that `get_type_app_internal` does not
panic, and does **not** prove that the type it computes is the
instantiation of the head's type. That would be a correctness statement,
which this milestone does not make, and with the rebinding it is not true
in general.

### What had to be rewritten

- **Messages.** The functions took `out: Option<&mut String>` and wrote
  with a macro around `write!`, reborrowing with `as_deref_mut`. Verus
  accepts neither. Now `say(out, text)` appends, the eleven texts that
  format a kind or print a term are functions (`msg_no_rule`,
  `msg_child_type`, ...), and a function that goes on with its message
  takes `&mut Option<&mut String>`. The public functions keep their
  signatures; `check_arity` and `get_literal_type_rule`, which are called
  from outside with a message by value and from inside with a message that
  goes on, each have an inner function (`arity`, `literal_type_rule`). The
  texts are the same, built at the same points, and only when a message
  was asked for, as before.
- **`check_arity`'s table** is written twice: as code, and as the
  specification `Checker::takes`, which Verus proves the code computes.
  `get_literal_op_type` reads `children[1]` and `child_types[0..2]` on the
  strength of it.
- **Loops and conditions**: the `map`/`collect` over children is a loop;
  `and_then` with a closure, a `match` with a guard and the comparison of
  two `Option<Term>` are `match`es; `if let ... &&` is nested; the
  `while let` of `get_type` is a `loop` with a `match`.
- **Gone**: `Checker::match_terms`, a method that only called
  `matching::match_terms`; typing calls that directly.

### The checker's invariant

One clause is new: the type rule of each kind of literal is a term of the
store. `set_literal_type_rule` is verified to keep it; the snapshot
reader, which also fills the table, reads each rule with `read_term`,
which is verified to return a term of the store it is given.

### What is trusted

New in this milestone:

| Function | Contract |
| --- | --- |
| `say` | None: it appends text to the message, if there is one. |
| The eleven `msg_` functions | None: each returns a `String`. Six take kinds only; five print terms (`show`, `show_ctx`) and are trusted not to panic on terms of the store. |
| `function_type_of` (which is `mk_function_type`, in `build.rs`) | Keeps the invariant; the store keeps its terms; the type is a term of the store. |
| `return_type_of` (which is `get_function_type(..).1`, in `build.rs`) | The type is a term of the store. |

Assumed besides: that the derived `Hash` and `Eq` of `LitKind` agree
(`axiom_literal_kinds_are_keys`), for the table of type rules.

No longer trusted: `type_of` and `arity_ok`.

### The preconditions, and who meets them

| Precondition | Met by |
| --- | --- |
| `get_type_app_internal`: the list has a head | `get_type_internal`, its only caller, from the store's shapes (`lemma_shape`). Proved. |
| `evaluate_program_app`, `compute_constructor_term`: the list has a head (milestone 21) | Still `build.rs` and `step.rs`. Typing calls neither. |
| `evaluate_literal_op`: an `eo::ite` has three arguments (milestone 21) | Still `build.rs`. Typing does not call it either, but it now supplies what `build.rs` needs to prove it: `check_arity` returns `Checker::takes(k, n)`, and `takes` of `eo::ite` is `n == 3`. |

So typing discharges neither of the two preconditions left to the callers
in milestone 21; both are for milestone 24.

### Time

The binary of this milestone against that of milestone 22 (`b991c02`),
instructions counted with Valgrind:

| Corpus | Instructions | Largest increase on one case | Time, best of 3 | Outputs |
| --- | --- | --- | --- | --- |
| Regressions (230) | -0.47% | +0.52% | +0.3% | identical |
| cvc5 proofs (400) | -0.08% | +0.34% | +0.2% | identical |

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `typing.rs` | 496 (was 407) | 174 | 46 |
| `matching.rs` | 93 | 167 (was 164) | 229 (was 218) |
| `checker.rs` | 284 | 89 (was 81) | 34 |
| `eval.rs` | 1,178 | 573 (was 571) | 504 |

`typing.rs` has 89 more lines of code: the message functions, the two
inner functions and the two wrappers around `build.rs`.

Verus takes about 36 seconds for `pathos-term` and 8 for `pathos-check`
(7 before).

### The estimate for milestone 24

`build.rs` (560 lines) and `step.rs` (138 lines): 300 to 600 lines of
specification and proof for panic freedom. Typing cost 0.6 lines a line of
code and the operators 0.7; `build.rs` is the same kind of code (it passes
terms along and indexes lists whose length it has just checked), with two
things that could cost more:

- `mk_expr` desugars: it folds n-ary applications, builds constructor
  terms and resolves overloads, and it calls typing and the evaluator. Its
  loops over arguments index several lists together, and I have not looked
  for an invariant that needs stating.
- `get_function_type` slices (`&ch[..n - 1]`), and `get_variables` and
  the overload search keep sets.

Milestone 24 would discharge the two preconditions above, remove
`list_of`, `function_type_of` and `return_type_of` from the trusted list,
and leave the plugin, printing and the parser as what the checker's core
assumes.

### Gates

- `scripts/verify`: `pathos_term` 215 verified, 0 errors; `pathos_check`
  105 verified, 0 errors; 45 seconds in all.
- `scripts/full-check --quick`, as the brief asks: every step passes.
  `tests` 230 of 230, `proofs` 400 of 400, `large` 43 of 43, `cli` 3,192
  of 3,192, `snapshot` under every option set and with the three broken
  snapshots, `bignum` 7 of 7, and `fuzz` has no finding that still differs
  in either set. The `options` and `perf` gates were not run; the table
  under "Time" stands in for `perf`.
- Three deliberate faults in typing were each refused by Verus: an index
  one past the argument types, `child_types[3]` for `eo::requires`, and a
  wrong number in `check_arity`'s table.
- `cargo test` in debug and release builds and `cargo clippy
  --all-targets` with warnings as errors pass, and `cargo fmt --check`.
  No test was changed.
- `Cargo.lock` is unchanged; no dependency was added.
- The CI job that runs Verus is now named for typing too.
- CI has not run on this branch yet: the reviewer pushes.

### For Daniel

1. **The contract of matching was changed**, not only added to: a
   requirement of milestone 19 became a hypothesis of its conclusions.
   Nothing that was proved is lost, and the function is unchanged, but it
   is a change to a reviewed specification.
2. **Typing's result is not proved correct even where matching is**,
   because of the rebinding of quoted parameters. If Ethos changes that
   (#269), the stronger statement becomes available.
3. **Milestone 24** (`build.rs`, `step.rs`), with the estimate above.

## Milestone 24: term building and step checking cannot panic

### Summary

- **Proved**: nothing in `build.rs` and `step.rs` that the checker's core
  uses can panic, each function keeps the checker's invariant, and every
  term built or returned is a term of the store: `mk_expr` with its
  desugaring (`mk_apply_expr`, `mk_apply_attr`, `mk_as_expr`,
  `mk_beta_reduce`, the overload search), the builders of function types,
  program types, lists, binder lists, pairs and proofs,
  `get_function_type`, `get_variables`, `has_variable`, and `check_step`.
  Verus checks 216 items in `pathos-term` and 137 in `pathos-check` (105
  before), with no errors.
- **No design stop was needed.** `mk_expr`'s desugaring is as it was, with
  closures and iterators written as loops.
- **The trusted wrappers are gone**: `list_of`, `function_type_of` and
  `return_type_of`. Of the cycle of evaluation, typing and building, only
  the plugin is trusted.
- **The two preconditions of milestone 21 are proved** at the calls in
  `build.rs` and `step.rs`.
- **Three functions of `build.rs` are not verified**, and say so:
  `mk_type_constant`, `get_bound_var` and `mk_disambiguated_type`. The
  parser calls them; nothing verified does.
- **Behaviour is unchanged**: every gate agrees with Ethos, warnings and
  step errors included. Against milestone 23 it executes 0.10% more
  instructions on the regressions and 0.01% more on the cvc5 proofs.
- **Cost**: about 450 lines of specification and proof for the 558 lines
  of the two files; the estimate was 300 to 600.
- **The last section** lists, for milestones 17 to 24 together, what is
  proved, what is trusted and what is not covered.

### The cycle, closed

Evaluation types and builds; typing evaluates; building evaluates, types,
and calls itself. After this milestone every function on those paths is
verified against the same contract:

> given the checker's invariant and terms of the store, the function keeps
> the invariant, the store keeps its terms, and what it returns is a term
> of the store.

Verus checks the functions one by one, each with the contracts of those it
calls. Nothing in the cycle is assumed any more except the plugin's two
hooks (`plugin_evaluate`, `plugin_evaluate_program`), which are given the
checker and are code Verus does not see. With no plugin installed, as in
`pathos` itself, they return at once.

As before, this is a proof for runs that end. In `pathos-check`,
twenty-four functions on the cycle carry
`exec_allows_no_decreases_clause`: the fifteen of milestone 23, seven of
`build.rs` that are on the cycle (`mk_expr`, `mk_apply_expr`,
`mk_apply_attr`, `mk_as_expr`, `mk_beta_reduce`, `get_overload_internal`,
`mk_list`), and two that were pulled into it (`evaluate_literal_op`,
`compute_constructor_term`). `get_variables` and `has_variable` carry it
too, for their work lists; they do end, and that was not proved. The loops
of `mk_function_type`, `mk_requires_list`, `get_function_type`,
`mk_apply_attr` and the overload search are proved to end.

### The preconditions of milestone 21

| Precondition | Proved at |
| --- | --- |
| `evaluate_program_internal`, `compute_constructor_term`: the list has a head | `mk_apply_expr`, which `mk_expr` calls only with a non-empty list, and `get_overload_internal`, whose callers pass a head. |
| `evaluate_program_app`: the list has a head | `check_step`: the list starts with the rule's program. |
| `evaluate_literal_op`: an `eo::ite` has three arguments | `mk_expr`: it calls it only after `check_arity`, which returns `Checker::takes`. |

What these functions ask of *their* callers, which are the parser and so
not verified:

| Precondition | Of |
| --- | --- |
| Every term passed is a term of the store | All of them. There is one store. |
| The kind is not that of a symbol or a literal | `mk_expr`. The parser passes constant compound kinds. |
| Each term is a pair | `mk_requires_list`. The parser passes the pairs it built. |

### The checker's invariant

Three clauses are new. Each is something the code relied on and nothing
said:

- **A builtin's kind is a compound kind.** `mk_expr` hands it to the store,
  which refuses a symbol's or a literal's kind by panicking. From text it
  is set from a fixed table; the snapshot reader checks it (milestone 20).
- **A program's patterns have a head.** `check_step` takes the arguments of
  the pattern (`[1..]`) to say what a rule expected. The snapshot reader
  checks it with the same function that checks the cases are pairs.
- **The terms a name is bound to are terms of the store** (the table of
  overloads).

As with the rest of the invariant, the code that is not verified (the
parser's calls that fill these tables) is trusted to keep it.

### What had to be rewritten

- `at(i)`, a closure in `mk_apply_attr`, is written out at its two uses.
- `iter().rev()` is a loop that counts down; `zip` is a loop over one
  index; `to_vec` is `copy_of`; `vec![x]` followed by `extend_from_slice`
  is `prepend`.
- A slice by a range goes through `rest_of(ts, from)` or
  `part_of(ts, from, to)`, whose precondition is the bound that the slice
  checks.
- Guards in `match`, `if let ... &&`, `map_or`, `filter`, `then_some`,
  `unwrap_or`, `saturating_sub` and the slice pattern of
  `mk_let_binder_list` are `if`s and `match`es.
- `mk_apply_expr` reads what it needs of the head's record (`kind`,
  `attr`, `cons`, and the overloads if the name is overloaded) before it
  starts building, where it read them as it went. The overloads are now
  looked up for a builtin too, and then not used; nothing else moves.
- Warnings and step errors: the texts that print something are `msg_`
  functions, and `check_step` appends with `say`, each line with its
  newline, where it used `writeln!`.

### What is trusted

New in this milestone:

| Function | Contract |
| --- | --- |
| `rest_of`, `part_of` | The slice asked for; the precondition is that the bounds are in range. Each is one slice expression. |
| Eight `msg_` functions (five in `build.rs`, three in `step.rs`) | None: each returns a `String`. Seven print terms. |

Assumed besides: that the `Hash` and `Eq` of `String` agree
(`axiom_names_are_keys`), for the table of overloads.

No longer trusted: `list_of`, `function_type_of`, `return_type_of`.

### Time

The binary of this milestone against that of milestone 23 (`f4766d8`),
instructions counted with Valgrind:

| Corpus | Instructions | Largest increase on one case | Time, best of 3 | Outputs |
| --- | --- | --- | --- | --- |
| Regressions (230) | +0.10% | +1.26% | +1.0% | identical |
| cvc5 proofs (400) | +0.01% | +0.40% | +0.0% | identical |

### Lines and time

| File | Code | Specification | Proof |
| --- | --- | --- | --- |
| `build.rs` | 552 (was 445) | 225 | 142 |
| `step.rs` | 185 (was 113) | 17 | 12 |
| `checker.rs` | 304 (was 284) | 124 (was 89) | 57 (was 34) |
| `typing.rs` | 490 (was 496) | 163 (was 174) | 46 |
| `eval.rs` | 1,175 (was 1,178) | 568 (was 573) | 504 |

The two files have 179 more lines of code: the `msg_` functions and the
helpers, and `match`es where there were combinators.

Verus takes about 34 seconds for `pathos-term` and 8 for `pathos-check`.

### Gates

- `scripts/verify`: `pathos_term` 216 verified, 0 errors; `pathos_check`
  137 verified, 0 errors; 42 seconds in all.
- `scripts/full-check --quick`, as the brief asks: every step passes.
  `tests` 230 of 230, `proofs` 400 of 400, `large` 43 of 43, `cli` 3,192
  of 3,192, `snapshot` under every option set and with the three broken
  snapshots, `bignum` 7 of 7, and `fuzz` has no finding that still differs
  in either set. The `options` and `perf` gates were not run; the table
  under "Time" stands in for `perf`.
- Four deliberate faults were each refused by Verus: a chain that reads
  one argument past the end, an opaque application that takes as many
  arguments as there are, a proof rule accepted with three components, and
  an `eo::` operator evaluated without the arity check.
- `cargo test` in debug and release builds and `cargo clippy
  --all-targets` with warnings as errors pass, and `cargo fmt --check`.
  No test was changed.
- `Cargo.lock` is unchanged; no dependency was added.
- The CI job that runs Verus is renamed for the checker's core.
- CI has not run on this branch yet: the reviewer pushes.

## Milestones 17 to 24: what is proved, trusted and not covered

This section is the basis for deciding on correctness proofs. It says what
the eight milestones add up to. Each claim is Verus's, on the code that
ships: `scripts/verify` checks 216 items in `pathos-term` and 137 in
`pathos-check`, and CI runs it.

### In one paragraph

The checker's core is the term store, the literal operators, matching,
the evaluator, typing, term building and step checking: about 4,000 lines
of code in `pathos-term` and `pathos-check`. **For every run that ends, no
function of that core can panic, and every term it handles is a term of
the store**, given that the code around it (the parser, the printer, a
plugin) hands it terms of the store and keeps the tables of the checker in
order. Beyond that, three parts are proved **correct** against a
specification: the literal operators, the term store, and matching of
programs. The evaluator, typing, building and step checking are proved
safe, not correct: nothing yet says what the *right* result of evaluating
a term or checking a step is.

### Proved

| Part | Proved | Milestone |
| --- | --- | --- |
| Bit-vectors (`bitvec.rs`) | No panic; each operation computes the stated value on width and integer. | 17 |
| Literal operators (`Lit::evaluate`) | No panic; agrees with a specification (`eval_spec`) for the arithmetic and bit-vector operators, with Ethos's corner cases; the result of an operation on well-formed literals is well formed. | 17 |
| Term store (`store.rs`) | No panic. Hash-consing: equal kind and children give the same term, and the store's view as trees is injective (same tree, same term). A child is made before its parent. A term has a number of children its kind can have. `is_ground` means the tree has no parameter and no `eo::?`. Adding terms keeps the old ones as they were. | 17, 19, 21 |
| Snapshot reader of the store (`read_from`, `Lit::read_from`, the codec) | No panic on any bytes; a store returned satisfies the whole invariant. | 20 |
| Matching (`match_terms`, `match_cases`) | No panic; ends. A match found is a match: the context, applied to the pattern, gives the term; a ground pattern matches exactly itself; `eo::?` matches nothing; bindings are only added. For programs (`match_cases`) this holds of the case chosen. For typing it holds only when no quoted parameter was rebound (cvc5/ethos#269). | 18, 19, 23 |
| Evaluator (`eval.rs`) | No panic; keeps the checker's invariant; results are terms of the store. The traversal's invariant: a term is evaluated after its children. | 21, 22 |
| Typing (`typing.rs`) | The same; `check_arity` computes a stated table. | 23 |
| Building and step checking (`build.rs`, `step.rs`) | The same. | 24 |

"No panic" covers every index, slice, `unwrap`-like operation, arithmetic
overflow in a debug build, and the two `unreachable!` of the evaluator. It
is the property the rows marked "Safe" in [panics.md](panics.md) argued
for by hand; for these files Verus now checks it.

### Trusted

What Verus is told and does not check. Each item is in the code as a
function marked `external_body`, or an `axiom_` function.

| What | How much | Why it is believed |
| --- | --- | --- |
| Arbitrary-precision numbers (`num.rs` over `malachite`) | 41 functions of `Integer` and `Rational` | Each is one call into `malachite`, with the mathematical operation as its contract. `malachite` is not verified; the `bignum` gate compares its results with Ethos's (GMP) up to a million bits. |
| Strings (`eostring.rs`) | 9 functions | Not specified at all: the string operators are outside `eval_spec`. They are trusted not to panic. |
| Parsing and printing of bit-vectors and one logarithm | 3 functions | Text in and out. |
| Hashing in the store | 7 functions and 2 axioms | The hash functions return a number; that two different node tags differ; a length fact about `Vec`. |
| Hash and order of keys | 6 axioms | That the derived `Hash`, `Eq` and `Ord` of `Term`, pairs and lists of `Term`, `LitKind` and `String` agree, so that the standard maps behave as maps. |
| One-line wrappers of the standard library | `copy_of`, `copy_of_ctx`, `push_all`, `rest_of`, `part_of`, `reverse`, `latin1_text`, four `from_index` | Verus has no usable specification for the call; the contract says what the call does. |
| Messages | `say`, `warn`'s sink, and 28 `msg_` functions | They build text. 21 of them print terms (`show`, `show_list`, `show_ctx`), so **the printer is trusted not to panic on terms of the store**. |
| Statistics | `Stats`, `count_program` | A counter. |
| The plugin | `plugin_evaluate`, `plugin_evaluate_program`, `has_eval_plugin` | Code from outside. Trusted to keep the invariant and return terms of the store. Without a plugin, they do nothing. |
| `is_fatal`, `children_first`, `atomic_kind` | 3 | A field read; and two functions that hold a `panic!`, whose precondition is `false`, proved at every call. |
| The solver and Verus | | Z3 and Verus itself are trusted, as is the Rust compiler. |

And one thing that is not a function: **the checker's invariant is assumed
at the boundary.** The verified functions require it and keep it. The
parser (`pathos-elab`) calls them and also writes to the checker's tables
directly (attributes, programs, overloads, literal type rules). That it
passes terms of the store and leaves the tables as the invariant says is
not proved. The snapshot reader, the other way into those tables, checks
the invariant's clauses with ordinary code and tests (milestone 20), and
only its store half is proved.

### Not covered

| What | State |
| --- | --- |
| **Correctness of evaluation, typing, building and step checking** | Not stated, so not proved. There is no specification of what `evaluate`, `get_type` or `check_step` should return. This is what a decision on correctness proofs is about. |
| **Termination** | Proved for matching, the literal operators, some builders, and the store's loops except the two that probe its hash tables (`ConsTable::find` and `ConsTable::insert_new`, which end as long as the table has an empty slot; that they end was not proved). Not proved, and false in general, for evaluation and whatever calls it: a program may run for ever. 28 functions are marked `exec_allows_no_decreases_clause`: those two, 24 on the cycle of evaluation, typing and building, and `get_variables` and `has_variable`, which end too. |
| **Stack depth and memory** | Not covered. The "Stack" and "Resource" rows of [panics.md](panics.md) stand: three recursions follow the input, and an input can ask for more memory than there is. |
| **Completeness of matching** | Not proved: that when matching fails, no match exists. |
| **The parser and the commands** (`pathos-syntax`, `pathos-elab`: about 4,500 lines) | Not verified. Its panic rows in `panics.md` rest on reading and on fuzzing. It is also the code that must keep the checker's invariant. |
| **The printer** (`print.rs`) | Not verified; see "Messages" above. |
| **The checker's own snapshot reader and writer, statistics, options** | Ordinary code with tests. |
| **Three builders the parser calls** (`mk_type_constant`, `get_bound_var`, `mk_disambiguated_type`) | Not verified. The last registers a program, so it too must keep the invariant. |
| **The string operators and the conversions between kinds of literals** | Proved not to panic only as far as their callers go; what they compute is not specified. |
| **`pathos-eoc`**, the compiler stages | Not touched. |
| **Agreement with Ethos** | Not a subject of these proofs at all. It rests on the gates. |

### What it cost

| Milestones | Code verified | Specification | Proof |
| --- | --- | --- | --- |
| 17 to 24, both crates | about 4,000 lines (5,780 in the two crates, with the wrappers of `malachite`, the tables of kinds, the printer and the checker's snapshot code) | 2,397 lines | 2,159 lines |

Panic freedom of the evaluator, typing and building (milestones 21 to 24)
took about 1,950 of those lines for about 2,700 lines of code, or 0.7 lines
a line. The parts proved correct cost far more per line: matching, 93 lines
of code, has 396 lines of specification and proof, and the store, 714
lines, has 1,543.

### For a decision on correctness

Three observations from doing this, not a recommendation:

1. **A correctness proof needs a specification first, and for the evaluator
   that is the hard part.** For matching the specification was one
   function (`inst`). For `evaluate` it would be a semantics of Eunoia's
   programs and operators: what a term evaluates to, including when
   evaluation is stuck, in which order, and what `eo::ite` leaves
   unevaluated. Ethos's manual does not give it in that form; it would be
   written from the C++ and from the manual, and it would itself be the
   thing to review.
2. **Some of what pathos must do is not what a clean semantics says.** The
   rebinding of quoted parameters in typing (#269) is the example: pathos
   reproduces it. A specification either includes such behaviour, as
   matching's does for three quirks, or pathos is proved against something
   Ethos does not do. The terms Ethos forgets (#271) are the opposite
   case: there pathos already does what a clean semantics says, and
   differs from Ethos.
3. **The ratio seen so far for correctness is 4 to 5 lines for each line of
   code**, against 0.7 for panic freedom. For the evaluator's 1,175 lines
   that is several thousand lines, on top of the specification, if the
   ratio holds. It may not: `evaluate`'s invariant for panic freedom
   turned out much smaller than estimated, and the operators mostly
   delegate to literal operations that are already specified.
