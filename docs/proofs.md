# The proofs about the compiled checker: setup and a pilot

Milestone 31. The goal that this prepares is a theorem that carries
logos's soundness over to `pathos`: if the Lean that Aeneas writes for the
compiled checker returns `Correct` on handles that stand for assumptions
and commands, then logos's verdict on them is `correct`, and logos's own
theorem gives that the assumptions are unsatisfiable. This milestone built
what such a proof needs and proved a few pieces of it, to find out what
the whole costs. The whole is not proved.

Everything is in [proofs/](../proofs/), a Lean project of its own.

## What there is

| | |
| --- | --- |
| `generated/cpcmini-checker/` | The checker for **CpcMini**, logos's calculus of five rules (`symm contra refl scope trans`), compiled by `rust-meta` as the CPC checker is. The pilot is on it. `scripts/generate-mini` writes it. |
| `proofs/MiniChecker/` | The Lean that Charon and Aeneas write for that crate, stitched: the runtime once (`Runtime.lean`, 13,531 lines) and the generated functions (`Part0.lean`, 15,937 lines). Generated, never edited. |
| `proofs/PathosProofs/` | The proofs written by hand: the store (`Store/`), the runtime lemmas and the embeddings that generated proofs use (`Runtime/`), and the tactics of their lines (`Tactic.lean`). 5,055 lines. |
| `proofs/MiniCases.lean`, `MiniEmbed.lean`, `MiniCtors.lean`, `MiniCacheSem.lean`, `MiniProofs.lean` | Generated with the crate by `scripts/generate-mini` (milestone 32): the cases of logos's programs as functions, how the checker's values are stored (`enc`, `dec`, and that `dec` undoes `enc` on the values the store can hold), what `construct` and `destruct` do with each data constructor, what the cache of results holds, and the proofs about the generated functions. Never edited. |
| `proofs/PathosProofs/Trusted.lean` | What is assumed about the Rust that is not translated. |
| `proofs/axioms-allowed.txt` | Every axiom a theorem may rest on: the trust, as a list. |
| `proofs/pins.env` | The versions: Lean and Mathlib `v4.36.0`, Aeneas `1dc8ad31`, Charon `454586e9`, logos `bdcbd95f` for the proofs (cvc5/logos main with #521, function types guarded; at Lean `v4.36.0` since cvc5/logos#518). The full CPC crate is compiled from the same logos revision (`difftest.env`'s `LOGOS_REV`). |
| `proofs-cpc/` | Stage 5: the same proofs for the **full CPC**'s checker (`generated/cpc-checker`), a Lean project of its own with `proofs/`'s pins and packages. Its translation (`CpcChecker/`, 13 parts, about 500,000 lines), its generated Lean (`CpcCases`, `CpcEmbed`, `CpcCtors`, `CpcCacheSem`, `CpcProofs`, by `scripts/generate-cpc`), and the hand-written library instantiated for CPC by `scripts/proofs-instance` (not in the repository), less what `proofs-cpc/excluded.txt` leaves out. `scripts/proofs-build --cpc` builds and audits it. See `proofs-cpc/README.md`. |

To build and check, from a clean checkout:

```
scripts/aeneas-setup DIR                 # Charon and Aeneas, once
scripts/proofs-build --translate DIR     # the Lean of the crate again, compared;
                                         # then the build, and the axioms
scripts/proofs-build                     # the build and the axioms only
scripts/proofs-build --no-build          # the pins and the overflow setting (CI)
```

`scripts/proofs-build` checks that the lakefile, the manifest,
`scripts/aeneas-setup` and the crate's note agree with `pins.env`, and that
`Cargo.toml` builds the checker crate with overflow checks; builds under an
8 GiB cap with two Lean processes at a time (`PROOFS_JOBS`); and runs `scripts/proofs-axioms`, which fails on a `sorry` or on
an axiom that `axioms-allowed.txt` does not list.

## CpcMini

logos has no signature file for CpcMini: `install/install-sig.sh --mini`
compiles `Cpc.cached.eo` for five rules, and the first stage of that
compilation writes the reduced signature (53 lines). `scripts/generate-mini`
runs the same command with the rules it reads from logos's script, fails
unless the Lean it gets is logos's `CpcMini/` at the pinned revision (12
files, the same apart from a header and `partial def`), and compiles the
reduced signature with `driver.py rust`. So the Rust and the Lean that the
proofs relate come from one signature and one compiler.

The crate has 82 functions; 76 have a definition of the same name in
logos's CpcMini. The other six are datatype helpers that the Lean pipeline
trims after its second stage and the Rust pipeline keeps.

**CpcMini has no `logos_verdict`**: no `Api`, `ApiChecks` or `ApiCorrect`.
Its top theorem is `correct___eo_is_refutation`. So the pilot's target is
the refutation: the Rust `check_refutation` returning `true` gives
`__eo_checker_is_refutation F pf = true`. The verdict-level theorem, with
the translation checks of `check_proof`, is for CPC.

## One Lean project

logos is at Lean and Mathlib `v4.36.0` itself since cvc5/logos#518, and
Aeneas's Lean library (at `v4.36.0-rc2`) needs no change to a source file
to build with them. Lake uses the root project's toolchain and, for a
package required more than once, the root's requirement. So `proofs/`
requires both at the commits pinned, names Mathlib `v4.36.0` last, and no
fork of either is needed for the build.

Milestone 31 found the same for logos at `v4.34.0` (`cf187429`), but only
for what `proofs/` builds, `CpcMini`'s proofs. **logos's verification of
all of CPC did need changes to its proofs**, as stage 1 of milestone 32
found (below): what `proofs/` pins is now logos's own move to `v4.36.0`.

| Build, under 8 GiB | Time | Peak |
| --- | --- | --- |
| Aeneas's library | 151 s | 4.3 GiB |
| logos, `CpcMini.Proofs.Checker` (Mathlib from its cache) | 95 s | 1.4 GiB |
| `proofs/`, first build of everything | 196 s | 4.3 GiB |
| `proofs/` from a clean checkout: the translation, the build, the axioms | 335 s | |
| logos, `Cpc.ApiCorrect` and what it imports (stage 1 of milestone 32, at `cf187429`, `LEAN_NUM_THREADS=3`, a cap of 16 GiB, not 8) | 3 h 11 min, to the failures described below | 8.6 GiB for one module, 15.3 GiB for the three |

**logos's verification of CPC at `v4.36.0`**: `lake build Cpc.ApiCorrect`
in logos's `verification` project, with the pins moved and nothing else
changed, was stopped by the 8 GiB cap three times in milestone 31, each run
going on from the last, and never by an error of Lean:

| Run | Cores given (`taskset`) | Ended after | Modules of `Cpc` built by then |
| --- | --- | --- | --- |
| 1 | all 20 | 22.5 min | 151 |
| 2 | 2 | 3 min | 12 more |
| 3 | 1 | 3.5 min | 1 more |

Milestone 31 concluded from the third run that one module needs more than
8 GiB. **That was wrong.** Lake starts as many Lean processes as the
machine has cores whatever `taskset` allows it: a sampler in milestone 32
found 20 of them in the "one core" run, each under 2.5 GiB, 15.4 GiB
together. `LEAN_NUM_THREADS` is what limits Lake: with
`LEAN_NUM_THREADS=2` there are two. The build with that setting is stage 1
of milestone 32. `CpcMini`'s proofs, which the pilot uses, build in 95 s at
1.4 GiB.

**Stage 1's result: logos's CPC proofs needed changes at `v4.36.0`.**
From Lean `v4.35.0` on, Lean checks a comparison such as
`native_zlt x 4294967296` with a symbolic `x` by evaluating `Int.decLt`,
once per unit of the bound, and fails with "(kernel) deep recursion
detected" or "maximum recursion depth has been reached". On logos main
then, 14 modules of `Cpc` failed (cvc5/logos#516). The fix rewrites with
a lemma, `SmtEval.native_zlt_eq : native_zlt x y = decide (x < y)`, where
the proofs unfolded `native_zlt`; a few proof scripts lost lines that newer
Lean no longer reaches. That is cvc5/logos#518 (`a9944ea7`), whose last
commit is the patch for the 10 modules that stage 1 found still failing;
with it `Cpc.ApiCorrect` and logos's default targets build. `CpcMini`
needed none of it.

**`-j1` must not be among the Lean arguments** (logos's lakefile has it).
Measured again in milestone 32 with a sampler, one Lean process each time
(`lake env lean` on the stitched first part of CPC, 37,178 lines, whose
largest group of mutually recursive functions is 12,107 lines), under the
8 GiB cap: with `-j1` the process is at the cap after 25 s and is killed;
without it, 169 s and a peak of 3.75 GiB. Setting `LEAN_NUM_THREADS` to 2
or to 4 instead changes nothing for that process (168 s, 3.8 GiB): it is
the `-j1` argument that costs the memory.

**How many Lean processes run at once** is Lake's choice, and it starts as
many as the machine has cores. `taskset` does not change that (it limits
Aeneas's workers, which is what `scripts/aeneas-translate` uses it for);
`LEAN_NUM_THREADS` does. `scripts/proofs-build` sets it (`PROOFS_JOBS`,
default 2), since what fits under a cap is the sum over the processes.

## Stitching

`scripts/aeneas-stitch IN OUT` makes one development of the per-part files
of `scripts/aeneas-translate`: the runtime once, each part importing the
earlier ones in place of its axioms, no declaration changed. It checks that
every part has the runtime of the first, that a `mutual` block is of one
part, and that each axiom it drops names a definition of an earlier part.
A part's file has an axiom for an opaque function only if the part calls
it, so the runtime's axioms are the union over the parts.

For CPC's thirteen parts it replaces 340 axioms by imports, and the result
builds under 8 GiB: the runtime in 85 s, the parts in 815 s, peak 3.7 GiB
(15 minutes, against 30 for the files one by one). It is not committed
(530,000 lines).

## What is proved

Every theorem is a partial-correctness triple of Aeneas's library
(`⦃ … ⦄div`): **if the Rust function returns, it has not panicked and the
postcondition holds.** Nothing is said of a run that does not end. That is
more than the goal needs (which only asks about runs that return `Ok`) and
it is what Aeneas's `step` tactic works with; absence of panics has been
cheap so far.

### The store (`Store/`)

- **The table of terms** (`Table.lean`, `SameData.lean`, `Hash.lean`,
  `Intern.lean`). `place`, `grow` and `find` as walks over the slots;
  `same_data` answers `true` exactly on equal data; computing a hash does
  not fail. `StoreInv`: every term has its hash, which is the hash of its
  data; the table has every term and nothing else; **no two handles have
  the same data**. `Store.intern_spec`: `intern` keeps it, keeps every term
  under its handle, and returns a handle whose data is the data given.
- **The operations** (`Ops.lean`). `view`, `is_stuck`, `unapply` as
  equations. Well-formedness: term 0 is the stuck term, data refers to
  earlier terms, no application has a stuck argument, a node has its
  constructor's arity. `apply`, and `construct` and `destruct` for the
  constructors that are plain data.
- **`Store.new_spec`** (`New.lean`): the store `Store::new` builds has the
  invariant, so the invariant is not vacuous.
- **Handles and logos's values** (`Tree.lean`, `Rep.lean`, milestone 32).
  A handle unfolds to a tree (`Holds nodes t x`: its data, with the handles
  in it unfolded). Every value of logos the checker computes with has the
  tree it is stored as, `Embedded.enc`, generated for each datatype
  (`MiniEmbed`), with `Embedded.emb` the values the store can hold.
  `Rep nodes t x`, and `Represents.rep s t x` for a store: the handle
  unfolds to the value's tree and the value is embeddable, for a value of
  any type. A handle stands for at most one value (`Rep.functional`, from
  `Holds.functional` and `dec_enc`), a value has at most one handle
  (`Rep.injective`, from "no two handles have the same data"), and both
  survive the store growing (`Rep.mono`). Both directions matter: the
  generated code chooses a case by comparing handles, and
  `Represents.eq_iff` says that is comparing values. (Until milestone 32
  there was a relation per type, written out for the stuck term, the
  operators, applications and Booleans only.)
- **The cache of program results** (`Cache.lean`, `CacheOps.lean`). Its
  table's operations do not panic and keep it well formed; what `get`
  answers is the result of an entry with that program and those arguments;
  `insert` adds the entry for what it is given, or nothing. **That `get`
  finds every entry is not proved, and not needed**: a cache that misses
  is slower, not wrong. `CacheInv`, part of the store's invariant: every
  entry is its program's result on what its arguments stand for.
- **The type cache** (`CacheOps.lean`, `Runtime/Ops.lean`). `$eo_typeof`
  and `$smtx_typeof` keep their results apart: a row per term, pushed
  with the term (`push_term`), with a slot for each kind, read and written
  by the term's handle (`cached_type`, `cache_type`); no hashing, no size
  limit. Its meaning is the program cache's for a program of one
  argument, so it reuses the generated table `ProgramSem`, under ids that
  no program id can be (`typeSemId`: 2^32 and 2^32 + 1). `CacheInv`
  gained two fields: every filled slot is right (`TypesOK`), and the count
  of entries that `type_insert` keeps is at most the number of filled
  slots (`count`), so its `+ 1` cannot overflow (Aeneas makes an
  overflow a failure). `Store.Extends` says that `intern` adds only empty
  rows and keeps the counters. The wrapper of such a program is
  `Store.framed_type_cached`, as `framed_cached` is for the other.
- **The jump pointers of the state lookup** (`Jumps.lean`, milestone 32).
  `state_nth` keeps a side table, `state_jumps`, indexed by handle; it is
  the fourth part of `Store.Inv`, `jumps : JumpsOK`.
  - What it says: the entry `(d, j)` of a handle, where `d > 0`, has `d`
    equal to the handle's depth (the number of `$emb_s.cons` nodes down
    its tails, `StateDepth`), and `j` is reached after between 1 and `d`
    tails (`StateDown`). These are inductive relations over the store's
    terms, so they survive the store growing (`JumpsOK.mono`).
  - It changes the meaning of no other part. The lemmas that rebuild the
    invariant (`Inv.congr`, `congr'`, `with_cache`) take that the table is
    unchanged, and `tick`, `enter` and `leave` now say so. `intern_inv`
    gets it from `Store.Extends`, and `new_spec` from the empty table.

### The programs (`MiniProofs.lean`, generated)

Milestone 31 proved four programs by hand (`$mk_symm`, `$eo_prog_contra`,
`$mk_trans`, `$eo_state_is_closed`: 1,537 lines). Those proofs are gone:
the generator writes them now, with the crate (see "Generated proofs"
below). Of each program with a generated proof, `specs` says: on a store
with the invariant and handles that stand for the arguments, the generated
program, if it returns, has not panicked, leaves a store with the
invariant in which every earlier handle stands for what it did, and
returns a handle of what logos's function of the same name gives (or an
error).

### CPC's builtins (stage 5, milestone 6)

The builtins CpcMini's logos lacks, proved for CPC in
`proofs-cpc/PathosProofsCpc/` and emitted by `scripts/proofgen` where a
program calls them; 820 of CPC's 1,103 programs have a generated proof
(746 at the start of milestone 6; 778 before `$eo_typeof`'s, which
brought 42: itself, `$eo_push_proven`, `$eo_is_bool_type` and the rules
and helpers that type their arguments).

- **Lists** (`Lists.lean`): `eo::list_len`, `list_rev`, `list_nth`,
  `list_find`, `list_erase`, `list_setof`, `list_singleton_elim`, and, for an
  operator with one nil (`UniqueNil`, see "`eo::list_concat` and the nils
  of an operator"), `list_concat`, `list_diff`, `list_inter` and
  `list_minclude` and `list_meq`. Each
  says the runtime's `list_parts`/`list_pair`, its walk over the handles,
  and `list_build` give logos's function.
- **The multiset table** (`Counts.lean`): `table::TermCounts`, the
  open-addressed table `list_setof`, `list_diff`, `list_inter` (and
  `list_meq`, `list_minclude`) count terms with, specified on the store
  table's `Path`: the invariant `TC`, `new`, `entry`, `add`, `count`,
  `remove_one`, and as a multiset (`TCList`), with `first_occurrences`,
  `multiset` and `multiset_select`.
- **Numbers** (`Arith.lean`): `eo::to_bin`, `eo::pow`, `eo::div`, `eo::mod`
  (numerals and binaries, with the conventions by zero), `eo::qdiv`; and
  (`Or.lean`) `eo::or`.

They rest only on the specs of `Trusted.lean` that `axioms-allowed.txt`
allows; `eo::or` brought `bitwise_or_spec` into use (32 assumptions, from
31). `$eo_typeof` is proved (above, "Large functions: `logos_eq_large`");
nine of the programs it had kept from being tried do not build, for the
reasons of the others (`proofs-cpc/unproved.toml`: a case's spec that
times out, a `logos_eq` that fails). What still blocks the most programs:
`eo::cmp` (the runtime's `Store::compare` against logos's `termCmp`);
`eo::concat` and `eo::extract` of binaries (above); the datatype operators
(the six with no logos function, a decision of milestone 8); and the
operators with several nils.

### `eo::cmp`

In three steps. First, generic (`Runtime/Compare.lean`, done): `compare`
computes `treeCmp` on the trees its two handles stand for, given the
constructors' arities (at most `A`, with `A ≤ 100`) and that their
`order_key` and `of_embedding` are total. Second, generated per
constructor: those facts for the checker's constructors, and
`treeCmp (enc x) (enc y) = termCmp x y` by induction on logos's terms.
Third, the builtin's spec, and the generator's support for it.

Decimal and hexadecimal literals never reach `compare`: `Store::literal`
normalizes them to rationals and binaries when it builds them, and `raw`
is only called with Boolean, numeral, rational and string values, so
`litCmp` does not order them (it gives `eq`, which no store reaches).

## What is trusted

`proofs/axioms-allowed.txt` is the list; `scripts/proofs-axioms` enforces
it, and sorts every axiom in use into one of two kinds (milestone 32,
step 5):

- **Assumptions**: axioms whose type is a proposition, and Lean's three.
  This is the trust. In use today, by 8,741 theorems, are **27**:
  `propext`, `Quot.sound`, `Classical.choice` (Lean's; choice is a
  function, `Nonempty α → α`, but it is the axiom of choice); 8 of
  `Trusted.lean` about the numbers themselves: `Integer` is ℤ and
  `Rational` is ℚ (`ofInt_toInt`, `toInt_ofInt`, `ofRat_toRat`,
  `toRat_ofRat`: the embedding's `dec_enc` uses `toInt (ofInt z) = z`),
  their `==` (`eq_spec`), and that their hash returns (`hash_code_spec`);
  and the specs of the integer functions that the proved programs reach
  (brought into use by Daniel's decision of 2026-11-20, group by group).
  Each states what a function of `num.rs` computes; `num.rs` wraps
  `malachite`'s integers and rationals in a thin layer (one line a
  function, e.g. `Integer(&self.0 + &y.0)`), which Aeneas cannot
  translate, so these say what that library computes:
  - the natural numbers (`nat.zero`, the patterns `nat.zero` and
    `nat.succ`, `Runtime/Nats.lean`): `Integer.zero_spec`, `one_spec`,
    `clone_spec`, `sgn_spec`, `add_spec`, `neg_spec`;
  - numeral and rational literals in patterns and built from values
    (`Runtime/Numbers.lean`): `Integer.clone_spec` (already in use) and
    `Rational.clone_spec`;
  - the integer natives (`zeq`, `zleq`, `mod_total`, `int.pow2`,
    `int.to_nat`, `nat.succ`) and the numeral constants of the generated
    code (`Runtime/IntNatives.lean`): `Integer.partial_cmp_spec`,
    `euclidean_qr_spec`, `fits_u32_spec`, `to_u32_spec`, `from_u32_spec`,
    `pow_spec` (and `eq_spec`, `sgn_spec`, `zero_spec`, `one_spec`,
    `add_spec`, `neg_spec`, `clone_spec`, already in use);
  - `eo::len` (`Runtime/Builtins.lean`): `Integer.from_usize_spec` (and
    `from_u32_spec`, already in use);
  - `eo::and` (`Runtime/Builtins.lean`): `Integer.bitwise_and_spec` and
    `mod_by_pow2_spec` (and `clone_spec`, `Rational.clone_spec`, already
    in use). logos computes the `and` of two binaries with
    `BitVec.toInt`, which is signed, and then reduces it modulo `2^w`;
    the runtime reduces malachite's `and` of the two values. They agree
    for every width and every pair of values in range
    (`bv_and_toInt_emod`, proved, not assumed).
- **Declarations**: axioms that declare a type or a function and say
  nothing of it: 44 of the 52 that Aeneas leaves without a body in the
  Lean of the checker (the types `num.Integer` and `num.Rational`, their
  functions, the printing functions), and `Trusted.lean`'s
  `toInt`, `ofInt`, `toRat`, `ofRat`. In use today: 48. An axiom whose
  type is not a proposition only says that its type has an element, and
  `Result α` always has one (`fail`), so a declaration adds no trust.

The declarations in use grow whenever a proof unfolds one of the runtime's
dispatchers, `native_op` or `builtin_core`: each is one `match` over all
its operations, so its equation names the functions of every operation,
and Lean counts every constant a proof refers to. The specifications of
step 5 take only the branch of their own operation (27 declarations in
use before them, 49 after). The audit fails if an axiom of the
`[MiniChecker]` or `[Aeneas]` sections is a proposition and in use: the
Lean of the checker and Aeneas's library are to declare, not to assume.
One of Aeneas's six is a proposition
(`Slice.get_unchecked_SliceIndexUsizeSlice_spec`); it is not in use.

No axiom of Aeneas's library is reached (it declares six), and none of
logos.

`Trusted.lean` gives every function of `num.rs` that the checker calls its
meaning on ℤ and ℚ, one equation each, with the hypothesis the Rust
documents where there is one (a non-zero divisor). Nothing of `front.rs`
is trusted any more: the checking code called one function of it,
`constant_name`, trusted only to return (`front.constant_name_spec`).
Since Ethos `cd4d38c` the name of a constant is built in `native.rs` from
its digits and proved (below, "The names of constants"), and
`constant_name_spec` and the declaration `front.constant_name` are gone
from `Trusted.lean`, the translation and `axioms-allowed.txt` (Daniel's
decision of 2026-11-20).

**The names of constants** (milestone 32, `Runtime/ConstNames.lean`).
logos's `native_uconst_id i` is `"@u." ++ toString i`.
- **The runtime:** `native::constant_name` builds the digits by repeated
  `euclidean_qr` by 10 and `to_u32` (`decimal_digits`, the last first),
  then the prefix (`@u.` or `@c.`), a `-` for a negative number (which
  the checker never asks for), and the digits back to front. A test
  checks it against `format!` for both prefixes, 0, small, large and
  negative numbers, so the strings are unchanged.
- **The one new error:** `CheckError::Limit` for a number with more than
  `usize::MAX - 8` digits. No memory holds such a number, and `format!`
  could not write it either; the bound keeps every push in range, which
  the proof needs (Aeneas makes a push past `usize::MAX` a failure, and
  the store's integers are unbounded).
- **The proof:** `digitsRev` and `toString_codes` relate the digits to
  `Nat.repr` (`toDigitsCore`, `digitChar`); the two loops are proved by
  fixpoint induction; `Store.native_spec_uconst_id` gives the line the
  emitter writes. It uses the specs of `euclidean_qr`, `to_u32`, `sgn`,
  `from_u32` and `clone`, all already in use.
- **Lemma C needs no `HasStuck SmtTerm`:** `__eo_to_smt` ends with
  `| y => SmtTerm.None`, a case that matches every value (the Rust has
  it too), so the no-case rule gives `default`. Checked with the force
  patch before the proof: lemma C and the body build.

**Literals are values** (milestone 32, Ethos `db074f2`). The generated
code builds every literal from a value, not from text. A numeral is
`Integer::from(<u32>)`, negated when negative (the specs of `from_u32`
and `neg`); a rational is `Rational::from_integers` of two such; a binary
is `BitVec::new` over one; a numeral or string constant of the EO
definitions is `s.raw` of such a value, or of `EoString::from_code_points`
of the code points the generator reads from the signature. So no parse,
no `NATIVE_TEXTS` lookup and no `native_literal` is on any path that a
proof reaches: every numeral of CpcMini and of the full CPC fits a `u32`
(20 distinct values in the CPC, at most 6 digits; a numeral that did not
fit would be built from 32-bit limbs with `mul` and `add`). The text and
parse paths are gone (milestone 32, Ethos `b8be4ea`): `parse_int`,
`parse_rat` and `native_literal` are removed from the runtime, and with
them the declaration `front.native_literal` and the assumption
`front.native_literal_spec` from `Trusted.lean` and
`axioms-allowed.txt`. What the generator can still write for a native
constant it cannot build as a value, `native_constant` and
`native_pattern_constant` (no signature has one today), now refuses it
with `UnsupportedNative`, the error `native_literal` gave for such a text.
`NATIVE_TEXTS` keeps the names that errors print (`UnsupportedNative`,
"SMT translation is unavailable"), so it is no gap for the final theorem:
no value the checker computes comes from it.

Beyond the axioms, the theorems are about a program under these
conditions:

- **`Platform64`**, a hypothesis of every theorem that reaches `intern`:
  `usize` has at least 40 bits. The table doubles with `len * 2`; with up
  to 2^32 terms that is 2^35 slots, more than a 32-bit `usize` counts.
  True of the six platforms pathos is built for.
- **Overflow checks.** Aeneas's Lean fails on arithmetic overflow; a
  release build without overflow checks wraps. `Cargo.toml` now builds the
  checker crate with `overflow-checks = true` in release, which costs
  nothing measurable (docs/aeneas.md, "Overflow"). Without it the theorems
  would be about another program than the binary.
- **Charon and Aeneas** are trusted to translate the Rust faithfully, and
  the Rust compiler to compile it.
- **The front end** (`crates/pathos`: the reading of the proof and the
  adapter that builds the checker's input) is outside, as logos's parser
  is outside logos's theorem.

## Findings

### Stuck terms under an application: logos and the Rust differ in three places

The store never has an application with a stuck argument: `apply` returns
the stuck term instead. logos's `Term.Apply f Stuck` is a term of its own.
Where logos builds an application, in CpcMini:

- **guarded**, like the Rust: `__eo_mk_apply`; `__eo_prog_refl` and the
  last case of `__mk_trans` (their own `Stuck` cases come first);
- **from matched subterms** of an input: `__mk_symm`;
- **not guarded**:
  1. `__eo_prog_scope`: `| F, (Proof.pf G) => (=> F G)`. On a proof of
     `Stuck` logos returns `(=> F Stuck)`; the Rust returns the stuck term.
  2. `__eo_typeof` of a datatype selector: `(-> D (…sel_return…))`, whose
     second argument is a program's result and can be `Stuck`.
  3. `__eo_cons`: `((f e) a)` under a `requires` that catches a stuck `a`
     but not a stuck `e`. `Store.builtin_spec_cons` therefore takes `e`
     not stuck, and the emitter writes it only where that is known; in
     CpcMini's one `eo::cons` (`$eo_mk_premise_list`) the element is a
     result of `$eo_state_proven_nth`, which an OK state never makes
     stuck (`state_proven_nth_ne_stuck`, "The state invariant").

So, function by function, "the Rust's result stands for logos's result" is
false for the whole checker. The statement has to be up to this: let
`norm x` be `Stuck` when `x` has a stuck argument somewhere under an
application, and `x` otherwise; the Rust computes `norm` of logos's result,
and **each logos function has to respect `norm`** (`f x` and `f (norm x)`
have the same `norm`). That is one more lemma per function on logos's
side, trivial where every pattern that looks under an application sends
`Stuck` there to `Stuck`, and a real difference where it fails.

**Guarded applications are matched one for one** (milestone 32). lean-meta
writes `__eo_mk_apply` exactly where an application is evaluatable (has a
program or builtin call under it, `lean_meta_reduce.cpp`), and a plain
`Term.Apply` elsewhere. The runtime's `apply` is `__eo_mk_apply`
(`Store.apply_mk_rep`), so the emitter now writes that lemma, with no
hypothesis that the parts are not stuck, wherever lean-meta wrote the
guarded form; a literal counts as not stuck. That proved
`$eo_lit_type_Binary` and, in the full CPC, cleared 36 of the 40 programs
that stopped there first (452 to 473 generated). What is left of this
kind is the function type of `$eo_typeof`'s selector case, which waits
on a question to lean-meta's author (see the handoff). The plain
`Term.Apply` on a variable bound under a proof (`$eo_prog_scope`, and in
the full CPC `$eo_prog_arith_trichotomy` and `$eo_prog_true_intro`) is
proved since the proof argument is assumed OK ("The state invariant"; 473
to 476 generated in the full CPC).

For the pilot none of this is assumed. The four programs' inputs are
handles, so they stand for terms without a stuck argument, and each
theorem shows that logos's result has a handle too. What is restricted is
which logos terms the statements speak about.

Two things that are **not** true or not known:

- "`__eo_typeof x = Bool` implies `x` has no stuck argument" is **false**
  for logos's CpcMini: `__eo_typeof (Apply List_cons x1)` ignores `x1`, so
  `(Apply (UConst 0 (-> (-> List List) Bool)) (Apply List_cons Stuck))` has
  type `Bool`. Such a term has no handle, so the hypothesis of the final
  theorem excludes it as input.
- Whether logos can build such a term itself from inputs that have none
  was not checked.

Can a verdict differ? Not through these three, by this argument (not a
proof): the possibly stuck term of 1 and 3 comes from the state, and a
term enters the state only when `__eo_is_bool_type` of it is `true`, which
it is not for `Stuck`; the consumers of the type of 2 answer `Stuck` or
`false` either way.

**What Ethos does** (the harness's build of `b8d65127`, and `pathos-eo`,
`pathos` and logos, on a `trans` step whose premises do not chain, alone
and as the premise of a `scope` or a `contra`): it stops at that step with
`Evaluation failed: (eo::requires b c …)`. A step whose rule does not
evaluate is an error there, so no stuck value goes on to a later step, and
Ethos agrees literally with neither logos nor the Rust, which carry
`Stuck` on and reject at the end. All four reject the proof. A selector
whose return type is stuck cannot be written in a proof.

The proof that was run, beside cvc5's CPC signature (`../cpc/Cpc.eo` as in
the harness's corpus):

```
(include "../cpc/Cpc.eo")
(declare-const a Bool) (declare-const b Bool)
(declare-const c Bool) (declare-const d Bool)
(assume @p1 (= a b))
(assume @p2 (= c d))
(assume @p6 (not (= a d)))
(step @p3 :rule trans :premises (@p1 @p2))
(step @p7 false :rule contra :premises (@p3 @p6))
```

Ethos and `pathos-eo`: `Evaluation failed: (eo::requires b c (_ (_ = a)
d))`. `pathos`: `A step of rule trans failed to check`, with the same
line. logos: `incorrect`, naming the `trans` step. The same with the last
line left out, and with `(assume-push @p4 e)` before the `trans` step and
`(step-pop @p5 :rule scope :premises (@p3))` after it.

### `eo::list_concat` and the nils of an operator

logos's `eo::list_concat f a b` asks only that each of `a` and `b` be a
list of `f`: that each ends in a term logos's `__eo_is_list_nil f` takes
for a nil. Then it puts the elements of `a` before `b`, whole. Ethos
takes one nil for the call: the operator's own, or the nil for the type
of `a` where it depends on a type (`type_checker.cpp`,
`evaluateNil`). It requires both lists to end in exactly that term. The
runtime requires the two ends to be the same term (`list_pair`). So
where the nil test takes several terms, logos concatenates two lists that
end in different nils, and Ethos and the runtime give the stuck term.
For example, a `str.++` list ending in `""` and one ending in
`(seq.empty String)`.

Operators where this happens, by logos's nil test:
- `str.++`: `""` and any `(seq.empty T)`;
- the bit-vector operators: by the value, so of any width, and the
  integer too;
- `+` and `*`: `0` and `0/1`, `1` and `1/1`;
- `@@TypedList.cons`: any `T`.

The others have one nil: `or`, `and`, `concat`, `re.++`, `re.inter`,
`re.union`, `$eo_List_cons`, `Tuple`, `tuple`, `@@poly`, `@from_bools`.

`Store.builtin_spec_list_concat` (proofs-cpc/PathosProofsCpc/Lists.lean)
is proved under `UniqueNil f`: two terms the nil test takes are one.
proofgen emits it only for an operator constant whose clause of
`__eo_is_list_nil` is a single closed pattern answering `true`
(`unique_nil_ops`). The calls on the other operators stay unproved,
with this as the reason. Daniel's decision (2026-11-24): leave them so,
and report the difference to logos. The runtime keeps Ethos's
behaviour.

### `eo::concat` and `eo::extract` of binaries: widths past 2^32

A binary's width is a `u32` in Ethos and the runtime. `eo::concat` of two
binaries adds their widths with wrapping (`BitVec::concat`,
`size.wrapping_add`), and `eo::extract` takes its count of bits modulo
2^32 too. logos adds them as integers: `__eo_concat` makes
`(Term.Binary (w1 + w2) …)` with `__eo_mk_binary`, whatever the sum. A
width of 2^32 or more is cheap to reach, since `eo::to_bin` makes a binary
of any width below 2^32 without its digits: `(eo::concat (eo::to_bin
4294967295 0) (eo::to_bin 1 0))` has width 0 in Ethos and the runtime,
and width 2^32 in logos. A store has no binary of that width (`okBv`), so
`eo::concat` and `eo::extract` of binaries have no spec stating logos's
result, and the programs calling them stay unproved. The difference is
logos's against Ethos's, like `eo::list_concat`'s nils, and is for
Daniel to take to logos.

### Equation lemmas of large functions

The generated `rust_eq` of a program unfolds logos's function, and Lean
makes the function's equation lemma then, in the module of the proof.
It makes it under the options of the `lean` command line (the import's
options; Lean's `realizeConst`), not those the module sets with
`set_option`, nor those of the module that defines the function. For
logos's `__eo_typeof` (209 cases), that takes about 30 s and more than
the default 200,000 heartbeats, so `proofs-cpc/lakefile.toml` passes
`-DmaxHeartbeats=2000000` to `CpcProofs`. The generated proofs no longer
unfold `__eo_typeof` (below), nor will they `__eo_cmd_step_proven`, which
is not recursive: its definition unfolds without a lemma.

### Large functions: `logos_eq_large`

`$eo_typeof`'s `rust_eq` (logos's function is the first of 208 cases that
answers, else stuck) did not build with `logos_eq`, which splits the
function's match and, in every branch, simplifies the whole list that
`firstSome` tries: quadratic, past `simp`'s `maxSteps` (100,000), and with
2,000,000 steps past the 2,000,000 heartbeats (it does not finish in 50
minutes without limits). `scripts/proofgen` now proves the `rust_eq` of a
program of 100 cases or more (`LARGE_CASES`; in CPC `$eo_typeof`, and
`$eo_cmd_step_proven` when what it calls is proved) with `logos_eq_large`
(`Tactic.lean`), and nothing unfolded first. The others keep `logos_eq`.

`logos_eq_large` is a proof by evaluation, with no `simp`, no `split` and
no equation lemma:

- It goes down the list of cases. A case that evaluates to `none` on the
  arguments is dropped (`firstSome_drop`), one that evaluates to `some v`
  ends the list with `v` (`firstSome_hit`), and one that does not evaluate,
  because its pattern matches on a variable, is kept (`firstSome_keep`).
  Each lemma's hypothesis is `rfl`.
- With cases kept, it takes cases of the variable that the first of them
  waits for (found by reducing the case's match to the recursor it is
  stuck on), and goes on in each branch, with the kept cases only.
- With none kept, the right side is a value: logos's function evaluates
  to it (`rfl`), or waits for a variable in turn, whose cases it takes.
- A test for the stuck term (`if x = Stuck then … else …`) is decided by
  evaluation, after cases of `x`.

For `$eo_typeof` that is 1,036 leaves, since the patterns are nested
(`Apply (Apply (UOp op) x) y`, with 170 operators). It fails, with the
term it waits for, on a case that matches on a number or a string (no
cases to take), and on a function with fall-through helpers (those keep
`logos_eq_deep`).

Measured (2026-11-25, the theorem alone, `-DmaxHeartbeats=2000000`):

| | `$eo_typeof` (209 cases) | `$eo_cmd_step_proven` (617 cases) |
|---|---|---|
| `logos_eq` | no end in 50 min (4 GB) | not tried |
| `unfold`, `split`, then `rfl` per branch, and the fall-throughs by the split's hypotheses | 110 s, 2.9 GB: 56 s for the equation lemma, 2 s `split`, 25 s `rfl`, 12 s the two fall-throughs | `split` times out (`isDefEq`, 2,000,000 heartbeats, 68 s); Lean had not made the match's equations after 13 min and 8.7 GB with no limit |
| `logos_eq_large` | 21 s, 2.1 GB: 8 s the tactic, 9.5 s the kernel | 484 s, 4.0 GB: 237 s the tactic, 223 s the kernel; 3,779 leaves |

In the build, the part of `CpcProofs` with `$eo_typeof` (490 theorems)
takes 86 s and 3.4 GB alone. With the 42 programs that `$eo_typeof`'s
proof brought, `scripts/proofs-build --cpc` has 43,833 theorems (38,624
before) and reaches its 8 GB cap with two Lean processes (5.7 GB before;
it passed, in 24 minutes on a machine busy with another build). The
largest part alone takes 4.8 GB.

The second row was the first tactic written here: in a fall-through
branch (a variable pattern after more specific ones, or the last one) an
earlier case answers `none` by the hypothesis that `split` leaves for its
pattern, one per case and in the cases' order, so linear. It closes
`$eo_typeof` but rests on Lean's splitter of logos's match, which Lean
does not make for 617 cases over three arguments; it is not kept.

**Does it scale to `$eo_cmd_step_proven`?** Yes, within the build's
limits, as measured on its statement written by hand (its proof is not
generated yet: it waits for `$eo_mk_premise_list`): 8 minutes and 4 GB
for the one theorem, under 2,000,000 heartbeats. The cost there is
probably cubic in the rules, not quadratic: in the branch of each of the
617 rules, each of the 617 cases is evaluated, and a case's match on an
enumeration is a recursor applied to one minor premise per constructor
(seen on `UserOp`, 170), which Lean instantiates each time. Should that
have to come down, the next step is one lemma per case (`r ≠ CRule.k →
case_k … = none`), so that a branch drops a case without evaluating it.
At 4 GB the theorem will not fit under the cap beside another part of
`CpcProofs` at its largest (4.8 GB): its part will have to build alone.

### The generator

- Clippy with warnings as errors fails on the CpcMini crate in one place:
  the generator assumes a left-associative operator (`is_left_assoc` with
  a single arm). (The other, `parse_int` unused, went with the text
  paths.) The tests pass.
- The Rust pipeline lacks the Lean pipeline's second trim, so six
  functions with no counterpart in logos's CpcMini stay.
- A cache entry's meaning (`EntryOK`) has a clause per cached program; for
  the whole checker it is a table from a program's number to what it
  computes, which the generator knows (`caches.tsv`).

### Aeneas's Lean library

Its `Result` is now an interaction tree, specifications are `spec` (total)
and `dspec` (partial), and a loop written as a recursive function
(`-loops-to-rec`) is proved by the induction principle Lean generates for
`partial_fixpoint`, with an admissibility side goal. Aeneas's own tactic
discharges it for a function of one argument; `Util.lean` has the lemmas
for two to five. A group of mutually recursive functions gives one
induction with a statement per function (`$mk_trans`: four). Each proof
file checks in seconds, since it imports the compiled runtime.

## How mechanical the program proofs are

Very, and in a way a generator could follow.

- A `case_i` function is specified by what it answers when its pattern
  matches (`Some` of a handle of the right-hand side, and the shape of the
  input) and when it does not (`None`, and the input is not of that
  shape). Its proof follows the generated code line by line: each store
  operation is one lemma of `Store/Sem.lean` (`unapply`, the construction
  of an operator, `apply`, the comparison of two handles), then a split on
  `Ok`/`Err`, carrying the invariant and the growth of the store.
- The body is "the first case that matches", proved against logos's
  definition by unfolding it and splitting.
- `Frame.lean` proves once that `enter`, body, `leave` is the body.
- A loop adds one induction, a recursive group one induction with a
  statement per function, a cached program the two cache lemmas.

Evidence that it is mechanical: the second case of `$mk_symm` (110 lines),
the recursive case of `$mk_trans` (90 lines) and the last two cases and
the step function of `$eo_state_is_closed` (180 lines) were written
without compiling and passed the first time. What made proofs fail was never the argument, always Lean's surface:
how a tuple pattern or a `let` is reduced, which lemma rewrites a bind,
a `simp` that hits a recursion limit.

The generator has what it needs to write each case's lemma and its proof:
it knows the pattern (so the shape on match and on no match), the
right-hand side (so the logos term), and the sequence of store operations
(so the sequence of lemmas). What it would need from us is a small tactic
that does the per-operation step (apply the lemma, split `Ok`/`Err`, carry
the invariant, transport the `Rep` facts to the new store): today that is
six to ten lines repeated after every operation, about four fifths of
every case proof.

How often a new runtime fact forces edits to finished proofs: adding the
cache to the store's invariant changed three lemmas (`intern_inv`,
`Inv.congr`, `new_spec`) and no program proof; widening `Extends` for the
cache changed two files by six lines. The program proofs only ever use
"the invariant holds" and "the store grew", so what the invariant says can
change under them.

## Generated proofs (milestone 32, stage 2: the state at the first checkpoint)

**Who writes them.** pathos's `scripts/proofgen` writes the proofs, from
what Ethos main `bde41a79` (cvc5/ethos#289) records of the code it
generated:
- rust-meta's trace of the generated code: per case, the nodes of its
  patterns and body, each with its Rust variable, and lean-meta's decision
  of a guarded application;
- lean-meta's table of the embedding's constructors;
- lean-meta's cases of the programs as Lean functions (`MiniCases.lean`).

What the generator knows of the checker's programs and types is in
`proofs/proofgen.toml`: the state, the programs that keep it OK, the types
with a trivial `Valid`, and the programs proved by hand.
`scripts/generate-cpc` and `scripts/generate-mini` run Ethos and then the
generator.

Its output is byte-identical to what rust-meta itself wrote during
milestone 32, on the Ethos fork's `m32-proofs`, which is no longer used.
The rest of this section says "rust-meta" or "the emitter" for the
generator of the proofs, as it was then.

The generator writes the proofs for the full CPC too, into
`generated/cpc-checker`
(`proofs.lean`, `proofs.tsv`, `cache_sem.lean`) and into `proofs-cpc/`,
where they are **built** under the axiom audit (`scripts/proofs-build
--cpc`, stage 5): **625 of 1,103** programs at the end of milestone 5,
with the same 27 assumptions as CpcMini. `proofs.tsv` gives each other
program the first thing it has no proof line for, or why its proof is
held back: `proofs-cpc/unproved.toml` lists the 24 whose generated proof
does not build, each with why. What is left is mostly arithmetic and the
list builtins. `eo::typeof` is supported, as a call of `$eo_typeof`, but
gains nothing yet: `$eo_typeof` calls `$eo_typeof_@from_bools`, which
uses `eo::add`, so the programs with `eo::typeof` wait on the arithmetic
of milestone 7 (the trust decision), not on anything cheap; the survey of
stage 5 counted it as cheap. The CPC is compiled from logos `bdcbd95f`, the
revision the proofs pin and the eoc gate uses (`LOGOS_REV`); before the
reference moved to Ethos `bde41a79` it was logos `a3232131`, with 478 of
1,086.
**76 of CpcMini's 82 programs (all 76 the gate counts)** have one, the four of the pilot among them; only the six datatype operators have none, the four of the pilot
among them; `generated/cpcmini-checker/proofs.tsv` lists every program
with `generated` or the first thing in it that the emitter has no line of
proof for yet. `proofs/MiniProofs.lean` (7,809 lines) elaborates in 16
seconds (3.0 GiB; `$smtx_typeof` adds about 2 s), `MiniCtors.lean` (169 lemmas) in 2 and `MiniEmbed.lean` in 5.

**Three generated pieces.**

- *The cases as functions* (`MiniCases.lean`, by lean-meta in the same run
  that writes logos's Lean). For each case of each program a function
  `EoCases.<program>.case_<i>` from the arguments to `Option` of the
  result: `some` of the right-hand side where the case's pattern matches,
  `none` where it does not. A pattern that uses a variable twice is
  written with fresh variables and a test that they are equal, which is
  what the Rust does with handles.
- *The proofs* (`MiniProofs.lean`, by rust-meta). The emitter records one
  line of proof with each line of Rust it writes. For a case: a theorem
  that the Rust function answers `Some` of a handle of what the case's
  function answers, or `None` where it answers `none`. For the body: that
  it gives logos's function, through the lemma below. For a tail-call
  loop: a round of it, and an induction over the rounds (below).
  For the program: the body between `enter` and `leave`, with its cache.
- *Lemma C*, per program: logos's function is the tests for the stuck term
  followed by the first case that answers (`<program>.rust_eq`). It is
  proved by unfolding both sides and splitting on the arguments
  (`logos_eq`). **It is never assumed**: a program whose lemma does not
  close is a program without a proof, and `scripts/proofs-axioms` checks
  the generated files as it does the others (no `sorry`, no axiom outside
  `axioms-allowed.txt`).

**Recursion.** Every call of a program goes through `enter`, which counts
depth against a limit. The theorems about cases and bodies assume what is
to be proved of every program (`Specs n`) for stores that can enter at
most `n` more calls; the theorem about a program proves it for `n` from
all smaller numbers; `specs` closes all programs together by one induction
on `n`. So programs that call each other need no induction of their own,
and the generator does not need to know which do. (Where `enter` refuses, at the limit, the program returns an error, of which the theorems say nothing: they are about runs that return, and an error is a return with nothing claimed.) (The pilot's proof of
`$mk_trans` was an induction over its four functions with a statement for
each.)

**Loops.** Loops are not calls, so `Specs n` does not cover them: each
loop has an induction of its own, on the budget of calls
(`Store.budget`: the limit of `calls` less the calls made, which `enter`
and `tick` count). Every round begins with `tick`, which fails at the
limit and otherwise uses up one call; no function raises the budget
again (it is a field of `Store.Grows`, which every operation's theorem
gives). So the round's theorem says, where the loop goes round again, that
the budget went down, and the loop's theorem is a strong induction on it
over the loop's unfolding equation. (The induction that Lean gives a
`partial_fixpoint` does not do: where a loop's round calls programs that
call back into the loop's program, as `$smtx_inhabited_type`'s does, Aeneas
puts the loop in one mutual block with them, and that block's induction
takes the programs it calls as unknown functions; `$smtx_inhabited_type`
and the four programs on its cycle are proved this way. The only reset of
`calls`, in `check_refutation_inner`, is the entry point's, before any
generated function runs.)

**Where logos and the Rust agree only on values a store can hold.**
logos's `__eo_prog_contra` is `requires (eo_eq F F') true false` where the
Rust compares two handles; the two differ on a proof of `(not Stuck)`,
which is a value of logos's type and of no store (`apply` never builds an
application of or to the stuck term). Lemma C therefore takes, for each
argument, that it is `Valid` (for a term: no application in it is of or to
the stuck term), and the body's proof gets that from the handle
(`Store.Rep.valid`). For a term, `Valid` is defined through the encoding
(`TermValid x = TreeValid (enc x)`), so it also holds in the indices of an
operator (`UOp1`, …, whose indices the encoding makes a node's fields),
for every calculus with the one definition: no application inside an
index is of or to the stuck term. An index may itself be the stuck term,
though: logos builds `(set.empty (eo::typeof a))` and
`(seq.empty (eo::typeof t))` (`Term.UOp1 UserOp1.set_empty (__eo_typeof
a)` in CPC's Lean), and `eo::typeof` of a term with no type is the stuck
term; the store holds such a node as it is (`construct` does not check a
node's fields, as `apply` does an application's, `TermData.Wf`), which is
logos's value. So `Valid` does not exclude it, and a program whose case
repeats a variable that is an index itself stays unproved
(`proofs-cpc/unproved.toml`).

**A latent hazard: repeated pattern variables on an index.** rust-meta
tests a repeated variable of a pattern with handle equality, where logos
uses `__eo_eq`, which is stuck if either side is. The two differ only when
a side can be the stuck term, which today is only an operator's index
(above). They are the same on every run now only because no logos program
builds an `update` or `tuple_update` term with a stuck index: the
repeated-variable tests of `$dt_updater_elim_rhs` and
`$tuple_updater_elim_rhs` compare such an index, and both programs stay
unproved for it (the reachability argument is in the milestone's notes,
`updater-index.md`). A change to rust-meta, testing a repeated variable
that can be an index as `__eo_eq` does, would make it sound by
construction; Daniel approved it, and it is queued after milestone 5
(not made here). This is the same boundary as the first finding below,
met from the other side. For the checker's other argument types (its
states, lists of commands, arguments and indices, rules; the datatype
declarations; the SMT types, datatypes and terms; commands; strings and naturals) `Valid`
is `True`: no case of a program over them tells apart values that no
store holds (they match data constructors, compare strings, pass values
on), and a term inside one of them is compared only as the argument of a
program over terms, whose own lemma C takes it `Valid`. The emitter lets
through exactly the types that have an instance (`Runtime/Embed.lean`
says why each is enough). `CCmd` and `SmtTerm` were added last, by the
same experiment (a `True` instance, the gate opened, the proofs forced):
lemma C closes for `$eo_invoke_cmd` and `$smtx_typeof`. The full CPC's
`Int` arguments have none yet; its programs over SMT terms pass the gate,
and lemma C closes for them in CPC's built proofs too (stage 5).

**Order of the stuck tests.** The Rust tests the arguments for the stuck
term in order, before any case; logos's function has a first match arm for
each. Lemma C states the Rust's order explicitly (`if x0 = Stuck then …
else if x1 = Stuck then … else firstSome […]`) and is proved against
logos's definition, so if the two orders could give different results the
lemma would not close. Inside a requirement the order is `a ≠ b` first,
then `a` stuck; both give the stuck term, and `requires_ite` (in
`Runtime/Ops.lean`) is where that is shown.

**Where no case applies.** The body then gives the stuck term (handle 0),
whatever the program's type. For a program that returns a term, a proof
or a native Boolean, lemma C gives the type's stuck value there
(`HasStuck.stuck`), and the body's proof shows that handle 0 stands for
it. For every other type (checker states, datatype declarations, SMT
types) lemma C gives `default` (every logos type is `Inhabited`), a value
the body never returns: logos writes no default case for such a type, so
its cases cover every value (a last case that matches anything, or one
case per constructor, which Lean checks), and the body's proof closes the
path by contradiction from the facts that every case answered `none`
(`body_stuck … splitting`, `round_stuck … splitting`; `split_none` splits
an argument into its constructors where the cases are one per
constructor). A native Boolean keeps its stuck value in lemma C, but its
body's proof closes the path the same way: handle 0 stands for no
Boolean. logos and the Rust agree on stuck tests for every type
(only a program that returns a term tests, and only its term arguments),
and the checker's state `CState.Stuck` is a node in the Rust as in logos
(`$emb_s.Stuck`), built and matched where logos builds and matches it. The
split over constructors is in the proofs of seven programs of CpcMini
(`$eo_dd_lookup`, `$eo_dt_resolve`, `$eo_dtc_resolve`, `$smtx_dd_has_dt`,
`$smtx_dd_lookup`, `$smtx_dt_resolve`, `$smtx_dtc_resolve`).

**The state invariant** (Ethos `d42bf81`). The store does not keep the
stuck term out of a state: `construct` checks nothing, and a handle can
stand for `pf Stuck` or for a state that holds `Stuck`. logos's functions
can, though: no builder of the checker puts a stuck formula into a state.
`Runtime/StateInv.lean` states that and proves it on logos's side only:

- `StateOK S`: no object of `S` holds the stuck term; `ProofOK p`: if
  `p` is `pf G`, then `G` is not stuck.
- `state_proven_nth_ne_stuck`: a premise looked up in an OK state is not
  stuck.
- Every function that builds a state keeps it: `StateOK.push_proven`,
  `.push_assume_check` and `.push_input_assume_check` in the guarded form
  the checker calls them in, `.invoke_cmd_check_proven`,
  `.invoke_cmd_step_pop`, `.invoke_cmd`, `.invoke_cmd_list` and
  `.invoke_assume_list`. With `.nil`, `.stuck` and `.tail`, these are
  enough for every state passed in CpcMini.

The generated specs assume the invariant, and every call proves it:

- **The spec's shape.** `<program>.Spec n` is the spec it was, with one
  more premise after the handle facts for each argument the program
  assumes OK: `StateOK x_ai →` for every state argument (by its type), and
  `ProofOK x_ai →` for a proof argument whose formula a case applies
  without logos's guard. The case, group, body and loop theorems take the
  same facts as `hg_ai`. The facts are about values, so no store carries
  them. `Specs n` still has one field per program, the induction is
  unchanged, and lemma C does not mention the invariant.
- **Which proof arguments.** The emitter decides while it writes a case's
  lines: the formula of a `$eo_pf` pattern on the argument, used in an
  application that logos writes as `Term.Apply`, gets
  `have hn_v := hg_ai _ rfl`. Only `$eo_prog_scope` does this in CpcMini.
  The rule is narrow by design: a `ProofOK` on every proof argument would
  oblige `$eo_prog_trans`'s caller to show that `__eo_mk_premise_list`
  is not stuck, which is not true for every operator.
- **Calls.** A call passes `(by good_tac)` for each argument its callee
  assumes OK. `good_tac` is `solve_by_elim` over the hypotheses and the
  lemmas above, or `ProofOK.pf` with `ns_tac`.
  - The callee's assumptions are known only once every program has been
    emitted, so the line holds a marker until the printer resolves it.
  - The emitter writes the proof only where it can name where the value
    comes from: an argument assumed OK, the tail of an OK state, the
    empty or stuck state, a builder applied to OK states, or `pf` of a
    term that is not stuck. Elsewhere the program gets a reason ("a state
    that may not be OK", "a proof that may not be OK") instead of a proof
    that does not build. No program of CpcMini or the CPC has one.
- **Loops.** A loop's next round assumes its states OK too: the round's
  theorem says so of the next arguments (`case_again … goods k`, by
  `good_tac`), and the loop's induction carries it. A loop with a
  `ProofOK` argument gets a reason; there is none.
- **A new non-stuck fact.** After a call of `$eo_state_proven_nth` on an
  OK state, `have hn_v := state_proven_nth_ne_stuck_of h_v (by good_tac)`
  says its result is not stuck, for the gate. This is what
  `$eo_mk_premise_list`'s `eo::cons` needed, which now waits only on
  `$eo_state_proven_nth`.
- **The hand-written fold** (`invoke_assume_list_spec`) assumes its state
  OK too, and carries it through every push of the unwind loop.

The emitted lines for a proof argument (`$eo_prog_scope`) and for states
(the tail in `$eo_invoke_cmd_check_proven`, a parameter and a builder's
result in `$eo_state_is_refutation`, the next round of
`$eo_state_is_closed`) build. So do the `$eo_state_proven_nth` fact and
`ProofOK` of `pf` of a looked-up premise, since `$eo_state_proven_nth` is
proved (`$eo_mk_premise_list`, `$eo_cmd_step_proven`,
`$eo_cmd_step_pop_proven`). The fold's application against the spec it
will have was checked in a throwaway module: it still waits on
`$eo_is_bool_type`.

**The state lookup** (milestone 32). The
generator compiles `$eo_state_proven_nth` to the runtime's
`Store::state_nth`, which finds the index-th object of a state list in
O(log n) steps with Myers's jump pointers, and to `$eo_StateObj_proven` on
it. `Runtime/StateNth.lean` proves `state_nth` against logos's recursive
definition (`Store.state_nth_spec`), and the program around it
(`state_proven_nth_spec`: `enter`, `state_nth`, `$eo_StateObj_proven` or
the literal `true`, `leave`), which the emitter writes the program's theorem
as an application of, as for the fold (Ethos `a30d58c`): for handles of a state `S` and an
index `n`, it gives the handle of an object `so` with
`__eo_state_proven_nth S n = __eo_StateObj_proven so`, or `none` where logos
gives `true`, or an error.
- It rests on the store's new invariant part `JumpsOK` (above), which
  `state_depth` keeps: each entry it writes, on its way back up, is the
  node's depth and either its tail or the tail's two jumps, which
  `jumpOK_two` shows stay within the depth.
- The specs are partial: an error satisfies them. So the budget that
  `state_nth` charges (the runtime charges what the walk would) needs no
  proof that it equals the walk's, only that the store grows
  (`Store.Grows`, whose budget never goes up).
- **`charge` and the runtime fix.** `charge` used to compute
  `self.calls += count` after a saturating test against `limits.calls`.
  With `limits.calls` at `u64::MAX` (what pathos-eoc's adapter sets,
  panics.md, `adapter.rs:140-142`) the test let a sum past `u64::MAX`
  through, and the addition overflowed. pathos builds with
  `overflow-checks = true` (Cargo.toml), so that is a panic in release
  too, and a failure in Aeneas's model. It takes about 2^64 calls, but the
  store's invariant could not rule it out. Daniel's decision (2026-11-20):
  fix the runtime. `charge` now assigns the saturating sum that it tested
  (Ethos `25e4ef7`), and `Store.charge_spec` and `state_nth_spec` need no
  hypothesis beyond the store's invariant.

**What is written by hand** (`proofs/PathosProofs/`):

| File | Lines | |
| --- | --- | --- |
| `Tactic.lean` | 941 | The tactics that generated lines are written in: one per kind of line of Rust (`store_step`, `pat_unapply`, `pat_destruct`, `pat_same`, `case_done`, `case_again` (with `goods k` for a loop over states), the three of a requirement, `stuck_check`, `case_step`, `body_stuck`, the four of a loop), of groups (in a body and in a loop's round) and conditionals, `pat_is_node`, `pat_native_zero` and `nat_no_match`, `pat_destruct_lit2` (a literal with two fields), `split_none` (no case answered, which cannot be), and `good_tac` (an argument the callee assumes OK, see "The state invariant"). |
| `Runtime/Frame.lean` | 140 | `enter`, `leave` (with what they do to the budget of calls), the measure of the induction over calls, a program around its body. |
| `Runtime/Embed.lean` | 152 | The stuck value of a type, `Valid` (`True` for every argument type but terms and proofs, and why), and that a handle stands only for valid terms and proofs. |
| `Runtime/Ops.lean` | 514 | `literal` and `native_bool` for Booleans, guarded applications (`apply_mk_rep`: `apply` is logos's `__eo_mk_apply`), `tick`, `__eo_requires` and `__eo_eq`, a cached program around its body (`framed_cached`, and `framed_type_cached` for the type cache). |
| `Runtime/Node.lean` | 143 | `construct` and `destruct` of any data constructor or variable (`$emb_Var`, which the runtime stores as a node the same way), over trees; `construct` of the stuck term (`$emb_Stuck`), which gives handle 0 (`Store.construct_stuck_spec`); `is_node`, which a function type in a pattern (`(-> T U)`, the applications `(FunType T) U`) tests its head with (`pat_is_node`). |
| `Runtime/Natives.lean` | 252 | What `native_op` gives for `teq`, `Teq`, `streq`, `and`, `or`, and `builtin_core` for `eo::eq`: on handles of the arguments, a handle of logos's native. The equalities compare handles, which is comparing values (`Represents.eq_iff`). |
| `Runtime/Strings.lean` | 297 | `not`, `string_valid` and `string_prefix_eq`: the two string operations are loops over the code points, proved by induction over the loop; a string the store can hold has code points below 2^32 (the embedding's `okStr`), so its code points are its characters. |
| `Runtime/Nats.lean` | 153 | The natural numbers: the constant `nat.zero`, and the patterns `nat.zero` (`pat_native_zero`) and `(nat.succ m)` (`pat_destruct_lit`), which store a numeral; from the trusted specs of `zero`, `one`, `clone`, `sgn`, `add` and `neg`. |
| `Runtime/Builtins.lean` | 730 | Builtin operators on literals: what every one needs (a literal's clone, `literal_of`, `literals` on one and two arguments, `any_stuck` on one, what a handle of a literal stands for), `eo::len` (`builtin_spec_len`: the width of a binary, the length of a string) and `eo::and` (`builtin_spec_and`: the `and` of two Booleans, of two binaries of the same width), through `Lit::evaluate`; and that logos's signed `and` of bit-vectors, reduced, is malachite's (`bv_and_toInt_emod`). |
| `Runtime/IntNatives.lean` | 283 | The native operations on integers (`zeq`, `zleq` through `partial_cmp`, `mod_total`, `int.pow2`, `int.to_nat`, `nat.succ`) and the numeral constants of the generated code (`Integer::from(<u32>)`, negated); from the trusted specs of the integer functions. |
| `Runtime/StateInv.lean` | 160 | The checker-state invariant, on logos's side only: `StateOK` (no object of a state holds `Stuck`) and `ProofOK`; a premise looked up in an OK state is not `Stuck` (`state_proven_nth_ne_stuck`, and `_of` a handle's fact, for the generated lines); and every state builder keeps it (the three push checks, `push_proven`, `invoke_cmd_check_proven`, `invoke_cmd_step_pop`, `invoke_cmd`, `invoke_cmd_list`, `invoke_assume_list`; `StateOK.nil`, `.stuck`, `.tail`). The generated specs take it as a precondition (see "The state invariant"). |
| `Runtime/StateNth.lean` | 1178 | `Store::state_nth`, the jump-pointer lookup that `$eo_state_proven_nth` is compiled to, against logos's recursive `__eo_state_proven_nth` (`Store.state_nth_spec`): the walk down a state list and back up, which fills the entries (`state_down_spec`, `state_up_…_spec`; the two copies of the way up that Aeneas makes are proved alike), the search for the node at a depth (`state_ancestor_spec`), the read of the index, `charge`, and the program (`state_proven_nth_spec`), which the generated proofs use. See "The state lookup". |
| `Runtime/ConstNames.lean` | 293 | The names of constants (`native::constant_name`, `uconst_id`): the runtime's digit loop and copy loop against `"@u." ++ toString i` (`digitsRev`, `toString_codes`, `native_uconst_id_codes`), and `Store.native_spec_uconst_id`, which the emitter writes the line of `uconst_id` from. See "The names of constants". |
| `Runtime/Compare.lean` | 872 | `eo::cmp`'s `Store::compare`, generically: the order it computes on the trees of two handles (`treeCmp`: constructors by `order_key`, then literals by `litCmp`, applications and the fields of nodes left to right) and `compare_spec`, that `compare` returns it. The stack is bounded (`Blocks`: at most `A * (M + 1)` pairs for `M` terms and largest arity `A ≤ 100`), so its pushes never overflow. The constructors' arities and that `order_key` and `of_embedding` are total are hypotheses, for generated lemmas to discharge; relating `treeCmp` to logos's `termCmp` is the next step. See "`eo::cmp`". |
| `Top.lean` | 506 | CpcMini's top-level theorem (`check_proof_correct`): `check_proof_inner`'s refutation (`check_refutation_inner`, with `calls = 0`), its side-condition checks (`has_translation`, `arguments_translate` and its loop, the loop over the commands) against logos's `TranslatableAssumptionList` and `CmdListTranslationOk`, and the composition with logos's `correct___eo_is_refutation`. See "The top-level theorem". |
| `Runtime/AssumeFold.lean` | 451 | `$eo_invoke_assume_list`, which the generator compiles to an iterative fold (`scan`, then `unwind`): proved by hand against logos's recursive definition (`invoke_assume_list_spec`), from what is proved of `$eo_is_bool_type`, `$eo_is_closed` and `$eo_push_input_assume_check` (hypotheses in the shape of the generated specs, the state assumed OK); the emitter writes the program's theorem as that application (`handProof`). |
| `Runtime/Lists.lean` | 624 | Lists of an operator: the runtime's walk down a list (`list_step_spec`, `list_elements_loop_spec`), its parts (`list_parts_spec`, which takes what is proved of the generated `$eo_is_list_nil` as a hypothesis, `IsListNilSpec n`, from the generated `Specs n`), building one again (`list_build_loop_spec`), and `eo::cons` (`Store.builtin_spec_cons`) against logos's `__eo_cons`, for operators that nest to the right. Meant for every list builtin. |
| `Runtime/StringLits.lean` | 455 | String and binary literals: a pattern on one stores a copy of its code points (`destruct_string_spec`, with `pat_destruct_lit`), `construct` from a native string gives the literal (`construct_string_spec`), and `raw` of a string in range (`raw_str_spec`); a string constant of the generated code (`"@"`: `raw` of `EoString::from_code_points(vec![64])`) stands for the code points of its vector (`raw_str_vec_spec`: a vector of `u32` is always in range), rewritten to logos's `native_string_lit` once both are concrete (`Represents.rep_of_eq`). `EoString`'s clone is translated code, so no trusted spec. A pattern on a binary literal stores its width and value as two numerals (`destruct_binary_spec`, with `pat_destruct_lit2`), and building it again from those two fields gives the literal (`construct_binary_spec`, in range by `rep_binary_okBv`), from the specs of `from_u32`, `clone`, `fits_u32`, `to_u32` and `mod_by_pow2`, already in use. |
| `Runtime/Numbers.lean` | 399 | Numeral and rational literals: a pattern on one stores a copy of its value (`destruct_numeral_spec`, `destruct_rational_spec`, with `pat_destruct_lit`), and `construct` from a native value gives the literal (`construct_numeral_spec`, `construct_rational_spec`); from the trusted specs of `clone`. |
| `Runtime/Literals.lean` | 122 | `destruct` with the Boolean literal's constructor, which stores a native copy of the Boolean: a pattern that changes the store (`pat_destruct_lit`). |

No generated proof has a line written by hand, and no program needed a
person. What needed a person is the above: a tactic for each kind of line,
and a lemma for each runtime operation and constructor a line names.

**All 76 are proved** (2026-11-21). The last eight (`$eo_typeof`,
`$eo_is_bool_type`, `$eo_push_proven`, `$eo_invoke_cmd_step_pop`,
`$eo_invoke_cmd`, `$eo_invoke_cmd_list`, `$eo_invoke_assume_list` with its
hand-written fold, and `$eo_checker_is_refutation`) waited on `$eo_typeof`'s
selector case.
- **The fix:** with cvc5/ethos#286 and cvc5/logos#521, a function type
  whose parts call a program is built with logos's guarded `__eo_mk_apply`,
  as the runtime's `apply` builds it. The emitter writes `apply_mk_rep`
  for it (Ethos fork `2a9bd4b`).
- **The other six** of the 82 are the datatype operators below, which
  have no logos function.

In the full CPC (484 of 1,103), `$eo_state_proven_nth` and
`$eo_cmd_step_pop_proven` are proved, and:
- `$eo_to_smt` is past `uconst_id` and stops at case 170 (the native
  operation `mk_rational`), with `$eo_to_smt_distinct`,
  `$eo_to_smt_distinct_pairs` and `$eo_to_smt_typed_list_elem_type`
  waiting on it;
- `$eo_mk_premise_list` stops at `eo::cons` with an operator that nests to
  the left (the CPC has some);
- `$eo_cmd_step_proven` stops at its case 556, a literal that is not a
  Boolean;
- `$eo_typeof` is past its selector case and stops at a call of
  `$eo_typeof_@from_bools`.

The CPC crate and its proofs are now generated from logos `bdcbd95f`,
which has #521, so the selector's type is guarded in both, as in CpcMini.
They are still not built (stage 5).

`$eo_prog_scope`'s application of a term that may be stuck (the first
finding below) is proved since its proof argument is assumed OK. The lemmas of `construct` and `destruct` are generated for
every data constructor (`MiniCtors`); the literal constructors are stored
otherwise and have none. The cache of results is stated for every
embedded type (`MiniCacheSem`).

**Groups of cases** (milestone 32, step 4). A program with more than four
cases tries them in groups (`cases_<d>_<g>`), and each group has a
theorem: it answers what the first of its cases that answers does (`∀ d,
firstSome [its cases] d = res`), or none of them answers. The body and
the enclosing groups split their list of cases around each member
(`firstSome (l₁ ++ l₂) d = firstSome l₁ (firstSome l₂ d)`). None of the 8
such programs of CpcMini has a proof yet, each for another reason; the
group proofs were checked by writing `$eo_typeof`'s (27 cases, groups of
groups) and `$eo_cmd_step_proven`'s with `sorry` for the cases that the
emitter cannot do: the groups and the body go through (4 s, 1.8 GiB). A
loop whose cases are in groups (`$smtx_inhabited_type`) has the same
theorems with a round's result: a group ends the loop with what its first
answering case gives, or names the next round's arguments, on which the
program has the same result (`∀ d, firstSome [its cases] d = f ys`); its
members are tried with `group_round_step` and, in the round,
`body_group_round_step`.

**Conditionals** (step 4). `eo::ite c a b` and the native `ite` are
functions of their own in the Rust (`if_k`), and the proof of each is a
statement proved in place, as a requirement's is: the function gives a
handle of logos's `__eo_ite` (or `native_ite`) of the condition and the
branches, with a bullet per branch (`Store.boolean_value_term`,
`_native` and the `ite` lemmas in `Runtime/Ops.lean`). None of the 10
programs that had a conditional has a proof yet: the condition of most is
a native operation (`streq`, `Teq`), which the emitter has no line for.
The proof was checked by forcing `$eo_to_smt_type`: two cases with a
native `ite` go through. No case of CpcMini can exercise `eo::ite` (its
one use, in `$eo_is_closed_rec`, is in a case with a variable in its
pattern).

**Six programs have no function in CpcMini's logos**: the datatype
operators (`$eo_dt_constructors`, `$eo_dt_selectors` and the four they
call). The runtime calls them for `eo::dt_constructors` and
`eo::dt_selectors`, so rust-meta always compiles them; no program of
CpcMini uses either operator, and lean-meta leaves them out. There is
nothing to prove them against there, and CpcMini counts 76 programs. This
is CpcMini's alone: the CPC's signature uses both operators, so logos
defines the six (`__eo_dt_constructors`, ...) and lean-meta writes their
cases. rust-meta marks them `datatype_operators_only` in either crate;
proofgen excludes such a program only where logos has no function of its
name, and proves the CPC's like any other. A call of either operator
(`builtin` `DtConstructors` / `DtSelectors` in the trace) is, in the Rust,
a call of the program, and proofgen proves it by that program's spec, as
it does `eo::typeof`.

**The alternative not taken: have rust-meta compile the linearized
program.** lean-meta makes a pattern linear before it prints (a variable
used twice becomes two and a `requires`, or an `ite` with a continuation
program where a later case could still apply), and rust-meta compiles the
pattern as written, with a comparison of handles. If rust-meta compiled
lean-meta's linear form, each Rust case would be a logos match arm, and
lemma C would be the identity. It would also change the Rust of every
program with such a pattern: a comparison that answers "no match" would
become the evaluation of `eo::requires` or `eo::ite` on terms, with a
program call for each continuation, so the change would have to be
measured on the 400 and the large proofs, and Ethos's rust-meta would
depend on the linearization pass. Reasoned, not measured: with the case
functions the Rust stays byte for byte what it is (checked:
`scripts/generate-mini` writes the same crate), and the difference is
confined to lemma C, which Lean proves per program.

## The top-level theorem

`proofs/PathosProofs/Top.lean` states and proves, for CpcMini:

```lean
theorem check_proof_correct
    (s : Store) (hinv : s.Inv) (h64 : Platform64) (a c : Term)
    (F : Eo.CArgList) (pf : Eo.CCmdList)
    (hF : Represents.rep s a F) (hpf : Represents.rep s c pf) (s' : Store)
    (hrun : Store.check_proof_inner s a c = ok (core.result.Result.Ok Verdict.Correct, s')) :
    eo_satisfiability (argListAssumes F) false
```

If the compiled checker says `Correct` on handles of the assumptions `F`
and the proof `pf`, then `F` is unsatisfiable as logos defines it.

**How.**
- `check_proof_inner` returns `Correct` only after three things:
  - its refutation (`check_refutation_inner`: `calls = 0`, then
    `$eo_checker_is_refutation`, then `is_native_true`) is true, which is
    `eo_is_refutation F pf`;
  - the assumptions translate (`arguments_translate`), which is
    `TranslatableAssumptionList F`;
  - every command passes the loop over the commands, which is
    `CmdListTranslationOk pf`: an `assume_push` formula translates, a
    step's arguments translate, nothing is asked of the others.
- `has_translation` is `__smtx_typeof (__eo_to_smt t) ≠ None`, through the
  proved `$eo_to_smt` and `$smtx_typeof`.
- logos's `correct___eo_is_refutation` (`CpcMini/Proofs/Checker.lean:865`)
  takes the three and concludes.
- No rule of CpcMini has an argument mask, so every argument is checked
  as a term; the full CPC's masks are not covered.

**It is unconditional** (2026-11-21).
- `check_proof_correct_of_spec` is the same theorem from any proof of
  `$eo_checker_is_refutation`'s spec, `CheckerIsRefutationSpec`.
- `check_proof_correct` gives it the generated one,
  `fun n => (specs n).eo__24eo_5fchecker_5fis_5frefutation`. That program
  is proved since cvc5/ethos#286 and cvc5/logos#521.
- So the theorem has no hypothesis beyond the store's invariant, the
  handles, the platform and the run.

**Its trust base.**
- **The 27 assumptions of "What is trusted"**, and only those:
  `#print axioms check_proof_correct` gives Lean's three and the 24 of
  `Trusted.lean` in use. Its other 47 axioms are declarations of the
  translation (`num`'s types and functions), which add no trust.
- **Charon and Aeneas:** that the Lean of the checker is the Rust's
  meaning.
- **logos's definitions** (`eo_satisfiability`, the SMT model, the
  checker's functions) and its proofs, at `bdcbd95f`. Its `correct___eo_is_refutation`
  rests on Lean's three axioms only.
- **The boundary**, unverified:
  - `Store::check_proof` runs `check_proof_inner` on a thread with a
    larger stack (`with_checker_stack`); both are in `front.rs`, which is
    not translated.
  - CpcMini has no front end: `crates/pathos` builds the full CPC's
    checker. So the theorem is about any store with the invariant and any
    handles that stand for some `F` and `pf`. For CPC, the front end
    (`crates/pathos/src/adapter.rs`) would have to give handles that stand
    for what the input file means.
- **Partial correctness:** a run that returns `Correct`. Other verdicts,
  errors and runs that do not return are not covered.
- **`Platform64`** (a 64-bit `usize`) is assumed, as in every spec.

## What is missing for the theorem

1. **The rest of the runtime.** Proved: the table, `intern`, the cache,
   `view`/`is_stuck`/`unapply`/`apply`, `construct`/`destruct` for data
   constructors, `literal` and `native_bool` for Booleans, `enter`/
   `leave`/`tick`. Not proved: the other embeddings of `construct` and
   `destruct` (literals from native fields, binaries, user operators with
   indices), the builtin operators (`lit.rs`: arithmetic, strings,
   bit-vectors, on the trusted numbers), the list operators, `state_nth`
   with its jump pointers, term comparison and its order, and for CPC the
   translation checks. (The type cache is now proved, with `$smtx_typeof`.)
2. **`Rep` for all of `Eo.Term`** and for the other embedded types
   (datatype declarations, the SMT terms, types and values of
   `$eo_to_smt`), with `norm` (above).
3. **Every program**, by generated proofs (7 of CpcMini's 82 so far, see
   above): CpcMini has 82 functions with 233 case functions; CPC has 1,086 with 2,975 case functions, 66 loops
   and 190 cached programs.
4. ~~The specification of `native_literal`~~: not needed, literals are
   values (above).
5. **The top**: for CpcMini, done (above, "The top-level theorem"),
   given `$eo_checker_is_refutation`'s spec. For CPC, `check_proof` with the
   translation checks against logos's `ApiChecks`, and the composition
   with `correct___logos_verdict`.
6. **The "respects `norm`" lemmas** on logos's side, and the answer to
   whether logos builds a stuck argument from clean inputs.

## An estimate

By hand the programs are out of reach: the pilot's nine case functions
took about 1,500 lines, so CPC's 2,975 would take on the order of 400,000.
With generated proofs the work is in three places:

- **The runtime, by hand**: the pilot proved roughly a fifth of it (by
  lines of Rust) in about 2,400 lines of Lean. The rest is larger per line
  where it computes (the builtin operators over ℤ and ℚ against logos's
  natives) and comparable where it is bookkeeping. Somewhere between 6,000
  and 12,000 more lines.
- **The generator and the tactic**: the step tactic, the emission of a
  lemma and a proof per case, per body, per loop, per recursive group and
  per cached program, and the Lean tables (the cache's
  meanings, `Rep` for every constructor). The pilot's four shapes cover
  what the generator emits; what is untried is scale: whether 3,000
  generated proofs elaborate in acceptable time (the Lean of CPC itself
  takes 15 minutes), and how many fail for a reason that needs a person.
- **logos's side**: the `norm` lemmas, one per function, and whatever the
  three unguarded sites turn out to need.

The pilot found no obstacle of principle. The two risks it leaves are the
scale of generated proofs, and `norm`: if some logos function does not
respect it, the Rust and logos differ there and one of them has to change.
