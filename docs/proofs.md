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
| `proofs/pins.env` | The versions: Lean and Mathlib `v4.36.0`, Aeneas `1dc8ad31`, Charon `454586e9`, logos `a9944ea7` (cvc5/logos main, at Lean `v4.36.0` since cvc5/logos#518). |

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

## What is trusted

`proofs/axioms-allowed.txt` is the list; `scripts/proofs-axioms` enforces
it, and sorts every axiom in use into one of two kinds (milestone 32,
step 5):

- **Assumptions**: axioms whose type is a proposition, and Lean's three.
  This is the trust. In use today, by 5,933 theorems, are **27**:
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
  nothing of it: 45 of the 54 that Aeneas leaves without a body in the
  Lean of the checker (the types `num.Integer` and `num.Rational`, their
  functions, the text functions of `front.rs`), and `Trusted.lean`'s
  `toInt`, `ofInt`, `toRat`, `ofRat`. In use today: 49. An axiom whose
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
documents where there is one (a non-zero divisor). Of the two functions of
`front.rs` it declares (`native_literal`, `constant_name`) it assumes only
that they return.

**Literals are values** (milestone 32, Ethos `db074f2`). The generated
code builds every literal from a value, not from text. A numeral is
`Integer::from(<u32>)`, negated when negative (the specs of `from_u32`
and `neg`); a rational is `Rational::from_integers` of two such; a binary
is `BitVec::new` over one; a numeral or string constant of the EO
definitions is `s.raw` of such a value, or of `EoString::from_code_points`
of the code points the generator reads from the signature. So no parse,
no `NATIVE_TEXTS` lookup and no `native_literal` is on any path that a
proof reaches: every numeral of CpcMini and of the full CPC fits a `u32`
(20 distinct values in the CPC, at most 6 digits). `parse_int`,
`parse_rat` and `native_literal` stay in the runtime, unused by generated
code, until the specs `Trusted.lean` declares about them are retired. The
one text path the generator can still write is `native_pattern_constant`,
a native constant in a pattern (no signature uses one today): it reads
its value with `native_literal`. `NATIVE_TEXTS` keeps the names that
errors print (`UnsupportedNative`, "SMT translation is unavailable").

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
     but not a stuck `e`.

So, function by function, "the Rust's result stands for logos's result" is
false for the whole checker. The statement has to be up to this: let
`norm x` be `Stuck` when `x` has a stuck argument somewhere under an
application, and `x` otherwise; the Rust computes `norm` of logos's result,
and **each logos function has to respect `norm`** (`f x` and `f (norm x)`
have the same `norm`). That is one more lemma per function on logos's
side, trivial where every pattern that looks under an application sends
`Stuck` there to `Stuck`, and a real difference where it fails.

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

### The generator

- Clippy with warnings as errors fails on the CpcMini crate in three
  places: the generator assumes a numeral in the generated code
  (`parse_int` unused, now allowed to be: literals are values) and a
  left-associative operator
  (`is_left_assoc` with a single arm). The tests pass.
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

`rust-meta` writes the proofs with the Rust (Ethos branch `m32-proofs`).
For the full CPC it writes them too, into `generated/cpc-checker`
(`proofs.lean`, `proofs.tsv`, `cache_sem.lean`): they are generated and
checked to be what the generator writes (`scripts/generate-cpc --check`),
but **not built**; `proofs.tsv` (438 of 1,086 marked generated) says how
far the emitter gets.
60 of CpcMini's 82 programs (60 of the 76 the gate counts) have one so far, the four of the pilot
among them; `generated/cpcmini-checker/proofs.tsv` lists every program
with `generated` or the first thing in it that the emitter has no line of
proof for yet. `proofs/MiniProofs.lean` (6,134 lines) elaborates in 11
seconds (2.6 GiB), `MiniCtors.lean` (169 lemmas) in 2 and `MiniEmbed.lean` in 5.

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
(`Store.Rep.valid`). This is the same boundary as the first finding below,
met from the other side. For the checker's other argument types (its
states, lists of commands, arguments and indices, rules; the datatype
declarations; the SMT types and datatypes; strings and naturals) `Valid`
is `True`: no case of a program over them tells apart values that no
store holds (they match data constructors, compare strings, pass values
on), and a term inside one of them is compared only as the argument of a
program over terms, whose own lemma C takes it `Valid`. The emitter lets
through exactly the types that have an instance (`Runtime/Embed.lean`
says why each is enough); the full CPC's `SmtTerm` and `Int` arguments
have none yet.

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

**What is written by hand** (`proofs/PathosProofs/`):

| File | Lines | |
| --- | --- | --- |
| `Tactic.lean` | 861 | The tactics that generated lines are written in: one per kind of line of Rust (`store_step`, `pat_unapply`, `pat_destruct`, `pat_same`, `case_done`, `case_again`, the three of a requirement, `stuck_check`, `case_step`, `body_stuck`, the four of a loop), of groups (in a body and in a loop's round) and conditionals, `pat_is_node`, `pat_native_zero` and `nat_no_match`, and `split_none` (no case answered, which cannot be). |
| `Runtime/Frame.lean` | 140 | `enter`, `leave` (with what they do to the budget of calls), the measure of the induction over calls, a program around its body. |
| `Runtime/Embed.lean` | 143 | The stuck value of a type, `Valid` (`True` for every argument type but terms and proofs, and why), and that a handle stands only for valid terms and proofs. |
| `Runtime/Ops.lean` | 336 | `literal` and `native_bool` for Booleans, `tick`, `__eo_requires` and `__eo_eq`, a cached program around its body. |
| `Runtime/Node.lean` | 143 | `construct` and `destruct` of any data constructor or variable (`$emb_Var`, which the runtime stores as a node the same way), over trees; `construct` of the stuck term (`$emb_Stuck`), which gives handle 0 (`Store.construct_stuck_spec`); `is_node`, which a function type in a pattern (`(-> T U)`, the applications `(FunType T) U`) tests its head with (`pat_is_node`). |
| `Runtime/Natives.lean` | 252 | What `native_op` gives for `teq`, `Teq`, `streq`, `and`, `or`, and `builtin_core` for `eo::eq`: on handles of the arguments, a handle of logos's native. The equalities compare handles, which is comparing values (`Represents.eq_iff`). |
| `Runtime/Strings.lean` | 297 | `not`, `string_valid` and `string_prefix_eq`: the two string operations are loops over the code points, proved by induction over the loop; a string the store can hold has code points below 2^32 (the embedding's `okStr`), so its code points are its characters. |
| `Runtime/Nats.lean` | 153 | The natural numbers: the constant `nat.zero`, and the patterns `nat.zero` (`pat_native_zero`) and `(nat.succ m)` (`pat_destruct_lit`), which store a numeral; from the trusted specs of `zero`, `one`, `clone`, `sgn`, `add` and `neg`. |
| `Runtime/Builtins.lean` | 730 | Builtin operators on literals: what every one needs (a literal's clone, `literal_of`, `literals` on one and two arguments, `any_stuck` on one, what a handle of a literal stands for), `eo::len` (`builtin_spec_len`: the width of a binary, the length of a string) and `eo::and` (`builtin_spec_and`: the `and` of two Booleans, of two binaries of the same width), through `Lit::evaluate`; and that logos's signed `and` of bit-vectors, reduced, is malachite's (`bv_and_toInt_emod`). |
| `Runtime/IntNatives.lean` | 283 | The native operations on integers (`zeq`, `zleq` through `partial_cmp`, `mod_total`, `int.pow2`, `int.to_nat`, `nat.succ`) and the numeral constants of the generated code (`Integer::from(<u32>)`, negated); from the trusted specs of the integer functions. |
| `Runtime/StringLits.lean` | 264 | String literals: a pattern on one stores a copy of its code points (`destruct_string_spec`, with `pat_destruct_lit`), `construct` from a native string gives the literal (`construct_string_spec`), and `raw` of a string in range (`raw_str_spec`); a string constant of the generated code (`"@"`: `raw` of `EoString::from_code_points(vec![64])`) stands for the code points of its vector (`raw_str_vec_spec`: a vector of `u32` is always in range), rewritten to logos's `native_string_lit` once both are concrete (`Represents.rep_of_eq`). `EoString`'s clone is translated code, so no trusted spec. |
| `Runtime/Numbers.lean` | 399 | Numeral and rational literals: a pattern on one stores a copy of its value (`destruct_numeral_spec`, `destruct_rational_spec`, with `pat_destruct_lit`), and `construct` from a native value gives the literal (`construct_numeral_spec`, `construct_rational_spec`); from the trusted specs of `clone`. |
| `Runtime/Literals.lean` | 122 | `destruct` with the Boolean literal's constructor, which stores a native copy of the Boolean: a pattern that changes the store (`pat_destruct_lit`). |

No generated proof has a line written by hand, and no program needed a
person. What needed a person is the above: a tactic for each kind of line,
and a lemma for each runtime operation and constructor a line names.

**What limits the 60** (the reasons of `proofs.tsv`, for the other 22,
on 2026-11-20, after the string constants): calls of programs without a
proof (7); the six of the datatype operators below; a builtin operator
(1: `eo::cons`, in `$eo_mk_premise_list`); a binary literal in a pattern
(2, `$emb_Binary`, past the string literal patterns of `$eo_typeof` and
`$eo_to_smt`; the runtime stores the width and the value as two numerals,
with specs already in use); the two compiled to the runtime; two
applications of a term that may be stuck (`$eo_prog_scope`, the first
finding below, and `$eo_lit_type_Binary`, past `eo::len`); and `Valid`
for two types (`SmtTerm` for `$smtx_typeof`, `CCmd` for `$eo_invoke_cmd`;
no trust). The lemmas of `construct` and `destruct` are generated for
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

**Six programs have no function in logos's Lean**: the datatype operators
(`$eo_dt_constructors`, `$eo_dt_selectors` and the four they call). The
runtime calls them for `eo::dt_constructors` and `eo::dt_selectors`, so
rust-meta always compiles them; no program of CpcMini uses either
operator, and lean-meta leaves them out. There is nothing to prove them
against. For the gate they need a decision: count 76 programs, or show
that the checker never reaches them.

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

## What is missing for the theorem

1. **The rest of the runtime.** Proved: the table, `intern`, the cache,
   `view`/`is_stuck`/`unapply`/`apply`, `construct`/`destruct` for data
   constructors, `literal` and `native_bool` for Booleans, `enter`/
   `leave`/`tick`. Not proved: the other embeddings of `construct` and
   `destruct` (literals from native fields, binaries, user operators with
   indices), the builtin operators (`lit.rs`: arithmetic, strings,
   bit-vectors, on the trusted numbers), the list operators, `state_nth`
   with its jump pointers, term comparison and its order, the type caches
   (`$eo_typeof`, `$smtx_typeof`), and for CPC the translation checks.
2. **`Rep` for all of `Eo.Term`** and for the other embedded types
   (datatype declarations, the SMT terms, types and values of
   `$eo_to_smt`), with `norm` (above).
3. **Every program**, by generated proofs (7 of CpcMini's 82 so far, see
   above): CpcMini has 82 functions with 233 case functions; CPC has 1,086 with 2,975 case functions, 66 loops
   and 190 cached programs.
4. ~~The specification of `native_literal`~~: not needed, literals are
   values (above).
5. **The top**: `check_refutation` and, for CPC, `check_proof` with the
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
