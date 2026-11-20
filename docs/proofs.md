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
| `proofs/PathosProofs/` | The proofs: 4,400 lines, 1,120 theorems (Lean counts the auxiliary ones). |
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
- **Handles and logos's terms** (`Rep.lean`). `Rep nodes t x`: the handle
  `t` stands for the CpcMini term `x`. A handle stands for at most one term
  (`Rep.functional`), a term has at most one handle (`Rep.injective`, from
  "no two handles have the same data"), and both survive the store growing
  (`Rep.mono`). Both directions matter: the generated code chooses a case
  by comparing handles, and `Store.Rep.eq_iff` says that is comparing
  terms. `Rep` covers the stuck term, the operators, applications and
  Booleans; numerals, strings, variables and datatypes are embedded the
  same way and are not written out.
- **The cache of program results** (`Cache.lean`, `CacheOps.lean`). Its
  table's operations do not panic and keep it well formed; what `get`
  answers is the result of an entry with that program and those arguments;
  `insert` adds the entry for what it is given, or nothing. **That `get`
  finds every entry is not proved, and not needed**: a cache that misses
  is slower, not wrong. `CacheInv`, part of the store's invariant: every
  entry is its program's result on what its arguments stand for.

### Four programs (`Programs/`)

| Program | Shape | Theorem | Lines |
| --- | --- | --- | --- |
| `$mk_symm` | not recursive, two cases | `eo__24mk_5fsymm_spec` | 331 |
| `$eo_prog_contra` | nonlinear pattern: proofs of `F` and `(not F)` | `eo__24eo_5fprog_5fcontra_spec` | 252 |
| `$mk_trans` | recursive, cached (and nonlinear) | `eo__24mk_5ftrans_spec` | 483 |
| `$eo_state_is_closed` | compiled to a loop | `eo__24eo_5fstate_5fis_5fclosed_spec` | 471 |

Each says: on a store with the invariant and handles that stand for the
arguments, the generated program, if it returns, has not panicked, leaves a
store with the invariant in which every earlier handle stands for what it
did, and returns a handle of what logos's definition gives (or an error).

## What is trusted

`proofs/axioms-allowed.txt` is the list; `scripts/proofs-axioms` enforces
it. In use today, by 1,120 theorems, are 25 axioms:

- Lean's three (`propext`, `Quot.sound`, `Classical.choice`).
- 12 of the 54 declarations that Aeneas leaves without a body in the Lean
  of the checker (the types `num.Integer` and `num.Rational` and some of
  their functions).
- 10 of the 52 axioms of `Trusted.lean`: `Integer` is ℤ and `Rational` is ℚ
  (`toInt`/`ofInt`, `toRat`/`ofRat`), their `==`, and that their hash
  returns.

No axiom of Aeneas's library is reached (it declares six), and none of
logos.

`Trusted.lean` gives every function of `num.rs` that the checker calls its
meaning on ℤ and ℚ, one equation each, with the hypothesis the Rust
documents where there is one (a non-zero divisor). Of the two functions of
`front.rs` that CpcMini's checker calls (`native_literal`,
`constant_name`) it assumes only that they return. **That is not enough
for the final theorem**: a literal of the generated code must stand for
logos's constant, so `native_literal` needs its specification, and that
needs the generated list `NATIVE_TEXTS` as a Lean table, which the
generator would have to write.

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
  (`parse_int` unused) and a left-associative operator
  (`is_left_assoc` with a single arm). The tests pass.
- The Rust pipeline lacks the Lean pipeline's second trim, so six
  functions with no counterpart in logos's CpcMini stay.
- `NATIVE_TEXTS` as a Lean table, for `native_literal` (above).
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
3. **Every program**, by generated proofs: CpcMini has 82 functions with
   233 case functions; CPC has 1,086 with 2,975 case functions, 66 loops
   and 190 cached programs.
4. **The specification of `native_literal`** and the table it needs.
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
  per cached program, and the Lean tables (`NATIVE_TEXTS`, the cache's
  meanings, `Rep` for every constructor). The pilot's four shapes cover
  what the generator emits; what is untried is scale: whether 3,000
  generated proofs elaborate in acceptable time (the Lean of CPC itself
  takes 15 minutes), and how many fail for a reason that needs a person.
- **logos's side**: the `norm` lemmas, one per function, and whatever the
  three unguarded sites turn out to need.

The pilot found no obstacle of principle. The two risks it leaves are the
scale of generated proofs, and `norm`: if some logos function does not
respect it, the Rust and logos differ there and one of them has to change.
