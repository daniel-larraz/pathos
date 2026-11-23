# `pathos`: the checker for CPC

The repository builds two checkers.

- **`pathos-eo`** reads any Eunoia signature and checks proofs against it by
  interpreting the signature, as Ethos does. It is the binary the rest of
  the documentation is about, and the one compared with Ethos.
- **`pathos`** checks proofs in one calculus, CPC, the one cvc5 writes. Its
  rules are not interpreted: they are Rust code that Ethos's `rust-meta`
  stage compiles from CPC ([cvc5/ethos#274](https://github.com/cvc5/ethos/pull/274), merged into Ethos's main branch).
  The compiled code mirrors, function by function, the checker of
  [logos](https://github.com/cvc5/logos), which is proved sound in Lean. The
  plan is to prove that the compiled checker computes what logos's does, so
  that logos's theorem applies to `pathos`. Nothing of that is proved yet.

`pathos` takes one proof and, like logos, prints `correct` (exit status 0),
`incorrect` (1) or `incomplete` (2). A proof it cannot read is an error on
standard error, with status 1 and no verdict. `incomplete` means the proof
is a refutation, but of a problem outside the fragment logos's theorem
covers.

```
pathos [--explain] [--profile] [--no-cache] [--cache-stats] [--depth=N] <proof.cpc>
```

`--explain` says which command of an incorrect proof the checker does not
accept, `--profile` which rules its time goes to; `--no-cache` and
`--cache-stats` are for measuring the checker's caches; `--depth` sets
how deep the checker's functions may nest (the checker's own default,
16,384, unless given).

## The parts

| Part | Where | Proved later? |
| --- | --- | --- |
| The compiled checker: rules, typing, the state of assumptions and steps, the final test | `generated/cpc-checker` (crate `pathos-compiled-checker`) | That is the plan: Charon and Aeneas translate all of it to Lean that compiles ([aeneas.md](aeneas.md)); nothing is proved yet |
| The front end: lexer, parser, elaboration | `crates/pathos-syntax`, `-term`, `-check`, `-elab`, shared with `pathos-eo` | No, as logos's parser is not |
| The adapter: from the front end's terms and commands to the compiled checker's | `crates/pathos/src/adapter.rs` | No |

`generated/cpc-checker` is generated code and is never edited by hand.
`scripts/generate-cpc` writes it, from the commit of Ethos's main branch
that the script names and from logos's CPC at `LOGOS_REV`
(`install/defs/Cpc.cached.eo`); `generated/cpc-checker/GENERATED.md` records
both, and `scripts/generate-cpc --check` says whether the directory is what
those revisions generate. CI runs `scripts/generate-cpc --check --from-note`,
which regenerates the crate from the two commits `GENERATED.md` names (the
Ethos one looked for in cvc5/ethos, then in the harness's fork, where work
not yet merged upstream lives) and fails on any difference: every change to
the checker is a change to Ethos's generator or runtime, so it can go
upstream as it is. It is a Cargo workspace of its own, so pathos's
lints, formatting and tests do not apply to it; its dependencies are the
three `malachite` crates at the versions pathos pins.

## How a proof is checked

1. **CPC is built in.** `Cpc.cached.eo`, the signature the checker was
   compiled from, is in `generated/cpc-checker`. The build script of
   `crates/pathos` reads it once with the front end and stores the resulting
   state in the binary (`State::signature_image`), so a run starts from that
   state in about 3 ms. The proof's own `include` and `reference` commands
   are read and ignored, as in logos.
2. **The front end reads the proof** against that signature exactly as
   `pathos-eo` would: it resolves names and overloads, expands `define` and
   `let`, desugars applications by the operators' attributes, computes nil
   terminators, and types every term. An ill-typed or malformed proof is an
   error here, with Ethos's message.
3. **The adapter writes the checker's input.** It is a plugin of the front
   end (`pathos_elab::Plugin`). For each `assume` it converts the formula
   and adds it to the assumption list. For each `assume-push`, `step` and
   `step-pop` it adds a command to the command list; the rule programs of
   the interpreter are not run.
4. **`check_proof` runs once**, on the two lists, and gives the verdict.

### Terms

The front end's term, after its desugaring, is converted node by node,
without recursion (terms can be a million applications deep) and once per
distinct term.

| Front end | Compiled checker |
| --- | --- |
| A symbol of CPC | The constructor of that name (`Constructor::from_name`); the n-th symbol of a name is `$eoo_<name>.<n>`, as the compiler names it |
| `(f a b)`, curried | `Store::apply`, twice |
| An operator with indices, `(extract 3 1)`, `(_ is cons)`, `(as set.empty (Set Int))` | The constructor with its indices as fields |
| `true`, `5`, `3/2`, `"s"`, `#b01` | `boolean`, `numeral`, `literal`; decimals are rationals and hexadecimals are binary, as in logos |
| `Bool`, `Type`, `(-> A B)` | `$emb_Bool`, `$emb_Type`, `$emb_FunType` applied to `A` and `B` |
| A bound variable `(eo::var "x" T)` | `$emb_Var` |
| A constant the proof declares | `$emb_UConst` with a number and its type |
| A sort the proof declares, or an application of a sort constructor it declares | `$emb_USort` with a number |
| A datatype, a constructor, a selector | `$emb_DatatypeType`, `$emb_DtCons`, `$emb_DtSel` with the declaration of the whole block |

Constants and sorts are numbered from 1 in the order they are first used.
A block of datatypes is declared in the order logos's parser puts it in
(`productiveOrder`): the checker's translation to SMT finds a value of a
datatype only through the datatypes declared after it. A parametric
datatype is declared one instance at a time: `(List Int)` becomes a
datatype of its own, named `.par_<n>_List`, with the instances its fields
need; instances that need each other form one declaration. Which instance a
constructor belongs to follows from the type of its application; for a
selector, a tester or an updater, from the type of the term it is applied
to.

### Commands

| Proof | Command list |
| --- | --- |
| `(assume @a F)` | none: `F` joins the assumptions |
| `(assume-push @a F)` | `assume_push F` |
| `(step @p F :rule r :premises (...) :args (...))` | `step r args indices`, then `check_proven F` |
| `(step-pop @p F :rule r ...)` | `step_pop r args indices`, then `check_proven F` |

A premise is given to the checker as its distance from the top of the
checker's state. The adapter keeps the formulas of that state as the proof
goes and finds a premise by the formula it proves, the most recent one; two
entries with the same formula are the same premise to the checker. A
premise that is no longer in the state (it was proved inside a scope that a
`step-pop` closed) is an error.

`check_proven` makes the checker compare what the rule gives with what the
step states. A step without a stated conclusion is checked by the compiled
checker all the same; to know which formula it leaves in the state, the
adapter lets the interpreter compute it.

## Where `pathos` and logos read a proof differently

The aim is the same verdict, not the same terms: constants are numbered in
another order, premises may be found at another distance, and names that
logos keeps with their bars (`|x|`) are plain names here.

| Input | logos | `pathos` |
| --- | --- | --- |
| A rule logos leaves out (`trust`, the rules about `lambda`); with the CPC of logos `a3232131`, also a term with `lambda` | Parse error | Error: the checker for CPC has no symbol, or no rule, of that name |
| An `assume` after the first step | Parse error | Error, for the same reason: the checker takes the assumptions first |
| `set-info`, `set-option`, `declare-parameterized-const`, `program`, `define` with `:type` | Parse error | Read as Ethos reads them |
| An ill-typed term | Read; the checker rejects the step (`incorrect`) | Error from the front end, with Ethos's message |
| A use of a parametric datatype that logos's parser cannot resolve | The term is stuck: `incorrect` | Read, when the types determine the instance |
| A symbol the proof declares under the name of a CPC operator | Chosen by type | Chosen by Ethos's overloading |

## What depends on the stage

The adapter uses only what the stage's `README.md` documents under "Using
the artifact in Pathos": `Store::new` with `Limits`, `literal`, `raw`,
`boolean`, `apply`, `named`, `construct`, `Constructor::from_name`,
`arity` and `is_user`, `check_proof`, `Verdict`, and, for the measurements,
`set_caching` and `cache_stats`. It also relies on these conventions, which
a change of the stage could break:

- the names of the embedding's constructors (`$emb_Apply`, `$emb_UConst`,
  `$emb_cmd.step`, `$emb_al.cons`, `$emb_edd.cons`, ...) and their fields;
- a rule `a-b` being the constructor `$emb_r.a_b` (a test checks that no
  two rules of CPC then share one);
- the head of the assumption list being the assumption pushed last;
- a premise index counting from the top of the state.

`--explain` goes further: it calls the generated functions for
`$eo_invoke_assume_list`, `$eo_invoke_cmd` and `$eo_state_is_refutation`
one command at a time, to say which command the checker does not accept. It
is kept in `explain.rs`, apart from the adapter, and never decides a
verdict.

Since milestone 28 the crate is written for Charon and Aeneas
([aeneas.md](aeneas.md)): its generated functions are in modules
`generated::part0` to `part12`, still reached as `generated::f`, and the
literal's variants are `Lit::Boolean` and `Lit::Str`. `Store::named`,
`Constructor::from_name` and the other functions that work on names are
in its `front.rs`, which is not translated.

## Proofs that are not proofs

A proof is untrusted text, and `pathos` must answer any of it with a
verdict or an error. [panics.md](panics.md), in its section "pathos (the
CPC checker)", lists every place in `crates/pathos` that could panic and
why no proof or command line reaches it; `scripts/check-panics` keeps that
list tied to the commit it was made at. `scripts/fuzz-cpc` runs `pathos` on
mutated proofs of the harness's safe corpus and reports every run that ends
otherwise than in a verdict or an error. The generated checker is not part
of that audit.

One consequence for what `pathos` reads: a constructor, selector, tester or
updater of a parametric datatype used at an instance of another datatype,
such as `((_ is cons) b)` for `b` of type `(Box Int)`, is an error
(`... is used at the type ..., which is not an instance of its datatype`),
although CPC types it and Ethos accepts it: the checker's datatypes are
declared instance by instance, and that instance has no such member.

## Comparing with logos

`scripts/compare-logos` runs `pathos` and logos on the harness's proofs
from a cvc5 built in safe mode and lists every proof on which the verdicts
differ; with `--perf` it also times `pathos-eo`, `pathos-eo` with a
snapshot, and Ethos. Every run is under a memory cap and a time limit.

## Measurements

On the development machine (Linux x86-64, 20 cores), on 2026-11-18, with
the checker generated from Ethos `cc027fc` (branch `m28-aeneas` of the
fork: Ethos's main `e51f527c` with the generator and runtime of milestone
28) and logos at `LOGOS_REV`. One run of `scripts/compare-logos --perf`
for each corpus (the second with `--large --timeout 300`) ran all six
rows, each run of each checker under an 8 GiB cap, one process at a time;
the reports are `target/compare-logos/safe-all-m28.json` and
`large-all-m28.json`. Ethos is the harness's release build of `b8d65127`
(there is none of the current `REFERENCE_REV`; the checker's code is the
same). Times are sums of wall-clock times measured to 0.01 s, so within a
table they compare. Nothing else of this work ran at the same time, but
the times of the large proofs were about a tenth higher than in a run of
`pathos` alone an hour before (139.5 s for the 39 it decides, 150.5 s
here).

### The 400 proofs of the safe corpus (120 s per run)

| Checker | correct | incorrect | error | timeout | Time on the 376 proofs every checker decided | Time on all 400 | Largest peak memory |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `pathos` | 383 | 1 | 16 | 0 | 10.1 s | 10.8 s | 0.09 GiB |
| logos | 377 | 2 | 15 | 6 | 26.8 s | 880.9 s | 3.06 GiB |
| `pathos --no-cache` | 375 | 1 | 16 | 8 | 124.1 s | 1084.3 s | 0.08 GiB |
| `pathos-eo` | 400 | 0 | 0 | 0 | 16.9 s | 18.7 s | 0.02 GiB |
| `pathos-eo --snapshot` | 400 | 0 | 0 | 0 | 9.6 s | 10.9 s | 0.02 GiB |
| Ethos | 400 | 0 | 0 | 0 | 28.7 s | 31.6 s | 0.08 GiB |

`pathos`'s verdict on each of the 400 is the one it gave before milestone
28 (`target/compare-logos/safe-pathos-d83d2ab6.json`). Most of its time is
starting: a run on a small proof takes about 25 ms. Its slowest proofs are
`regress0__bv__bv-options4` (0.86 s; `pathos-eo` 1.12 s, Ethos 1.90 s),
`regress1__sets__setofsets-disequal` (0.52 s) and
`regress1__bv__fuzz18.smtv1` (0.40 s), and on none is it both twice as
slow as `pathos-eo` and half a second slower.

`pathos` says `correct` on no proof that Ethos does not accept. It differs
from logos on seven proofs:

| Proofs | logos | `pathos` | Why |
| --- | --- | --- | --- |
| `regress1__auflia__bug330`, `regress1__bvdiv2`, `regress1__bv__proj-issue438-prerewrite-fixed-point-original`, `regress1__datatypes__acyclicity-sr-ground096`, `regress1__fmf__with-ind-104-core` | timeout | `correct`, each in under 0.2 s | The compiled checker caches types and program results; logos computes them again for each occurrence of a shared subterm. `pathos --no-cache` runs out of time on all five too. (`with-ind-104-core` took logos 106.7 s on 2026-11-17, under the limit.) |
| `regress1__proofs__base-lfsc-treesize` | timeout | error | The proof uses `lambda`; logos does not get as far as refusing it. |
| `regress1__datatypes__dt-param-card4-unsat` | `incorrect` | `correct` | logos's parser leaves a term of the block `((Pair 2) (Color 0))` stuck ([cvc5/logos#510](https://github.com/cvc5/logos/issues/510)). Ethos accepts the proof. |

The 16 errors are the 16 proofs with `lambda`. (These figures are with the
CPC of logos `a3232131`. Since logos `bdcbd95f` (#517, #519), the CPC the
checker is compiled from translates `lambda`, and `pathos` checks a term
with `lambda` rather than refusing it; the corpus has not been run again
with it.) The one `incorrect`, which
logos shares, is `regress1__quantifiers__RND_4_16`: both stop at
`(assume-push @p2020 ...)`, whose formula is a `forall` with a variable of
an outer quantifier free in it (`?y2`). The checker accepts only closed
formulas as assumptions; Ethos has no such condition and accepts the proof.

### The 41 large proofs of the safe corpus (300 s per run)

| Checker | correct | timeout | error | over the 8 GiB cap | Time on the 30 proofs every checker decided | Time on the 40 that `pathos`, `pathos-eo` and Ethos decide | Largest peak under the cap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `pathos` | 39 | 0 | 1 | 1 | 28.3 s | 150.5 s | 2.74 GiB |
| logos | 30 | 9 | 1 | 1 | 544.6 s | | 2.70 GiB |
| `pathos --no-cache` | 33 | 6 | 1 | 1 | 468.6 s | | 2.51 GiB |
| `pathos-eo` | 40 | 1 | 0 | 0 | 29.7 s | 255.0 s | 3.64 GiB |
| `pathos-eo --snapshot` | 40 | 1 | 0 | 0 | 29.4 s | 255.2 s | 3.64 GiB |
| Ethos | 40 | 0 | 0 | 1 | 60.6 s | 564.6 s | 2.52 GiB |

`pathos` says `correct` on no proof that Ethos does not accept, and gives
no other verdict on any of the 41: where it finishes, it agrees with Ethos.
(The peaks of `pathos-eo` are on `hole10`, which it does not finish; on the
proofs it finishes its largest is 0.47 GiB.)

- **Time**: half of Ethos's total is one proof, `regress4__bug143.smtv1`
  (287.2 s; `pathos-eo` 125.4 s; `pathos` 24.3 s). On
  `regress4__comb2.shuffled-as.sat03-420.smtv1`, with 112,463 assumptions,
  `pathos` takes 47.0 s, `pathos-eo` 41.4 s and Ethos 91.2 s; on
  `regress3__hole9.cvc` 24.0 s, 33.4 s and 73.3 s; on
  `regress3__bv-fuzz17.smtv1` 10.8 s, 10.0 s and 18.3 s.
- **logos** runs out of 300 s on nine proofs that `pathos` finishes, in
  between 0.2 s and 47 s; `pathos --no-cache` runs out of time on six of
  the nine.
- **Memory**: `pathos` now uses about what Ethos does on the largest
  proofs (`hole9` 2.74 GiB against 2.47, `comb2` 2.71 against 2.15,
  `bug143` 2.65 against 2.52), where before milestone 28 it used two to
  three times that (6.21 GiB on `bug143`).
- **Errors**: `regress1__arith__issue9427-cdiv-def` uses `lambda`.
  It is the only error. `regress3__friedman_n4_i5.smtv1` and
  `regress4__C880mul.miter.shuffled-as.sat03-348.smtv1` need a depth of
  11,493 and 9,381 at least, under the default of 16,384 (1.6 s and 2.3 s,
  with peaks of 0.12 GiB and 0.18 GiB). Each has a single assumption;
  which function nests that deep was not looked into.
- **`regress3__hole10.cvc`** (475 MB) fits under 8 GiB for neither `pathos`
  nor Ethos, and `pathos-eo` runs out of 300 s on it at 3.64 GiB. It was
  not run again under a larger cap; with the checker of milestone 27, alone
  under a 32 GiB cap with ten minutes, Ethos was `correct` in 435 s with a
  peak of 21.96 GiB and `pathos` was out of time at 12.70 GiB.

### Before and after milestone 28

Milestone 28 rewrote the generator and the runtime so that Charon and
Aeneas translate the checker ([aeneas.md](aeneas.md)). `pathos` built
before it (main at `565c786`, the checker from Ethos `d83d2ab6` with
#277) and after it were timed in turn, three times each on the 400 and
once on the large proofs, `pathos` alone on the machine
(`scripts/compare-logos --perf --only pathos`):

| | Before | After |
| --- | --- | --- |
| The 400, all runs | 12.5 s, 12.3 s, 12.0 s | 9.5 s, 9.3 s, 9.3 s |
| The 39 large proofs it decides | 211 s | 139.5 s |
| Largest peak memory under the cap | 6.21 GiB | 2.74 GiB |
| Building `pathos` (release) | 63 s | 24 to 28 s |

Every verdict is the same. The memory is mostly the runtime's own table
of terms, which replaced a hash map of boxed terms; the build is faster
because the generated functions are smaller and in thirteen modules.

### The caches

Without its caches of types and of program results `pathos` runs out of
120 s on eight of the 400, each of which takes under a second with them,
and out of 300 s on six of the large proofs; on the proofs every checker
decides it takes twelve times as long on the 400 and seventeen times on
the large ones.
