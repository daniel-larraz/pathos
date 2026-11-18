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
4096, unless given).

## The parts

| Part | Where | Proved later? |
| --- | --- | --- |
| The compiled checker: rules, typing, the state of assumptions and steps, the final test | `generated/cpc-checker` (crate `pathos-compiled-checker`) | That is the plan |
| The front end: lexer, parser, elaboration | `crates/pathos-syntax`, `-term`, `-check`, `-elab`, shared with `pathos-eo` | No, as logos's parser is not |
| The adapter: from the front end's terms and commands to the compiled checker's | `crates/pathos/src/adapter.rs` | No |

`generated/cpc-checker` is generated code and is never edited by hand.
`scripts/generate-cpc` writes it, from the commit of Ethos's main branch
that the script names and from logos's CPC at `LOGOS_REV`
(`install/defs/Cpc.cached.eo`); `generated/cpc-checker/GENERATED.md` records
both, and `scripts/generate-cpc --check` says whether the directory is what
those revisions generate. It is a Cargo workspace of its own, so pathos's
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
| A term with `lambda`, a rule logos leaves out (`trust`, the rules about `lambda`) | Parse error | Error: the checker for CPC has no symbol, or no rule, of that name |
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

## Comparing with logos

`scripts/compare-logos` runs `pathos` and logos on the harness's proofs
from a cvc5 built in safe mode and lists every proof on which the verdicts
differ; with `--perf` it also times `pathos-eo`, `pathos-eo` with a
snapshot, and Ethos. Every run is under a memory cap and a time limit.

## Measurements

On the development machine (Linux x86-64), with the checker generated from
Ethos's main branch at `b8d65127` and logos at `LOGOS_REV`. Each run under
an 8 GiB cap, one process at a time.

Only `pathos` was run for this pin (`scripts/compare-logos --perf --only
pathos`, and the same with `--large --timeout 300`). The rows of logos,
`pathos-eo` and Ethos (`c7d3db90`) are **the reviewer's runs of
2026-11-17, not rerun**: the same binaries, proofs, cap and time limit, but
timed by the harness's `timeit.py` in another session, so the times of
different rows are comparable only roughly. `pathos`'s times are sums of
times measured to 0.01 s, and most of its runs on the 400 take less than
that. `pathos --no-cache` was not rerun.

### The 400 proofs of the safe corpus (120 s per run)

| Checker | correct | incorrect | error | timeout | Time on the 380 proofs every checker decided | Largest peak memory |
| --- | --- | --- | --- | --- | --- | --- |
| `pathos` | 383 | 1 | 16 | 0 | 4.2 s | 0.19 GiB |
| logos (not rerun) | 378 | 2 | 15 | 5 | 197.0 s | 3.06 GiB |
| `pathos-eo` (not rerun) | 400 | 0 | 0 | 0 | 14.7 s | 0.02 GiB |
| `pathos-eo --snapshot` (not rerun) | 400 | 0 | 0 | 0 | 11.3 s | 0.02 GiB |
| Ethos (not rerun) | 400 | 0 | 0 | 0 | 19.4 s | 0.08 GiB |

`pathos`'s verdict on each of the 400 is the one it gave with the checker
of milestone 27 (`8d7f7c68`); over all 400 it takes 4.4 s, where it took
67.6 s on 376 of them then. Its slowest proofs are
`regress0__bv__bv-options4` (0.74 s; 10.4 s then),
`regress1__sets__setofsets-disequal` (0.36 s; 20.3 s then) and
`regress1__bv__fuzz18.smtv1` (0.32 s; 15.7 s then), and on none is it now
both twice as slow as `pathos-eo` and half a second slower. Most of logos's
197.0 s is one proof, `regress1__fmf__with-ind-104-core` (106.7 s).

`pathos` says `correct` on no proof that Ethos does not accept. It differs
from logos on six proofs:

| Proofs | logos | `pathos` | Why |
| --- | --- | --- | --- |
| `regress1__auflia__bug330`, `regress1__bvdiv2`, `regress1__bv__proj-issue438-prerewrite-fixed-point-original`, `regress1__datatypes__acyclicity-sr-ground096` | timeout | `correct`, each in under a second | The compiled checker caches types and program results; logos computes them again for each occurrence of a shared subterm. With the checker of milestone 27, `pathos --no-cache` ran out of time on these too. |
| `regress1__proofs__base-lfsc-treesize` | timeout | error | The proof uses `lambda`; logos does not get as far as refusing it. |
| `regress1__datatypes__dt-param-card4-unsat` | `incorrect` | `correct` | logos's parser leaves a term of the block `((Pair 2) (Color 0))` stuck ([cvc5/logos#510](https://github.com/cvc5/logos/issues/510)). Ethos accepts the proof. |

The 16 errors are the 16 proofs with `lambda`. The one `incorrect`, which
logos shares, is `regress1__quantifiers__RND_4_16`: both stop at
`(assume-push @p2020 ...)`, whose formula is a `forall` with a variable of
an outer quantifier free in it (`?y2`). The checker accepts only closed
formulas as assumptions; Ethos has no such condition and accepts the proof.

### The 41 large proofs of the safe corpus (300 s per run for `pathos`)

| Checker | correct | timeout | error | over the 8 GiB cap | Time on the 37 proofs both decided | Largest peak under the cap |
| --- | --- | --- | --- | --- | --- | --- |
| `pathos` | 37 | 0 | 3 | 1 | 110.2 s | 6.21 GiB |
| Ethos (not rerun) | 40 | 0 | 0 | 1 | 281.0 s | 2.51 GiB |

`pathos` says `correct` on no proof that Ethos does not accept, and gives
no other verdict on any of the 41: where it finishes, it agrees with Ethos.
With the checker of milestone 27 it finished 31, in 957.0 s; the seven
proofs it then ran out of 300 s on now take between 1.8 s and 18.0 s.

- **Time**: more than half of Ethos's total is one proof,
  `regress4__bug143.smtv1` (159.2 s; `pathos` 17.5 s). On the others the
  two are close: `regress4__comb2.shuffled-as.sat03-420.smtv1`, with
  112,463 assumptions, 37.9 s against 39.2 s; `regress3__hole9.cvc` 18.0 s
  against 34.2 s; `regress3__bv-fuzz17.smtv1` 9.2 s against 8.9 s.
- **Memory**: `pathos` uses two to three times what Ethos does on the
  largest proofs (`bug143` 6.21 GiB against 2.51 GiB, `comb2` 5.70 against
  2.15, `hole9` 5.61 against 2.47), so it is closer to the cap.
- **Errors**: `regress1__arith__issue9427-cdiv-def` uses `lambda`.
  `regress3__friedman_n4_i5.smtv1` and
  `regress4__C880mul.miter.shuffled-as.sat03-348.smtv1` end in `the
  compiled checker stopped without a verdict: Limit` at the default depth
  of 4096: they need `--depth=11493` and `--depth=9381` at least, and are
  `correct` with those (and with `--depth=1000000`, without overflowing
  the stack). Each has a single assumption; which function nests that deep
  was not looked into. With the limit of 100,000 that `pathos` set before
  this pin, both were `correct`.
- **`regress3__hole10.cvc`** (475 MB) fits under 8 GiB for neither. It was
  not run again under a larger cap; with the checker of milestone 27, alone
  under a 32 GiB cap with ten minutes, Ethos was `correct` in 435 s with a
  peak of 21.96 GiB and `pathos` was out of time at 12.70 GiB.

### The caches, and where the time went before

Measured with the checker of milestone 27 (`8d7f7c68`), not again: without
its caches `pathos` ran out of 120 s on eight of the 400 that took under a
second with them. What was then left, about 16 ms for each step of
`chain_m_resolution`, went on hashing and interning terms and native
numbers in the runtime; the runtime at `b8d65127` (case helpers, a
logarithmic premise lookup, the assumption list checked in a loop) no
longer shows it, as the times above say.
