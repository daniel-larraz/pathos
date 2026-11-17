# `pathos`: the checker for CPC

The repository builds two checkers.

- **`pathos-eo`** reads any Eunoia signature and checks proofs against it by
  interpreting the signature, as Ethos does. It is the binary the rest of
  the documentation is about, and the one compared with Ethos.
- **`pathos`** checks proofs in one calculus, CPC, the one cvc5 writes. Its
  rules are not interpreted: they are Rust code that Ethos's `rust-meta`
  stage compiles from CPC ([cvc5/ethos#274](https://github.com/cvc5/ethos/pull/274)).
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
pathos [--explain] [--no-cache] [--cache-stats] <proof.cpc>
```

## The parts

| Part | Where | Proved later? |
| --- | --- | --- |
| The compiled checker: rules, typing, the state of assumptions and steps, the final test | `generated/cpc-checker` (crate `pathos-compiled-checker`) | That is the plan |
| The front end: lexer, parser, elaboration | `crates/pathos-syntax`, `-term`, `-check`, `-elab`, shared with `pathos-eo` | No, as logos's parser is not |
| The adapter: from the front end's terms and commands to the compiled checker's | `crates/pathos/src/adapter.rs` | No |

`generated/cpc-checker` is generated code and is never edited by hand.
`scripts/generate-cpc` writes it, from the Ethos commit of the pull request
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

## What depends on the pull request

The adapter uses only what the stage's `README.md` documents under "Using
the artifact in Pathos": `Store::new` with `Limits`, `literal`, `raw`,
`boolean`, `apply`, `named`, `construct`, `Constructor::from_name`,
`arity` and `is_user`, `check_proof`, `Verdict`, and, for the measurements,
`set_caching` and `cache_stats`. It also relies on these conventions, which
a change of the pull request could break:

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
