# Milestone 32: where the work stands

Rewritten on 2026-11-21 for whoever continues (Fable, the week after).
Start here; [proofs.md](proofs.md), "Generated proofs", "What is trusted"
and "The top-level theorem", has the report. Everything is on pathos `m32`
and upstream Ethos. pathos pins the Ethos commit in `scripts/generate-cpc`
(`default_rev`, `mini_default_rev`): Ethos main `bde41a79`, cvc5/ethos#289.
- The proofs are written by pathos's `scripts/proofgen`, from the trace of
  the generated code that Ethos writes, with `proofs/proofgen.toml` for
  what it knows of logos's checker.
- The Ethos fork's `m32-proofs`, where rust-meta wrote the proofs itself,
  is no longer used. The generated proofs are byte-identical to what it
  wrote.

## Done for CpcMini

- **All 76 programs the gate counts have generated proofs** (76 of 82;
  the six datatype operators have no logos function). They are listed in
  `generated/cpcmini-checker/proofs.tsv`.
- **The top-level theorem is proved and unconditional:**
  `check_proof_correct`, `proofs/PathosProofs/Top.lean`.
  - If `check_proof_inner` says `Correct` on handles of `F` and `pf`, in a
    store with the invariant on a 64-bit platform, then `F` is
    unsatisfiable as logos defines it, through logos's
    `correct___eo_is_refutation`.
  - Its boundary: it is about `check_proof_inner` (`with_checker_stack`
    and `front.rs` are untranslated); CpcMini has no front end; it is
    partial correctness.
  - `check_proof_correct_of_spec` is the same from any proof of
    `$eo_checker_is_refutation`'s spec.
- **Trust:** 27 assumptions (Lean's three, the 24 specs of `Trusted.lean`
  in use) and 48 declarations, which add no trust. `#print axioms
  check_proof_correct` is the 27 and 47 declarations. Theorems: see
  `scripts/proofs-axioms`.
- **Revisions:**
  - logos `bdcbd95f` for the proofs (`LOGOS_PROOFS_REV`, and
    `mini_logos_rev` for CpcMini's crate), which is cvc5/logos#521:
    function types guarded;
  - Ethos main `bde41a79` (cvc5/ethos#289: rust-meta's trace and
    lean-meta's case functions and embedding table), with pathos's
    `scripts/proofgen` writing the proofs. Before it, the fork's
    `m32-proofs` at `2a9bd4b` wrote them.
- **What got it there in milestone 32**, each with its section in
  proofs.md:
  - generated proofs, with groups of cases and loops by induction on the
    budget;
  - guarded applications;
  - `eo::cons`;
  - the assumption fold by hand;
  - the state invariant (`StateOK`, `ProofOK`);
  - the jump-pointer lookup (`JumpsOK`), with `charge` fixed;
  - the names of constants proved (`constant_name_spec` no longer
    trusted);
  - function types guarded.
- **Rust:** the generated code builds literals as values (Ethos
  `db074f2`); the runtime has no text parsing; `charge` assigns the sum it
  tested (`25e4ef7`); `constant_name` is built from its digits
  (`cd4d38c`). Each passed difftest. Taking m32 to main means taking these
  rust-meta changes upstream to cvc5/ethos first.
- **Build:** MiniProofs and `Top.lean` elaborate in seconds (see
  proofs.md); a clean `scripts/proofs-build` takes about 2 minutes.

## What remains

1. **Stage 5, the full CPC** (478 of its 1,086 programs generated; see
   "Stage 5" below and `~/Projects/cvc5/pathos-m28/work/cpc-proofs-measure.md`).
   - Its proofs are not built. Hand-written lemmas that enumerate the
     calculus (`Store/Rep.lean`'s `uopCtor`, `cases op <;> rfl`) run out of
     memory at the CPC's 1,062 constructors and must be generated or
     reproved.
   - Its first remaining reasons:
     - `$eo_to_smt` at case 169 (`mk_rational`);
     - `$eo_mk_premise_list` at `eo::cons` with a left-nested operator;
     - `$eo_cmd_step_proven` at case 550 (a non-Boolean literal);
     - `$eo_typeof` at a call of `$eo_typeof_@from_bools`;
     - `$smtx_typeof` at `$smtx_typeof_bv_op_2`.
   - A top-level theorem for CPC also needs the argument masks (`ArgKind`
     against logos's `ArgTranslationKind`), CPC's command kinds, and a
     statement about the front end (`crates/pathos/src/adapter.rs`).
2. **The harness's revisions** (`difftest.env`: `LOGOS_REV a3232131`,
   `REFERENCE_REV e51f527c`): Daniel's decision.
   - The full CPC crate is still compiled from logos `a3232131`, whose
     Lean prints the selector's type unguarded, while its proof lines are
     now guarded. It doesn't matter until stage 5 builds them, which
     needs the CPC at a logos revision with #521 anyway.
   - Moving `LOGOS_REV` changes the CPC's signature (1,104 programs at
     the prototype's revision against 1,087): a full difftest.
   - Moving `REFERENCE_REV` to an Ethos with #282 and #286 means
     pathos-eoc must mirror them first (next item).
3. **pathos-eoc's mirror of the stages**, when the reference Ethos moves:
   - #286: `crates/pathos-eoc/src/lean_meta.rs:816-817` and
     `crates/pathos-eoc/src/smt_meta.rs:673`, the function-type printing
     (`__eo_mk_apply (__eo_mk_apply Term.FunType …` when evaluatable);
   - #282's lean-meta, model_smt and semantics-compiler changes (fallback
     cases, parallel bind), not yet looked at.
4. **Smaller items:**
   - the repeated datatype name in one block (cvc5/ethos#285; pathos's
     compiled checker and Ethos disagree on it);
   - the selector invariant is no longer needed (A was chosen);
   - `docs/ethos-differences.md` for #285 once it is decided.

## Lemma C: both questions resolved

Lemma C (`<program>.rust_eq`) says logos's function is the stuck tests and
then the first case that answers; it is proved, never assumed. It needs
two things per type, and both are now settled for every type of CpcMini:

1. **Where no case applies (resolved, 2026-11-20).** Terms, proofs and
   native Booleans keep their stuck value (`HasStuck`); for every other
   type lemma C gives `default` (every logos type is `Inhabited`), and the
   body's proof shows the path unreachable (`body_stuck`/`round_stuck …
   splitting`, `split_none`). The findings behind it (report in
   `~/Projects/cvc5/pathos-m28/work/stuck-report.md`): logos and the Rust
   test arguments for stuck under the same rule (only in programs that
   return a term, only term arguments), and `CState.Stuck` is a node on
   both sides, built and matched in the same places. The Rust differs only
   where no case applies (it gives handle 0), and no logos value reaches
   that path: logos writes no default case for these types, so every
   program has a case that matches anything or one case per constructor
   (Lean checks that these are exhaustive; 10 such programs in CpcMini,
   24 in the full CPC). Most of these types have no stuck value in logos,
   so a stuck value per type was not the way. No Rust change; of the 23
   programs it stopped, 5 then had proofs and 18 stopped at `Valid`.
2. **`Valid` for the other types (resolved, 2026-11-20).** Terms keep
   `TermValid` (no application of or to the stuck term) and proofs keep
   theirs; every other argument type of CpcMini (checker states and their
   objects, the lists of commands, arguments and indices, rules, the
   datatype declarations, the SMT types and datatypes, strings, naturals,
   native Booleans) has `Valid := True` (`Runtime/Embed.lean`), and the
   emitter's gate lists exactly these. The findings behind it (report in
   `~/Projects/cvc5/pathos-m28/work/valid-report.md`): with `True`, every
   lemma C written closes; no case of a program over these types tells
   apart values that no store holds, and a term inside one of them is
   compared only as the argument of a program over terms, whose own lemma
   C takes it `Valid` and gets that from its handle. So no `Rep → Valid`
   lemma was needed, `CState`'s terms need not be said valid, and the
   `emb` bounds (strings below 2^32, bit-vectors in range) stay in
   `Represents.rep` rather than folding into `Valid`. Of the 30 programs
   it stopped, 12 now have proofs and 18 stop at calls. `CCmd` and
   `SmtTerm` were added later the same way (forced `$eo_invoke_cmd` and
   `$smtx_typeof`: lemma C closes with `True`). The full CPC's `Int`
   arguments have no instance yet; if one is needed, try `True` first.

Also on lemma C's side: the other linearization of repeated variables (an
`ite` with a continuation program `$eo.l.<n>.<prog>`) is untried; lemma C
would have to unfold the continuation program too. The application of a
possibly stuck term (`$eo_prog_scope`, proved now by the state invariant)
is milestone 31's first finding.

## Trust: the malachite specs (part B)

Daniel decided on 2026-11-20 (the trust memo,
`~/Projects/cvc5/pathos-m28/work/trust-memo.md`) to bring the
already-allowed malachite specs of groups 1–5 into use, one group a
commit, and to remove the text and parse paths by building literals as
values (done: proofs.md, "Literals are values").

| What | Runtime path | Trusted specs | Status |
| --- | --- | --- | --- |
| nat zero and succ patterns, `nat.zero` (group 3) | `native_pattern_nat_zero` (`Integer::zero`), `native_pattern_succ` (`raw_int` clone, `sgn`, `add`, `one`, `neg`) | `zero_spec`, `clone_spec`, `sgn_spec`, `add_spec`, `one_spec`, `neg_spec` | **in use**: 5 programs (`Runtime/Nats.lean`) |
| `eo::and`/`or`/`not` (group 1) | `builtin_core And` → `builtin_literal` → `Lit::evaluate_nary`; bit-vectors through `BitVec.and` | `Integer.bitwise_*_spec`, `mod_by_pow2_spec`; `clone_spec` | **in use** for `eo::and` (`bitwise_and_spec`, `mod_by_pow2_spec`; `Runtime/Builtins.lean`): `$eo_is_closed_rec` and `$eo_is_closed` proved; `$eo_invoke_cmd` (past `Valid` for `CCmd` since) stops at calls. logos's signed `BitVec.toInt`, reduced modulo `2^w`, is malachite's `and` for every width (`bv_and_toInt_emod`, proved). `eo::or` and `eo::not` are not in CpcMini; their specs stay unused. In the full CPC, `$eo_is_closed_rec` next stops at `eo::list_concat`. |
| integer natives, `zleq`, and numeral constants (group 5) | `native_int_compare`, `native_int_binary`, `native_pow2`, `native_int_to_nat`, `native_succ`; `Integer::from(<u32>)` | `partial_cmp_spec`, `euclidean_qr_spec`, `fits_u32_spec`, `to_u32_spec`, `from_u32_spec`, `pow_spec` | **in use** (`Runtime/IntNatives.lean`); with the string constants, `$eo_to_smt_type` (through `zleq`) is proved; `$smtx_typeof` is proved too (it uses `zleq`) |
| `eo::len` (group 2) | `builtin_core` → `builtin_strict` → `builtin_literal` → `literals` → `Lit::evaluate Length`: `Integer::from(size)` / `from(len)` | `from_u32_spec`, `from_usize_spec` | **in use** (`Runtime/Builtins.lean`); no program proved: `$eo_lit_type_Binary` next stops at an application of a term that may be stuck. The line is not in an emitted proof yet (the case stops before it). |
| numeral and rational literals in patterns and built from values (group 4) | `destruct` of a literal: `Hit::Raw` of a copy; `construct_literal` | `clone_spec`, `Rational.clone_spec` | **in use** (`Runtime/Numbers.lean`); `$eo_to_smt_type` is proved since the string constants; `$eo_to_smt` and `$eo_typeof` got past `$emb_String` and `$emb_Binary` (no trust, `Runtime/StringLits.lean`) and stop at case 8 |

Two more that are not about trust:

- **`eo::cons`** (`$eo_mk_premise_list`): `builtin_list Cons` →
  `list_cons_op`, which walks the list and calls generated programs
  (`eo__24eo_5fnil`, the list helpers). Its spec would be a runtime lemma
  that uses what is proved of generated functions: a new kind of piece.
- **The native string constant `"@"`** (`$eo_to_smt_reserved_datatype_name`):
  done, with no trust (`Store.raw_str_vec_spec` in `Runtime/StringLits.lean`).
  It proved that program and the four that waited on it; in the full CPC
  `"@Tuple"` goes the same way.

## Untested paths

None left in CpcMini: with all 76 programs proved, every kind of line the
emitter writes for CpcMini is in a proved program. That includes:
- `more_k` and `construct` of the stuck term;
- the string and binary literals (`$eo_typeof`, `$eo_to_smt`);
- building a function type, guarded;
- `not`;
- the state invariant's lines;
- the assumption fold's application (`invoke_assume_list_spec`).

The full CPC has kinds CpcMini lacks: argument masks, left-nested
operators, and the natives its rules use. They are untested until stage 5
builds its proofs.

## The force patch

`~/Projects/cvc5/pathos-m28/work/patches/rust-meta-force-proof.patch`
adds `LEAN_PROOF_FORCE=<program>` to rust-meta: that program's proofs are
written even though it has a reason, with `sorry` for the cases the
emitter cannot do. It is how the group, conditional, native and literal
proofs were checked on real code. Never commit it:

```
cd ~/Projects/cvc5/pathos-m28/ethos
cp plugins/rust_meta/rust_meta_reduce.cpp ../work/rmr-clean.cpp
patch -s -p1 --no-backup-if-mismatch < ../work/patches/rust-meta-force-proof.patch
(cd ../build-eoc && make ethos-eoc)
LEAN_PROOF_FORCE='$eo_typeof' ../work/gen-mini.sh   # writes proofs/Mini*.lean
~/Projects/cvc5/pathos-m28/work/le.sh MiniProofs     # errors with their goals
cp ../work/rmr-clean.cpp plugins/rust_meta/rust_meta_reduce.cpp
(cd ../build-eoc && make ethos-eoc); ../work/gen-mini.sh   # back to clean
```

Use `--no-backup-if-mismatch` (a `.orig` file once got into a commit),
and check `git status` of the Ethos clone before committing. Errors left
in a forced program are its other reasons (calls of unproved programs,
lemma C's `Valid`); the lines under test are fine when no error
points at them.

## Stage 5: the full CPC (measured, not started)

`~/Projects/cvc5/pathos-m28/work/cpc-proofs-measure.md` (2026-11-20): the
full CPC's Aeneas translation works (13 parts, 12 min; it elaborates in
7.9 min and 4 GiB). logos's CPC Lean, as lean-meta wrote it at the
crate's `LOGOS_REV` (`a3232131`) into a throwaway project, built only once
three `SmtTerm` constructors of `SmtModel.lean` (`_at_purify`,
`_at_strings_occur_index`, `_re`) were renamed: Lean 4.36 called them
internal constructors. logos's own `Cpc/SmtModel.lean` uses the same
names and does build under 4.36 (`Cpc.ApiCorrect` imports it, through
`Cpc.Spec` and `Cpc.Proofs`, and was built for cvc5/logos#518), so the
cause is in that project's setup or revision, not in logos: find it
before stage 5 (one logos revision for the crate and the proofs is
needed anyway). What stops it: `Store/Rep.lean`, pointed at the full
CPC, runs out of memory at 16 GiB, because hand-written lemmas split on
every constructor (1,062 checker constructors against CpcMini's 135),
and some hand-written files hold CpcMini's tables. Needed: one logos revision for the crate and the proofs, with the
`SmtModel` error above explained; hand-written lemmas that don't
enumerate the calculus (generated per signature, or proved without the
split); a second Lean target for the full CPC; then the 38,409-line
`proofs.lean`, built by part.

## Working notes

- Iterating: `~/Projects/cvc5/pathos-m28/work/gen-mini.sh` (run the
  working Ethos build on CpcMini into `proofs/`), `le.sh TARGET` (errors
  with goals), `ll.sh FILE`. The repository's way is `scripts/generate-mini
  --ethos <clone>` then `--check`. The full CPC is generated from the
  fork too, so check it from the m32 checkout itself, with the work
  directory outside it: `scripts/generate-cpc --ethos <clone> --rev
  <commit> --work ~/Projects/cvc5/pathos-m28/<dir> --check`.
- After a change to the generated Rust, run `scripts/full-check --quick`
  (difftest against the reference Ethos) before pushing.
- Every Ethos commit is pinned in the same pathos commit
  (`mini_default_rev`).
- Lean lessons: a syntax atom such as `" none "` becomes a keyword
  everywhere; `obtain ⟨h⟩ := e` on an equation case-splits it (bind one
  name with `have`); names made by `Lean.mkIdent` in a macro are not seen
  by `rename_i`, so use structured `cases … with` or `rcases`; `usize`
  addition has only a spec in this Aeneas (step through loops, don't
  rewrite); unfold a `partial_fixpoint` with `unfold`, not `rw`;
  `simp`ing near a literal like 2^32 can hit recursion limits (use `rw`
  and `omega`); `have h := (show T _ from by …)` lets the proof fill the
  holes of `T`, `have h : T _ := by …` does not.
- Lake runs as many Lean processes as cores unless `LEAN_NUM_THREADS` is
  set; keep the caps (4 GiB is enough for everything in `proofs/`; the CPC
  logos build needs up to 8.9 GiB per module).
