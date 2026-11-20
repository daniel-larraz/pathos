# Milestone 32: where the work stands

Written on 2026-11-20 for whoever continues (Fable, the week after). Start
here; [proofs.md](proofs.md), "Generated proofs" and "What is trusted",
has the report. Everything is on pathos `m32` and the Ethos fork's
`m32-proofs` (local clone `~/Projects/cvc5/pathos-m28/ethos`); pathos pins
the Ethos commit in `scripts/generate-cpc` (`mini_default_rev`).

## The state

- **19 of CpcMini's 82 programs** have a generated proof, listed in `generated/cpcmini-checker/proofs.tsv` with
  `generated`; every other program has the first thing that stops it.
- `scripts/proofs-build`: 2,814 theorems, no `sorry`. The trust is **11
  assumptions** (Lean's three among them), unchanged by steps 3–5; 49 declarations (axioms that declare a type or a function,
  which add no trust: see "What is trusted").
- The Rust has not changed: every step checked that CpcMini regenerates
  the same crate and that the full CPC checker's `src/`, Cargo files and
  tables are main's.
- The generated files elaborate in seconds (MiniProofs about 4.4 s and
  1.7 GiB at 5 (iii)). CPC's generated proofs are not built.

## What steps 3–5 built

The generated Lean, all written by `scripts/generate-mini` into `proofs/`:

| File | By | What |
| --- | --- | --- |
| `MiniCases.lean` | lean-meta | each program case as a function to `Option` |
| `MiniEmbed.lean` | lean-meta | per datatype `enc`, `dec`, `emb`, `dec_enc`, the inversions of `enc`, the `Embedded` instance |
| `MiniCtors.lean` | lean-meta | `CtorSpec.<rust ident>.construct/.destruct` for every data constructor and user operator |
| `MiniCacheSem.lean` | rust-meta | what a cache entry says (`ProgramSem`), for any embedded types |
| `MiniProofs.lean` | rust-meta | the proofs: case, group, body, loop and program theorems, lemma C, `specs` |

The hand-written pieces (`proofs/PathosProofs/`):

- `Store/Tree.lean`: `Tree`, `Holds` (a handle unfolds to a tree), proved
  functional, injective and monotone once; the class `Embedded` and the
  native codecs (integers, naturals, rationals, Booleans, strings as code
  points, bit-vector literals).
- `Store/Rep.lean`, `Store/Sem.lean`: `Rep nodes t x := Holds nodes t
  (enc x) ∧ emb x` for any embedded type; `Represents.rep` and `Store.Rep`
  are it for a store. The old per-type relations are gone (step 3).
- `Runtime/Node.lean`: `construct_holds`, `destruct_holds` for every data
  constructor. `Runtime/Natives.lean`: `teq`, `Teq`, `streq`, `and`, `or`,
  builtin `eo::eq`. `Runtime/Strings.lean`: `not`, `string_valid`,
  `string_prefix_eq` (loops by `fixpoint_induct`). `Runtime/Literals.lean`:
  the Boolean literal pattern, whose `destruct` changes the store.
  `Runtime/Ops.lean`: Boolean literal, `native_bool`, `tick`, `boolean_value`,
  the two `ite`s, `requires`, cached programs. `Runtime/Embed.lean`:
  `HasStuck`, `Valid`, and that a handle stands only for valid terms.
- `Tactic.lean`: one tactic per kind of generated line, including the
  groups of cases (`group_step`, `body_group_step`, `group_none`),
  conditionals (`ite_branch`, `ite_done`, `ite_stuck`) and the
  store-changing pattern (`pat_destruct_lit`).

The emitter (`plugins/rust_meta/rust_meta_reduce.cpp`): `Emitter::Lean` is
the script being recorded (`lines`, `store`, `facts`, `pure`, `built`:
terms known not stuck, `why`: the first unsupported thing). For a new kind
of operation call `leanStoreStep(spec, v)` (or `leanArgsStep` for a call on
a slice of arguments) where `expr()`/`pattern()` writes the Rust, or
`leanUnsupported("…")`. Helpers of the Rust (`requires_k`, `if_k`) are
proved in place as `have … := (show … from by …)` blocks. `emitProgram`
fills a `LeanProof`; `leanProofs()` writes the files and decides, per
program, the reason. The reasons recorded after the cases, in order: no
`HasStuck` for the return type, no `Valid` for an argument, a loop over
groups; then, across programs, "it calls … which has no proof".

## The reasons that remain (63 programs)

| Count | Reason | Programs |
| --- | --- | --- |
| 23 | no stuck value of the return type (`HasStuck`) | `$eo_dd_lookup`, `$eo_dd_resolve`, `$eo_dtc_resolve`, `$eo_dt_resolve`, `$eo_invoke_cmd_check_proven`, `$eo_invoke_cmd_list`, `$eo_invoke_cmd_step_pop`, `$eo_push_assume_check`, `$eo_push_input_assume_check`, `$eo_push_proven`, `$eo_push_proven_check`, `$eo_to_smt_datatype`, `$eo_to_smt_datatype_cons`, `$eo_to_smt_datatype_decl`, `$smtx_dd_lookup`, `$smtx_dtc_resolve`, `$smtx_dt_resolve`, `$smtx_ret_typeof_sel`, `$smtx_typeof_=`, `$smtx_typeof_apply`, `$smtx_typeof_guard`, `$smtx_typeof_guard_wf`, `$smtx_typeof_ite` |
| 12 | an argument of a type without `Valid` (lemma C) | `$eo_checker_is_refutation`, `$smtx_dd_has_dt`, `$smtx_decl_inhabited`, `$smtx_decl_wf_rec`, `$smtx_dt_cons_inhabited`, `$smtx_dt_cons_wf_rec`, `$smtx_dt_inhabited`, `$smtx_dt_wf_rec`, `$smtx_inhabited_type`, `$smtx_type_wf`, `$smtx_type_wf_component`, `$smtx_type_wf_rec` |
| 6 | no logos function (the datatype operators; the gate counts 76) | `$eo_datatype_cons_selectors_rec`, `$eo_datatype_constructors_rec`, `$eo_dt_constructors`, `$eo_dt_constructors_main`, `$eo_dt_selectors`, `$eo_dt_selectors_main` |
| 4 | a native pattern (nat zero/succ) | `$eo_typeof_dt_cons_rec`, `$eo_typeof_dt_sel_return`, `$smtx_ret_typeof_sel_rec`, `$smtx_typeof_dt_cons_rec` |
| 3 | a builtin operator | `$eo_invoke_cmd` (`eo::and`), `$eo_lit_type_Binary` (`eo::len`), `$eo_mk_premise_list` (`eo::cons`) |
| 2 | `$emb_Numeral` in a pattern | `$eo_to_smt`, `$eo_typeof` |
| 2 | the stuck term built as a constructor | `$eo_cmd_step_pop_proven`, `$eo_cmd_step_proven` |
| 2 | compiled to a function of the runtime | `$eo_invoke_assume_list`, `$eo_state_proven_nth` |
| 2 | a function type in a pattern | `$eo_to_smt_type`, `$eo_typeof_apply` |
| 1 each | `zleq`; the native string constant `"@"`; `$emb_Var` in a pattern; an application of a term that may be stuck (`$eo_prog_scope`) | `$smtx_typeof`; `$eo_to_smt_reserved_datatype_name`; `$eo_is_closed_rec`; `$eo_prog_scope` |
| 3 | calls of programs without a proof | `$eo_is_bool_type`, `$eo_is_closed`, `$eo_state_is_refutation` |

## Lemma C: the two open questions (yours)

Lemma C (`<program>.rust_eq`) says logos's function is the stuck tests and
then the first case that answers; it is proved, never assumed. It needs
two things per type that the proofs have only for some types, and
together they stop 35 programs:

1. **`HasStuck`** (the value a body gives where no case applies): there are
   instances for terms, proofs and native Booleans (`Runtime/Embed.lean`).
   Checker states, datatype declarations and SMT types have none.
   **What the bodies do (checked 2026-11-20, report in
   `~/Projects/cvc5/pathos-m28/work/stuck-report.md`)**: logos and the
   Rust test arguments for stuck under the same rule (only in programs
   that return a term, only term arguments), and `CState.Stuck` is a node
   on both sides, built and matched in the same places. The Rust differs
   only where no case applies (it gives handle 0), and no logos value
   reaches that path: of the 23, 13 end in a case that matches anything
   and 10 have one case per constructor (exhaustive; the full CPC has 24
   such programs, all exhaustive). Most of these types have no stuck value
   in logos (the datatype types, `CCmdList`, `CArgList`, …; `SmtType.None`
   is an ordinary value), so a stuck value per type is not the way. The
   proposal being prototyped: lemma C takes `default` (every logos type is
   `Inhabited`) where no case applies, and `body_stuck` closes by
   `exfalso`, after a case split on the argument for the exhaustive
   programs. No Rust change. Of the 23, 18 would then stop at `Valid`.
2. **`Valid` for the other types, and folding `emb` into it.** `Valid` has
   instances for terms (`TermValid`: no application of or to the stuck
   term), proofs, `CState`, `CStateObj` (both `True`, and they should say
   that the terms inside are valid), and native Booleans. The SMT types,
   the datatype declarations, strings, `CCmdList`, `CArgList` have none.
   `Represents.rep` carries `emb_T x` (strings with characters below 2^32,
   bit-vectors in range) beside `Holds`; it should fold into `Valid`. Why
   it holds of what logos builds: logos itself bounds widths
   (`native_zlt … 4294967296`) and characters (below 196608); the closure
   lemma (a handle unfolds only to embeddable values) is not written.

Also on lemma C's side: the other linearization of repeated variables (an
`ite` with a continuation program `$eo.l.<n>.<prog>`) is untried; lemma C
would have to unfold the continuation program too. The application of a
possibly stuck term (`$eo_prog_scope`) is milestone 31's first finding.

## What needs trust (decided: not this week)

Step 5 (iii) stopped where specs would bring `Trusted.lean` assumptions
into use. They are declared and allowed in `axioms-allowed.txt`; bringing
them into use is a decision to take with lemma C, when it yields proofs.

| What | Runtime path | Trusted specs it would bring into use |
| --- | --- | --- |
| `eo::and` (`$eo_invoke_cmd`) | `builtin_core And` → `builtin_literal` → `Lit::evaluate_nary`; bit-vectors through `BitVec.and` | `Integer.bitwise_and_spec`, `mod_by_pow2_spec`; `clone_spec` (copying numerals) |
| `eo::len` (`$eo_lit_type_Binary`) | `Lit::evaluate Length`: `Integer::from(size)` / `from(len)` | `from_u32_spec`, `from_usize_spec` |
| nat zero and succ patterns (4 programs) | `native_pattern_nat_zero` (`Integer::zero`), `native_pattern_succ` (`raw_int` clone, `sgn`, `add`, `one`, `neg`) | `zero_spec`, `clone_spec`, `sgn_spec`, `add_spec`, `one_spec`, `neg_spec` |
| `$emb_Numeral` patterns (`$eo_to_smt`, `$eo_typeof`) | `destruct` of a literal: `Hit::Raw` of a copy | `clone_spec` |

Three more that are not about trust:

- **`eo::cons`** (`$eo_mk_premise_list`): `builtin_list Cons` →
  `list_cons_op`, which walks the list and calls generated programs
  (`eo__24eo_5fnil`, the list helpers). Its spec would be a runtime lemma
  that uses what is proved of generated functions: a new kind of piece.
- **`$emb_Var`** in a pattern (`$eo_is_closed_rec`): the runtime treats it
  as data, but its schema embedding is `Var`, not `Data`, so
  `construct_holds`/`destruct_holds` (which require `Data`) do not apply;
  they would need a `Var` variant.
- **The native string constant `"@"`** (`$eo_to_smt_reserved_datatype_name`)
  goes through `native_constant` → `front.native_literal`, which
  `Trusted.lean` only assumes returns. It needs `native_literal`'s
  specification, and with it the generated `NATIVE_TEXTS` as a Lean table
  (the gap that "What is trusted" names for the final theorem).

## Untested paths

The emitter writes these, and they elaborate where they have been
exercised, but no proved program reaches them yet:

- `eo::ite`'s stuck branch (`ite_stuck`): CpcMini's only `eo::ite` is in
  `$eo_is_closed_rec`, in a case blocked by `$emb_Var`. The native `ite` is
  tested (forced `$eo_to_smt_type`).
- `more_k` inside a requirement: no requirement of CpcMini is cut into
  one. The only `more_k` (in `$eo_cmd_step_proven`'s case 0) is unfolded
  fine, but that case also calls a program without a proof.
- The round of a loop whose cases are in groups (`$smtx_inhabited_type`):
  not written; it is recorded only when nothing else stops the program.
- `not` and `string_prefix_eq` in a generated proof: their specs compile,
  but their only uses come after a failing call (`not`) or behind `"@"`.

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
lemma C's `Valid`/`HasStuck`); the lines under test are fine when no error
points at them.

## Working notes

- Iterating: `~/Projects/cvc5/pathos-m28/work/gen-mini.sh` (run the
  working Ethos build on CpcMini into `proofs/`), `le.sh TARGET` (errors
  with goals), `ll.sh FILE`. The repository's way is `scripts/generate-mini
  --ethos <clone>` then `--check`; the full CPC comparison runs in the
  origin/main worktree `~/Projects/cvc5/pathos-m28/main-wt`
  (`scripts/generate-cpc --ethos <clone> --rev <commit> --check`).
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
