# Milestone 32: where the work stands

Written on 2026-11-20 for whoever continues (Fable, the week after). Start
here; [proofs.md](proofs.md), "Generated proofs" and "What is trusted",
has the report. Everything is on pathos `m32` and the Ethos fork's
`m32-proofs` (local clone `~/Projects/cvc5/pathos-m28/ethos`); pathos pins
the Ethos commit in `scripts/generate-cpc` (`mini_default_rev`).

## The state

- **61 of CpcMini's 82 programs** have a generated proof (61 of the
  76 that the gate counts: the 6 datatype operators have been excluded
  since 2026-11-19), listed in
  `generated/cpcmini-checker/proofs.tsv` with `generated`; every other
  program has the first thing that stops it.
- `scripts/proofs-build`: 6,461 theorems, no `sorry`. The trust is **27
  assumptions** (Lean's three among them): the 11 of steps 3–5 and, from
  part B (Daniel's decision of 2026-11-20), the malachite specs that the
  proved programs reach (see the trust table below); 49 declarations (axioms that declare a type or a function,
  which add no trust: see "What is trusted").
- Loops are proved by strong induction on the budget of calls
  (`Store.budget`, which every round's `tick` lowers), not by Lean's
  fixpoint induction, so a loop in a mutual block works:
  `$smtx_inhabited_type` (a loop whose cases are tried in groups, on a
  cycle of four programs) and the ten that call it are proved. See
  proofs.md, "Loops" and "Groups of cases".
- The Rust is main's but for literals: since Ethos `db074f2` the
  generated code builds literals as values, not from text (proofs.md,
  "Literals are values"), and pathos m32's `generated/cpc-checker` is
  generated from the fork (`default_rev` of `scripts/generate-cpc`). Its
  diff with main is the literal sites, `names.rs`, two allowances in
  `front.rs`/`lib.rs`, and functions that move between parts; every
  other step checked that the Rust is unchanged.
- The generated files elaborate in seconds (MiniProofs about 11 s and
  2.6 GiB, after the string constants). CPC's generated proofs are not built.

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
`Valid` for an argument; then, across programs, "it calls … which has no proof".

## The reasons that remain (21 programs)

| Count | Reason | Programs |
| --- | --- | --- |
| 8 | calls of programs without a proof | `$eo_checker_is_refutation` (→ `$eo_invoke_assume_list`), `$eo_cmd_step_pop_proven` (→ `$eo_prog_scope`), `$eo_cmd_step_proven` (→ `$eo_mk_premise_list`), `$eo_invoke_cmd` (→ `$eo_cmd_step_proven`; it also calls `$eo_is_bool_type` and `$eo_invoke_cmd_step_pop`), `$eo_invoke_cmd_list` (→ `$eo_invoke_cmd`), `$eo_invoke_cmd_step_pop` (→ `$eo_cmd_step_pop_proven`), `$eo_is_bool_type` (→ `$eo_typeof`), `$eo_push_proven` (→ `$eo_is_bool_type`) |
| 6 | no logos function (the datatype operators; the gate counts 76) | `$eo_datatype_cons_selectors_rec`, `$eo_datatype_constructors_rec`, `$eo_dt_constructors`, `$eo_dt_constructors_main`, `$eo_dt_selectors`, `$eo_dt_selectors_main` |
| 1 | a builtin operator | `$eo_mk_premise_list` (`eo::cons`) |
| 2 | case 8, past the string and binary literal patterns (`Runtime/StringLits.lean`) | `$eo_typeof` (an application of a term that may be stuck: the function type it builds, past the line for building one), `$eo_to_smt` (the native operation `uconst_id`) |
| 2 | compiled to a function of the runtime | `$eo_invoke_assume_list`, `$eo_state_proven_nth` |
| 2 | an application of a term that may be stuck | `$eo_prog_scope`, `$eo_lit_type_Binary` |

## What's left (for Fable)

61 of the 76 programs the gate counts are proved. The other 15, by what
stops them first and what it would take:

**More of the same** (no decision, no trust beyond the 27):

- `$eo_typeof` and `$eo_to_smt`: past cases 0–7 (string and binary
  literal patterns done, `Runtime/StringLits.lean`), both stop at case 8.
  `$eo_typeof`'s case 8 builds a function type: the emitter now has its
  lines (the constant `$emb_FunType` and two applications), but the
  result type `__eo_typeof_dt_sel_return …` may be stuck, so it meets the
  stuck-application design question below. `$eo_to_smt`'s is the native
  operation `uconst_id`: `@u.` and the decimal digits of a runtime number
  (`front::constant_name`, `format!`, trusted by `constant_name_spec`).
  A generator change cannot make it a constant as with the literals,
  since the number is a value at run time; the runtime could build the
  digits with a loop over `Integer::euclidean_qr` by 10 and `to_u32`
  (specs in use), which Aeneas translates, and a proof that the loop
  spells `toString i` would then need no trusted spec. It also needs
  `HasStuck SmtTerm` for lemma C. Left for Daniel and Fable. Forced, case 4 of both elaborates;
  `$eo_typeof`'s case 4 calls `$eo_lit_type_Binary` (a design question,
  below), and `$eo_to_smt`'s lemma C needs `HasStuck SmtTerm` (its
  default case gives an SMT term), which has no instance yet. The type
  cache, which `$eo_typeof` keeps its results in, is done (proved with
  `$smtx_typeof`).
- `$smtx_typeof` is proved, with the type cache (`framed_type_cached`,
  the `TypesOK` part of the store's invariant). In the full CPC, where it
  is the 37/10/3-group loop, it now stops at a call of
  `$smtx_typeof_bv_op_2`, which has no proof.
- `$eo_is_bool_type` → `$eo_push_proven`: wait on `$eo_typeof`, so on
  the stuck-application question too.

**Design questions** (each needs Daniel's decision first):

- *An application of a term that may be stuck* (milestone 31's first
  finding): `$eo_prog_scope` and `$eo_lit_type_Binary`; through calls,
  `$eo_cmd_step_pop_proven` → `$eo_invoke_cmd_step_pop`.
- *`eo::cons`* (`$eo_mk_premise_list`): the runtime's `list_cons_op` calls
  generated programs, so its spec is a runtime lemma that uses what is
  proved of generated functions, a new kind of piece. Through calls:
  `$eo_cmd_step_proven` → `$eo_invoke_cmd` → `$eo_invoke_cmd_list`
  (`$eo_invoke_cmd` also waits on `$eo_is_bool_type` and
  `$eo_invoke_cmd_step_pop`).
- *Programs compiled to the runtime*: `$eo_invoke_assume_list` and
  `$eo_state_proven_nth` are functions of the runtime, not generated
  code, so they need hand-written proofs of the runtime's functions or a
  change to what is compiled; `$eo_checker_is_refutation` waits on them
  (and, through `$eo_invoke_cmd_list`, on the two above).

**Out of the count:** the six datatype operators have no logos function
(only the runtime's datatype operators reach them).

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
possibly stuck term (`$eo_prog_scope`) is milestone 31's first finding.

## Trust: the malachite specs (part B)

Daniel decided on 2026-11-20 (the trust memo,
`~/Projects/cvc5/pathos-m28/work/trust-memo.md`) to bring the
already-allowed malachite specs of groups 1–5 into use, one group a
commit, and to remove the text and parse paths by building literals as
values (done: proofs.md, "Literals are values").

| What | Runtime path | Trusted specs | Status |
| --- | --- | --- | --- |
| nat zero and succ patterns, `nat.zero` (group 3) | `native_pattern_nat_zero` (`Integer::zero`), `native_pattern_succ` (`raw_int` clone, `sgn`, `add`, `one`, `neg`) | `zero_spec`, `clone_spec`, `sgn_spec`, `add_spec`, `one_spec`, `neg_spec` | **in use**: 5 programs (`Runtime/Nats.lean`) |
| `eo::and`/`or`/`not` (group 1) | `builtin_core And` → `builtin_literal` → `Lit::evaluate_nary`; bit-vectors through `BitVec.and` | `Integer.bitwise_*_spec`, `mod_by_pow2_spec`; `clone_spec` | **in use** for `eo::and` (`bitwise_and_spec`, `mod_by_pow2_spec`; `Runtime/Builtins.lean`): `$eo_is_closed_rec` and `$eo_is_closed` proved; `$eo_invoke_cmd` next stops at `Valid` for `CCmd`. logos's signed `BitVec.toInt`, reduced modulo `2^w`, is malachite's `and` for every width (`bv_and_toInt_emod`, proved). `eo::or` and `eo::not` are not in CpcMini; their specs stay unused. In the full CPC, `$eo_is_closed_rec` next stops at `eo::list_concat`. |
| integer natives, `zleq`, and numeral constants (group 5) | `native_int_compare`, `native_int_binary`, `native_pow2`, `native_int_to_nat`, `native_succ`; `Integer::from(<u32>)` | `partial_cmp_spec`, `euclidean_qr_spec`, `fits_u32_spec`, `to_u32_spec`, `from_u32_spec`, `pow_spec` | **in use** (`Runtime/IntNatives.lean`); with the string constants, `$eo_to_smt_type` (through `zleq`) is proved; `$smtx_typeof` is proved too (it uses `zleq`) |
| `eo::len` (group 2) | `builtin_core` → `builtin_strict` → `builtin_literal` → `literals` → `Lit::evaluate Length`: `Integer::from(size)` / `from(len)` | `from_u32_spec`, `from_usize_spec` | **in use** (`Runtime/Builtins.lean`); no program proved: `$eo_lit_type_Binary` next stops at an application of a term that may be stuck. The line is not in an emitted proof yet (the case stops before it). |
| numeral and rational literals in patterns and built from values (group 4) | `destruct` of a literal: `Hit::Raw` of a copy; `construct_literal` | `clone_spec`, `Rational.clone_spec` | **in use** (`Runtime/Numbers.lean`); `$eo_to_smt_type` is proved since the string constants; `$eo_to_smt` and `$eo_typeof` got past `$emb_String` (no trust, `Runtime/StringLits.lean`) and stop at `$emb_Binary` |

Three more that are not about trust:

- **`eo::cons`** (`$eo_mk_premise_list`): `builtin_list Cons` →
  `list_cons_op`, which walks the list and calls generated programs
  (`eo__24eo_5fnil`, the list helpers). Its spec would be a runtime lemma
  that uses what is proved of generated functions: a new kind of piece.
- **The native string constant `"@"`** (`$eo_to_smt_reserved_datatype_name`):
  done, with no trust (`Store.raw_str_vec_spec` in `Runtime/StringLits.lean`).
  It proved that program and the four that waited on it; in the full CPC
  `"@Tuple"` goes the same way.

## Untested paths

The emitter writes these, and they elaborate where they have been
exercised, but no proved program reaches them yet:

- `more_k` inside a requirement: no requirement of CpcMini is cut into
  one. The only `more_k` (in `$eo_cmd_step_proven`'s case 0) is unfolded
  fine, but that case also calls a program without a proof.
- `construct` of the stuck term (`Store.construct_stuck_spec`): both
  programs that build it call programs without a proof
  (`$eo_cmd_step_pop_proven` → `$eo_prog_scope`, `$eo_cmd_step_proven` →
  `$eo_mk_premise_list`); its line was checked with the force patch on
  `$eo_cmd_step_proven`'s case 4.
- String literals in patterns and built from values
  (`destruct_string_spec`, `construct_string_spec`): `$eo_typeof` and
  `$eo_to_smt` now stop at case 4 (`$emb_Binary`). Checked with the force
  patch on `$eo_typeof`: case 3's lines, both lemmas among them,
  elaborate. (Its cached wrapper's id, `type#u32`, is gone: the type
  cache has its own lemma now.)
- `not` in a generated proof: its spec compiles, but its only use comes
  after a failing call. (`string_prefix_eq` is now in a proved program,
  `$eo_to_smt_reserved_datatype_name`, behind `"@"`.)

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
