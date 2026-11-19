# Milestone 32: where the work stopped

Written on 2026-11-19 for whoever continues. The state of the proofs is in
[proofs.md](proofs.md), section "Generated proofs"; this is what is not
there. pathos `m32` and the Ethos clone
`~/Projects/cvc5/pathos-m28/ethos` (`m32-proofs`) hold everything.

## Stage 2: what `Store/Tree.lean` was going to be

Today each logos type has a hand-written relation to handles (`Rep`,
`RepProof`, `RepState`, `RepObj`, `NativeBool`), each with its own
"functional", "injective" and "mono" proofs. That does not scale to 135
constructors and about 20 types. The plan:

- `Tree`: a handle's data with its handles unfolded. `Holds nodes t x`:
  the handle `t` unfolds to the tree `x`. Functional, injective (from "no
  two handles have the same data") and monotone are proved **once**, there.
- Per logos type a generated function `enc : T → Tree` (a data constructor
  is `Tree.node c [enc fields…]`; the seven special ones follow
  `Constructor::embedding` in the runtime: stuck, apply, the four literals,
  binary; a native field is `Tree.native`). `Represents.rep s t x` becomes
  `Holds s.nodes.val t.val (enc x)` for every type, so `carry_one`,
  `congr_one` and `pat_same` lose their per-type alternatives. `eq_iff`
  needs `enc` injective: generate a left inverse `dec` and prove
  `dec (enc x) = some x` by induction and `simp`.
- `construct`/`destruct` of a data constructor are then one generic lemma
  each over `Holds`; the per-constructor `CtorSpec.*` lemmas keep their
  shape (the tactics read it) and become one-liners, generated.
- lean-meta should write this file: `finalizeDecl`
  (`lean_meta_reduce.cpp`, about line 1275) has the EO name, the Lean
  constructor, its type and its field types in hand. It needs
  `RustMetaReduce::ident` for the Rust names.
- `destruct` of a literal constructor (`$emb_Numeral`…) interns a native
  handle, so it changes the store: `pat_destruct` assumes it does not.
- `MiniCacheSem` then uses `Holds`/`enc` and can cover caches over values
  that are not terms. Layering: `Tree` → generated embedding → cache table
  → `Store/Ops`.

The file as committed **does not compile** and nothing imports it. Known
errors: `Inhabited TermData` is needed for `nodes[t]!` (there is an
instance in `Store/`, import it or move it to `Util`), and in `Holds.mono`
the `refine Holds.rec … h` leaves the goal open. The proofs use the mutual
recursor with explicit motives; that part is untested.

## The emitter (`plugins/rust_meta/rust_meta_reduce.cpp`)

- `Emitter::Lean` (member `lean`) is the script being recorded: `lines`,
  `store` (counter: `s`, `s1`, …), `facts` (carried to the next store),
  `pure` (facts about terms), `why` (first unsupported thing), `indent`.
- A new kind of operation: where `expr()` or `pattern()` writes the Rust,
  call `leanStoreStep(spec, v)` for something that returns a handle
  (`spec` is a Lean term whose statement has the standard shape: new store
  has `Inv`, `Grows`, `Ok t => rep …`), or `leanLine(...)` with a tactic of
  `PathosProofs/Tactic.lean`; where there is no line yet, call
  `leanUnsupported("…")`. Every branch of `expr`/`pattern`/`op` already
  does one of the two.
- A helper function of the Rust (`requires_k`) is proved in place as a
  `have … := (show … from by …)` block; see `EVAL_REQUIRES` in `op()`.
  Conditionals (`conditional()`) should be done the same way.
- `emitProgram` fills a `LeanProof` per program; `leanProofs()` writes
  `proofs.lean`, `proofs.tsv`, `cache_sem.lean`. `leanCtorLemmas()` is the
  stopgap list of constructors with lemmas.
- Not done: groups of cases (`cases_<d>_<g>`, more than four cases) need a
  theorem per group; helpers cut by `close()` (`more_k`) are unfolded at
  the start of the case, untested inside a requirement.
- Iterating: `~/Projects/cvc5/pathos-m28/work/gen-mini.sh` (generate into
  `proofs/`), `le.sh TARGET` (errors with goals), `ll.sh FILE`.

## Lemma C with repeated variables

Already how it works: the case function has fresh variables and
`if x = x' then some … else none`; logos has `requires (eo_eq x x') true …`.
`logos_eq` closes the difference with `requires_ite`, `eo_eq_of_ne`,
`eo_eq_true`, given `Valid` of each argument. Untried: the other
linearization (an `ite` with a continuation program `$eo.l.<n>.<prog>`,
used when a later case could still apply). There lemma C must unfold the
continuation program too; I expected to add its name to the `unfold` list
and its `.case_i` functions to `firstSome`. `Valid` for states and state
objects is `True` and will have to say that the terms inside are valid.

## Stage 1: the recursion failures

Hypothesis, from `BvUaddoElimSupport:144` only: `simp`/`simpa` given
`SmtEval.native_zleq` (or a sibling) unfolds it to `decide` on a
hypothesis with a large literal (4294967296), and the kernel recurses on
the resulting term. Rewriting with the equation and never unfolding
(`rw [SmtEval.native_zleq] at h; exact of_decide_eq_true h`) fixed that
line; the later `simp […native_zleq…]` calls of the same proof fail the
same way and were not converted. So it is confirmed for one line of one
module. `Evaluate.Prelude.StringFromInt:172` has the same kernel error and
I did not look at it: the hypothesis is a guess there.
`Evaluate.Prelude.StringCode:199` is a different error (the elaborator's
"maximum recursion depth"), and the hypothesis does not cover it.
All three, and `StrReplaceReCaseSupport`, also fail at v4.35.0 unchanged.

## Not written elsewhere

- `proofs/.lake/packages/LogosVerification` has **uncommitted local
  edits** (the three script-drift fixes, two lines of
  `BvUaddoElimSupport`); the patch is
  `~/Projects/cvc5/pathos-m31/stage1/logos-v436-fixes.patch`. A fresh
  `lake update` loses them. CpcMini does not need them.
- The stage 1 commit is still owed: `docs/proofs.md` says neither logos
  nor Aeneas needs a source change, which is true for CpcMini only; six
  CPC modules fail at v4.36.0. Memory: ArithMultSupport, Translation/Full
  and Rules/String_ext each need 8.1 to 8.9 GiB at either Lean version;
  the full CPC build in `proofs/` took 3 h 11 min (834 modules, peak
  15.3 GiB with 3 jobs).
- Ethos `m32-proofs` has one commit after 4274d2b (a reason text in
  `proofs.tsv`). pathos still pins 4274d2b, so `generate-mini --check`
  is unaffected until the pin moves; moving it changes `proofs.tsv` only.
- In a macro, `rfl` in an `rcases`/`obtain` pattern and names used across
  two quotations are hygienic and silently become fresh hypotheses: use
  `Lean.mkIdent` and `subst`. `have h : T _ := by …` does not let the
  proof fill the hole; `have h := (show T _ from by …)` does.
- Lake runs as many Lean processes as cores unless `LEAN_NUM_THREADS` is
  set; keep the caps (4 GiB was enough for everything in `proofs/`).
