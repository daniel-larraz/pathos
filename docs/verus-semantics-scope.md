# Proving pathos sound: what it would take

The question this document answers: after milestone 24 the checker's core
cannot panic. What would it take to prove that pathos is *sound*? And can
logos's Lean development be reused for that?

## What "sound" would mean here

There are two claims, and they belong to different tools.

1. **The calculus is sound.** Every CPC rule concludes only what is true in
   SMT-LIB. This is logos's theorem (`correct___eo_is_refutation`, in Lean).
   pathos cannot add to it: pathos checks proofs against whatever signature
   it is given.
2. **The checker is faithful.** When pathos prints `correct` for a
   signature S and a proof P, the specification of Eunoia also checks P
   against S. Verus can prove this. It is what this document scopes.

Put together, they give the chain a user wants: pathos accepts a CPC proof,
so the specification accepts it, so (by logos) its assumptions are
unsatisfiable. The link in the middle, "the specification's reading of CPC
is the one logos proved sound", is discussed under "The link to logos".

## What logos has, and what it does not

logos's statement is about one calculus. `install/install-cpc.sh` runs
`ethos-eoc` over the CPC signature and produces Lean definitions
(`Cpc/Logos.lean`, about 10,700 lines, 1,140 definitions):
- a `Term` type whose constructors include CPC's own operators (`UserOp`);
- one total Lean function per `eo::` operator (`__eo_add`, `__eo_list_concat`,
  ...) that returns `Term.Stuck` when it does not apply;
- one Lean function per CPC program and per rule;
- the checker as a state machine (`__eo_invoke_cmd`, `__eo_checker_is_refutation`).

Its proof is in layers (logos `docs/modularity.md`). The checker layer, the
state machine and its invariants, is about 4,000 lines and is reused
verbatim by a second calculus (CpcMini). The rest, about 700,000 lines, is
specific to CPC's 591 rules and to the translation into SMT-LIB.

**logos has no semantics of Eunoia as such.** There is no definition of what
an arbitrary signature means. The meaning of CPC is "what `ethos-eoc`
compiles it to". pathos interprets any signature, so its specification has
to be a general interpreter, written as spec functions in Verus. logos
cannot be imported, and Lean and Verus share no proof format.

What can be reused:
- **The operators.** The `__eo_*` definitions are a precise, total
  description of every `eo::` operator, produced by the same compiler that
  pathos ports (`pathos-eoc`). They can be transcribed one for one into
  Verus spec functions, about 70 of them.
- **The shape of the checker's specification.** The state machine of
  `__eo_invoke_cmd`, with assumption pushes, `step`, `step-pop` and the final
  check, is small and calculus-independent. It is the right shape for
  pathos's top-level statement.
- **The term order.** logos's `LogosTermOrder.lean` says what `eo::cmp`
  must respect.

## What the specification would contain

pathos already has part of it from milestones 17 to 23:
- terms as trees (`tree`);
- substitution (`inst`);
- matching, with a proof that matching is correct (milestone 19);
- the store's invariant.

What is missing:

| Part | Content | Source |
|---|---|---|
| Operators | One spec function per `eo::` operator over trees and literal values | transcribed from logos's `__eo_*` |
| Evaluation | Program application (first matching case, substitution, evaluation of the body) and `eo::ite`, `eo::requires`, `eo::define`, with a fuel argument | Ethos's `evaluate` |
| Typing | The type of a term: applications, `eo::` operators, literals, quoted parameters | Ethos's type checker |
| Building | What `mk_expr` makes of n-ary, chained and pairwise applications, `:list` and nil terminators | Ethos's `mkExpr` |
| Checking | The command state machine and the verdict | logos's `__eo_invoke_cmd` |

The top-level theorem would read: if pathos prints `correct` for a
signature and a proof, as parsed, then the specification's checker gives
`correct` on the same parsed commands.

## The decisions the specification forces

1. **Stuck terms.**
   - logos: an operator that does not apply gives `Stuck`, and `Stuck`
     absorbs everything around it.
   - Ethos and pathos: they give back the unevaluated application, which can
     still be matched and printed.

   The specification has to describe pathos, so it uses Ethos's semantics,
   with a lemma connecting it to logos's. If a result still contains an
   unevaluated application, it would have been `Stuck` in logos. That lemma
   is the link to logos for the operators.
2. **The quirks.** pathos reproduces Ethos's bugs on purpose; the ones
   reported are #257 to #269 and #271. The options:
   - (a) The specification includes them. The theorem is then
     "pathos is faithful to Ethos's semantics", which is weaker and has
     awkward clauses.
   - (b) The specification is the intended semantics, and the theorem is
     stated on inputs that avoid the quirks, with a decidable check of
     "avoids" where possible.
   - (c) Wait for Ethos to fix them, and follow.

   Milestone 23 already met this: typing's use of matching cannot be
   proved correct while #269 is reproduced. My recommendation is (b), with
   the quirks as listed exclusions that shrink as Ethos fixes them. #271 is
   not an exclusion: pathos already behaves as intended there.
3. **Termination.** Programs need not terminate. The statement is partial:
   if pathos returns, the result equals the specification's at some fuel.
   This is standard, and costs little beyond carrying the fuel.
4. **`eo::hash` and `eo::cmp`.** Their values depend on the order in which
   terms are created. The specification takes them as functions it does
   not define, with the properties logos's term order states. A theorem
   that holds for any such function covers pathos and Ethos alike.
5. **Numbers.** The specification uses mathematical integers and rationals
   (`int` in Verus). `malachite`'s arithmetic stays trusted. That is the
   same position as logos, which trusts Lean's.
6. **What stays outside.**
   - the parser (text to terms);
   - the printer;
   - the plugin;
   - `include` and file handling;
   - the hash maps' models;
   - Verus and the Rust compiler.

   The theorem is about the terms the parser produced.

## The link to logos

The chain "pathos accepts, so the specification accepts, so logos's theorem
applies" needs, for CPC only, that the specification's reading of CPC agrees
with what `ethos-eoc` compiled for logos. Lean and Verus share no proof
format, so this step is argued rather than proved:
- **The operators** are transcribed from the same definitions. A test can
  check every one on generated inputs, using the `bignum` approach with
  logos's executable as the reference.
- **Programs and rules** are compiled by eoc. The `eoc` gate already
  checks that pathos-eoc and ethos-eoc produce the same Lean, byte for
  byte.
- **Verdicts:** a new gate would compare pathos's verdict with logos's on
  the cvc5 corpus. This is cheap and can be added now, independently of
  any proof. logos answers `incomplete` where its SMT-LIB model stops,
  which the gate has to allow for.

Argued plus tested is the same footing on which logos itself relates its
compiled CPC to the Eunoia text cvc5 maintains.

## Plan and estimate

| Milestone | Content | Size (proof lines, rough) |
|---|---|---|
| S1 | Specification of the operators (transcribed); `Lit::evaluate` and the list operators proved to compute it | 800–1,500 |
| S2 | Specification of evaluation with fuel; `evaluate` refines it, caches and frames included | 1,500–3,000 |
| S3 | Specification of typing; `get_type` refines it, quirks as exclusions | 800–1,500 |
| S4 | Specification of building; `mk_expr` refines it | 600–1,200 |
| S5 | Specification of the checker; step checking refines it; the top-level theorem | 600–1,200 |

Roughly 4,000 to 8,000 lines of proof in five to seven milestones. For
comparison, milestones 17 to 23 together came to about 4,800 lines of
specification and proof, 1,900 of them in milestone 17.

The range is wide for two reasons:
- **S2.** Proving that the caches and the frame stack are invisible is a
  refinement proof of a kind not attempted yet in pathos.
- **The quirks.** Each exclusion adds clauses to every statement that
  meets it.

## Recommendation

1. Finish milestone 24 (panic freedom).
2. Add the verdict gate against logos now. It is independent of the proofs
   and tests the link above directly.
3. Do S1 as a pilot. It is well defined, its specification exists in
   logos, and its cost gives a real measure for S2 to S5.
4. Decide on the quirks before S3: (a), (b) or (c) above.
5. Decide on S2 to S5 with S1's numbers in hand.
