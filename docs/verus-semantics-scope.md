# Proving pathos sound: what it would take

The question this document answers: after milestone 24 the checker's core
cannot panic. What would it take to prove that pathos is *sound*? And can
logos's Lean development be reused for that?

## What "sound" would mean here

There are two claims. Only the first is about pathos.

1. **The checker is faithful to Eunoia.** When pathos prints `correct` for
   a signature S and a proof P, the specification of Eunoia also checks P
   against S. This is the soundness of pathos as a checker, it holds for
   every signature, and it does not involve logos. Verus can prove it. It
   is what this document scopes, and the plan below is for it alone.
2. **The signature is sound.** Every rule of S concludes only what is true
   in its intended theory. This is a property of the signature, not of the
   checker: a checker that follows an unsound rule faithfully accepts a
   wrong proof. For CPC, logos proves it in Lean
   (`correct___eo_is_refutation`). pathos cannot add to it.

Claim 1 has its own weak point: the specification must say what Eunoia
means. It would be written from Ethos's manual and its C++, so it is what
a reader has to review, as with any verified checker.

Claim 1 and claim 2 together say that a CPC proof pathos accepts shows what
it claims. That needs one more step, that the specification reads CPC the
way logos's compiled version does; it is discussed under "The link to
logos", and it is needed only for that end-to-end statement.

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
  description of every `eo::` operator. Their source is Eunoia: Ethos's
  desugar plugin defines each operator as a program
  (`plugins/desugar/eo_desugar.eo` for the list operators,
  `eo_desugar_native.eo` for the literal ones, about 1,600 lines together),
  and eoc compiles them. They can be transcribed one for one into Verus
  spec functions, about 70 of them.
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
signature and a proof, as parsed and elaborated, then the specification's
checker gives `correct` on the same commands.

"Elaborated" matters. The parser and `pathos-elab` (about 4,500 lines)
turn the signature's declarations into the checker's tables: attributes,
programs, overloads, literal type rules. The theorem takes those tables as
given, so an elaboration bug could make pathos check the wrong signature.
The choice is to trust elaboration, backed by the gates against Ethos, or
to also specify what each declaration means, which would roughly double
the work. This document assumes the first.

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
   - the parser (text to terms) and elaboration (declarations to tables);
   - the printer;
   - the plugin;
   - `include` and file handling;
   - the hash maps' models;
   - Verus and the Rust compiler.

   The theorem is about the terms the parser produced.

## The link to logos

Only for the end-to-end statement about CPC (claims 1 and 2 together). The chain "pathos accepts, so the specification accepts, so logos's theorem
applies" needs, for CPC only, that the specification's reading of CPC agrees
with what `ethos-eoc` compiled for logos. Lean and Verus share no proof
format, so this step is argued rather than proved:
- **The operators** are transcribed from the same definitions. A test can
  check every one on generated inputs, using the `bignum` approach with
  logos's Lean definitions, run with `#eval`, as the reference.
- **Programs and rules** are compiled by eoc. The `eoc` gate already
  checks that pathos-eoc and ethos-eoc produce the same Lean, byte for
  byte.
- **Verdicts:** a gate could compare pathos's verdict with logos's on the
  cvc5 corpus. It is not yet known whether logos can run its checker on a
  proof file rather than only prove theorems about it; a one-off check
  would say. logos answers `incomplete` where its SMT-LIB model stops,
  which such a gate has to allow for.

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

1. Milestone 24 is done: the checker's core cannot panic.
2. Do S1 as a pilot (milestone 25). It is well defined, logos has a
   precise description of every operator, and its cost gives a real
   measure for S2 to S5.
3. Decide on the quirks before S3: (a), (b) or (c) above.
4. Decide on S2 to S5 with S1's numbers in hand.
5. The link to logos is needed only for an end-to-end statement about CPC.
   Leave it until claim 1 is proved, or nearly.
