module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Embed
public import PathosProofs.Runtime.Ops
public import MiniCtors
public import PathosProofs.Runtime.Natives
public import PathosProofs.Runtime.Strings
public import PathosProofs.Runtime.Literals
public import PathosProofs.Runtime.Nats
public import PathosProofs.Runtime.Numbers
public import PathosProofs.Runtime.IntNatives
public import PathosProofs.Runtime.Builtins
public import PathosProofs.Runtime.StringLits
public import PathosProofs.Runtime.Lists
public import PathosProofs.Runtime.AssumeFold
public import PathosProofs.Runtime.StateInv
public import PathosProofs.Runtime.StateNth
public import PathosProofs.Runtime.ConstNames

/-!
# The tactics of the generated proofs

A proof about a generated function follows its code: rust-meta writes one
line of proof for each line of Rust, and each line is one of the tactics
here. What a line has to do is always the same: name the result and the
new store, take the invariant of the new store, extend the record of how
the store grew, carry every fact about a handle over to the new store,
and on an error finish at once.

The names in a line are the generator's: `v<i>` and `a<i>` are the Rust's
variables, `h_v` says what the handle `v` stands for, `x_v` is the value it
stands for where a pattern took it out of another, `hn_v` says that value
is not the stuck term, `s<k>` and `hinv<k>` are the store after `k`
operations and its invariant, `hG` says how the store has grown since the
function began.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `carry_one h hg`: the fact `h` about a handle, carried over to the
store that the store has grown to (`hg`). -/
syntax "carry_one " ident ppSpace term : tactic
macro_rules
  | `(tactic| carry_one $h $hg) => `(tactic| first
    | replace $h:ident := Represents.grows $h $hg
    | replace $h:ident := lt_of_le_of_lt (Store.Grows.budget $hg) $h)

/-- `congr_one h hn`: the fact `h` about a handle, in a store with the
same terms (`hn`). -/
syntax "congr_one " ident ppSpace term : tactic
macro_rules
  | `(tactic| congr_one $h $hn) => `(tactic| exact Represents.congr $h $hn)

/-- Two handles are equal exactly when what they stand for is. -/
syntax "rep_iff " term:max ppSpace term:max ppSpace term:max : tactic
macro_rules
  | `(tactic| rep_iff $hinv $ha $hb) => `(tactic| exact Represents.eq_iff $hinv $ha $hb)

/-- A value that a handle stands for is one that a store can hold. -/
syntax "valid_tac " ident ppSpace ident : tactic
macro_rules
  | `(tactic| valid_tac $hinv $h) => `(tactic| first
    | exact Store.Rep.valid $hinv $h
    | exact Represents.valid_proof $hinv $h
    | trivial)

/-- What is proved of a function, where the same is wanted with the
result's cases written another way. -/
syntax "spec_exact " term : tactic
macro_rules
  | `(tactic| spec_exact $e) =>
    `(tactic| (
      apply WP.dspec_mono $e
      rintro ⟨r, s'⟩ h
      cases r <;> simpa [WP.uncurry'_pair] using h))

/-- `__eo_eq` of two terms that are not stuck, as the case functions write
it (`a = b`; `eo_eq_of_ne` has it the other way round). -/
theorem eo_eq_dec (a b : Eo.Term) (ha : a ≠ Eo.Term.Stuck) (hb : b ≠ Eo.Term.Stuck) :
    Eo.__eo_eq a b = Eo.Term.Boolean (decide (a = b)) := by
  rw [eo_eq_of_ne a b ha hb]; simp [eq_comm]

theorem eo_and_bool (a b : Bool) :
    Eo.__eo_and (Eo.Term.Boolean a) (Eo.Term.Boolean b) = Eo.Term.Boolean (a && b) := by
  rfl

open Lean Meta Elab Tactic in
/-- Takes apart each hypothesis `Valid.valid x` with `simp`: an
application's parts, and an operator's indices (the generated
`Valid.uop<k>`), are not stuck. -/
elab "valid_hyps" : tactic => withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    if (← instantiateMVars d.type).isAppOf ``Valid.valid then
      try evalTactic (← `(tactic| simp at $(mkIdent d.userName):ident))
      catch _ => pure ()
  -- and each conjunction among the hypotheses taken apart
  let mut fuel := 1000
  while fuel > 0 do
    fuel := fuel - 1
    let g ← getMainGoal
    let conj ← g.withContext do
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if (← instantiateMVars d.type).isAppOfArity ``And 2 then
          return some d.fvarId
      return none
    match conj with
    | none => break
    | some h =>
      let gs ← g.cases h
      replaceMainGoal (gs.map (·.mvarId)).toList

/-- `logos_eq` for a case whose repeated variables logos tests with one
`__eo_requires` of a conjunction of `__eo_eq`s, and the case function with
a nest of `if`s: both made `if c₁ ∧ … ∧ cₖ then … else stuck`, the
`__eo_eq`s decided from what `Valid` says is not stuck. A nest of many `if`s
is too much for `split_ifs` and `simp_all`. The other branches (a stuck
argument, a pattern that fails) by `simp_all`. -/
syntax "logos_eq_req" : tactic

/-- `logos_eq` where both sides have a match left after one split (a case
of the case form whose pattern another of logos's cases excludes, by a
hypothesis of the split: the bitblast steps): every match split, then
`simp_all`, then a hypothesis that makes the rest absurd
(`absurd_match`). -/
syntax "logos_eq_split" : tactic

/-- Closes the statement that logos's function is what the generated body
does, after both sides are unfolded: by cases on the function's
arguments; a function of one body, by its definition; last, a case that
tests many repeated variables (`logos_eq_req`). -/
macro "logos_eq" : tactic =>
  `(tactic| first
    | (split <;> simp_all [HasStuck.stuck]; done)
    | (split <;> simp_all [HasStuck.stuck, requires_ite] <;> (try split_ifs) <;>
        simp_all [eo_eq_of_ne, eo_eq_true]; done)
    | (split <;> simp_all [HasStuck.stuck, requires_ite, eo_logos_eq] <;> (try split_ifs) <;>
        simp_all [eo_eq_of_ne, eo_eq_true, eo_logos_eq]; done)
    | rfl
    | logos_eq_req
    | logos_eq_split)

open Lean Meta Elab Tactic in
/-- Closes a goal that a hypothesis makes absurd: one of the form
`∀ xs, a = x → … → ¬b = y`, which a match split leaves when a pattern did
not match, is contradicted by taking each `x` to be what it is equated
with. -/
elab "absurd_match" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let st ← saveState
    try
      let gs ← (← g.exfalso).apply d.toExpr
      for g2 in gs do
        unless ← g2.isAssigned do g2.refl
      replaceMainGoal []
      return
    catch _ => st.restore
  throwError "absurd_match: no hypothesis makes the goal absurd"

-- (after `absurd_match`, which the rule names)
macro_rules
  | `(tactic| logos_eq_split) =>
    `(tactic| (((repeat' split) <;>
        (try simp_all [HasStuck.stuck, requires_ite, eo_eq_of_ne, eo_logos_eq]) <;>
        (try (intros; absurd_match))) <;> done))

/-- `logos_eq` for a function of logos that falls through to helpers
(`__eo_l_<k>___f`) when the repeated variables of a case differ, with the
helpers unfolded: every match split, the connectives simplified, and what
is left closed by symmetry or by a pattern that did not match
(`absurd_match`). -/
macro "logos_eq_deep" : tactic =>
  `(tactic| first
    | logos_eq
    | (((repeat' split) <;>
        (try simp_all [HasStuck.stuck, requires_ite, eo_eq_of_ne, eo_logos_eq]) <;>
        (try split_ifs) <;> (try simp_all [eo_eq_of_ne, eo_eq_true, eo_logos_eq]) <;>
        (try (intros; simp_all [eq_comm])) <;>
        -- before the next step: its `by simp` fails only after `try` has
        -- let it through
        (try (intros; absurd_match)) <;>
        (try (rename_i hm _; exact absurd hm (by simp)))) <;> done))

/-- A list operator does not nest to the left (`NotLeftNested`): where no
constructor does (CpcMini), or by the constructor of the operator constant. -/
macro "not_left_tac" : tactic =>
  `(tactic| first
    | (intro _ _ _; rfl)
    | (intro c ts h
       simp only [Embed.embedded_enc_Term, Embed.enc_Term, Embed.uop, Tree.node.injEq] at h
       obtain ⟨hc, -⟩ := h
       subst hc
       rfl))

/-- A term is not the stuck term: said by a hypothesis, or plain from its
form. -/
macro "ns_tac" : tactic =>
  `(tactic| first
    | assumption
    | (intro h; cases h)
    | (simp; done)
    -- a strict builder (__eo_mk_uop<k>, __eo_mk_var) of parts the context
    -- says are not stuck: its simp lemmas make it the plain constructor
    | (simp [*]; done))

/-- An argument that the program called assumes OK (Runtime/StateInv.lean)
is: an argument assumed OK, the tail of an OK state, the empty or the stuck
state, what a function that keeps states OK builds from OK states, or the
proof of a formula that is not stuck (one looked up in an OK state among
them). -/
macro "good_tac" : tactic =>
  `(tactic| first
    | solve_by_elim only [*, StateOK.nil, StateOK.stuck, StateOK.tail,
        StateOK.push_proven, StateOK.push_assume_check, StateOK.push_input_assume_check,
        StateOK.invoke_cmd_check_proven, StateOK.invoke_cmd_step_pop, StateOK.invoke_cmd,
        StateOK.invoke_cmd_list, StateOK.invoke_assume_list, ProofOK.pf,
        state_proven_nth_ne_stuck]
    | (apply ProofOK.pf; ns_tac))

/-- Carries the facts named over to a store that has grown. -/
syntax "transport " term " at " (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| transport $hg at $hs*) => do
    let ts ← hs.mapM fun h => `(tactic| carry_one $h $hg)
    `(tactic| ($[$ts];*))

open Lean Meta Elab Tactic in
/-- `drop_names n₁ n₂ …`: clears, in the order given, each of the names
that the goal has and nothing else needs. The generator names what no
later line of a proof uses (a fact about a handle in a store that has
grown since, the handle, the store): what stays in the context is paid for
at every later step. A name that cannot be cleared stays. -/
elab "drop_names" hs:(ppSpace colGt ident)* : tactic => do
  for h in hs do
    let g ← getMainGoal
    let some d := (← g.getDecl).lctx.findFromUserName? h.getId | continue
    replaceMainGoal [← g.tryClear d.fvarId]

open Lean Meta Elab Tactic in
/-- Where the program of the goal is a call of a `more_<k>` function, the
rest of a long generated function (rust-meta ends a function after twelve
fallible calls with a call of the next), unfolds it. The tactics that take
a statement off the program end with this, so the goal holds the function
at hand and not the whole case. -/
elab "open_more" : tactic => do
  let g :: _ ← getUnsolvedGoals | return
  let t := (← instantiateMVars (← g.getType)).consumeMData
  for a in t.getAppArgs do
    let .const n@(.str _ last) _ := a.getAppFn | continue
    unless last.startsWith "more_" do continue
    -- (`unfold`, not `delta`: a function of a recursive group unfolds by
    -- its equation, to calls of the group's functions by name)
    evalTactic (← `(tactic| unfold $(mkCIdent n):ident))
    return

/-- `store_step with spec as ⟨v, s', hinv, h⟩ growing hG carrying h1 h2 …
dropping n1 n2 …`: one operation on the store whose specification `spec`
says that the new store has the invariant, has grown, and what the result
is on `Ok`. Leaves the `Ok` case with the result `v`, the store `s'`, its
invariant `hinv` and the fact `h` about `v`; `hG` is extended, and the
facts after `carrying` are carried over. An `Err` ends the function, with
nothing to prove about its result. The names after `dropping` are those
that no later line uses: they are cleared (`drop_names`), before the step
but for those that `spec` names, which go after it. -/
syntax "store_step " "with " term " as " "⟨" ident ", " ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " dropping" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| store_step with $e as ⟨$v, $s', $hinv, $h⟩ growing $hG carrying $hs*
      dropping $ds*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    -- what the specification names is cleared after the step, the rest before
    let mut used : Array Lean.Name := #[]
    for stx in e.raw.topDown do
      if stx.isIdent then used := used.push stx.getId
    let pre := ds.filter fun d => !used.contains d.getId
    `(tactic| (
      drop_names $pre*
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b h)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $v:ident
      simp only at $h:ident ⊢
      clear $hg
      drop_names $ds*
      open_more))

/-- Closes what is left where a pattern does not match. -/
macro "nm_close" : tactic =>
  `(tactic| first
    | rfl
    | (simp_all; done)
    | (injections; simp_all; done)
    | (injections; subst_vars; simp_all; done)
    | (simp_all [eq_comm]; done)
    | (simp_all; exact fun h => (by assumption : ¬ _) h.symm))

/-- `nat_no_match h hinv hG in cd`: as `no_match`, where `h` says that a
natural number is not `0` (`x ≠ 0`) or not a successor (`∀ m, x ≠ m + 1`):
each arm of the case's match either is `none` or has its own equation for
the number, against `h`. (`simp_all` can loop on such a goal.) -/
syntax "nat_no_match " ident ppSpace ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| nat_no_match $h $hinv $hG in $cd) =>
    `(tactic| (
      simp only [uncurry_apply_pair, ite_true, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, ?_⟩
      unfold $cd
      split <;> first
        | rfl
        | (exfalso; apply $h; first | rfl | assumption)))

/-- Ends a case at a place where its pattern does not match: the store has
the invariant `hinv` and has grown as `hG` says, and the case's function
`cd` (of the generated case file) answers `none`. The last is found by
unfolding it and using the hypotheses in sight: what `unapply` said of a
term that is not an application, what a comparison of two handles said of
the terms they stand for. -/
syntax "no_match " ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| no_match $hinv $hG in $cd) =>
    `(tactic| (
      simp only [Std.bind_ok, uncurry_apply_pair, ite_true, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, ?_⟩
      unfold $cd
      first
        | (split <;> nm_close)
        | (simp_all; done)))

/-- `no_match_ne hne hinv hG in cd`: `no_match`, where the pattern failed
because two of its terms differ (`hne : ¬x = y`, from `pat_same`). The case's
function is the pattern made linear, its repeated variables a nest of `if`s
over `none`; `hne` makes one of them false and `ite_self` the rest `none`.
`nm_close`'s `simp_all` can run out of steps on such a nest with a large
context. -/
syntax "no_match_ne " term:max ppSpace ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| no_match_ne $hne $hinv $hG in $cd) =>
    `(tactic| (
      have hne := $hne
      simp only [Std.bind_ok, uncurry_apply_pair, ite_true, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, ?_⟩
      unfold $cd
      first
        | (split <;> first
            | rfl
            -- `injections` stops a few constructors deep: a pattern's
            -- equation can be deeper
            | (iterate 40 (try injections)
               subst_vars
               simp only [hne, Ne.symm hne, ite_false, ite_true, ite_self]; done)
            | nm_close)
        | (simp_all; done)))

/-- `pat_unapply h as ⟨f, a, x, y, hf, ha, hnf, hna⟩ using hinv else hinv hG in cd`:
the pattern takes the term that `h` speaks of apart as an application.
Goes on with the two handles `f` and `a`, the two terms `x` and `y`, what
the handles stand for, and that neither term is stuck; where the term is
not an application the case ends (`no_match`). -/
syntax "pat_unapply " ident " as " "⟨" ident ", " ident ", " ident ", " ident ", " ident ", "
  ident ", " ident ", " ident "⟩" " using " ident " else " ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| pat_unapply $h as ⟨$f, $a, $x, $y, $hf, $ha, $hnf, $hna⟩ using $hi
      else $hinv $hG in $cd) =>
    `(tactic| (
      rcases Store.Rep.unapply $h with ⟨$f, $a, $x, $y, heq, $hf, $ha, hu⟩ | ⟨hne, hu⟩
      case inr => (rw [hu]; no_match $hinv $hG in $cd)
      subst heq
      rw [hu]
      simp only [Std.bind_ok, uncurry_apply_pair]
      clear hu
      obtain ⟨$hnf, $hna⟩ := Store.Rep.apply_ne_stuck $hi $h
      open_more))

/-- `pat_is_node h : x is v by inv else hinv hG in cd`: the pattern asks
whether the term `x` that `h` speaks of is the constant `v`, a constructor
without fields that the store keeps as a node (`is_node`); `inv` is the
inversion of its encoding. Goes on with `x` replaced by `v`; where it is
another term the case ends. -/
syntax "pat_is_node " ident " : " ident " is " term " by " term " else " ident ppSpace ident
  " in " ident : tactic
macro_rules
  | `(tactic| pat_is_node $h : $x is $v by $inv else $hinv $hG in $cd) =>
    `(tactic| (
      obtain ⟨b, hb, hbiff⟩ := Store.is_node_holds _ $h.1
      rw [hb]
      simp only [Std.bind_ok]
      have hiff : b = true ↔ $x = $v := hbiff.trans
        ⟨fun ⟨_, he⟩ => ($inv (by simpa only [Embed.embedded_enc_Term] using he) $h.2).1,
         fun he => ⟨_, by subst he; rfl⟩⟩
      clear hb hbiff
      cases b
      case false => (
        have hv : $x ≠ $v := fun he => by simpa using hiff.mpr he
        clear hiff
        (try simp only [Bool.not_false, Bool.false_eq_true, ite_true, ite_false])
        no_match $hinv $hG in $cd)
      have hv : $x = $v := hiff.mp rfl
      clear hiff
      (try simp only [Bool.not_true, Bool.false_eq_true, ite_true, ite_false])
      subst hv
      open_more))

/-- `pat_destruct lemma h as ⟨v, x, hv⟩ … else hinv hG in cd`: the pattern
takes the value that `h` speaks of apart as a constructor with fields, by
the constructor's `destruct` lemma. Goes on with a handle `v`, the value
`x` it stands for and the fact `hv`, for each field; where the value is
not of that constructor the case ends. -/
syntax "pat_destruct " term " as" (" ⟨" ident ", " ident ", " ident "⟩")* " else " ident ppSpace
  ident " in " ident : tactic
macro_rules
  | `(tactic| pat_destruct $l as $[⟨$vs, $xs, $hs⟩]* else $hinv $hG in $cd) => do
    let k := vs.size
    let fs := (List.range k).toArray.map fun i => Lean.mkIdent (Lean.Name.mkSimple s!"fld{i}")
    let vec := Lean.mkIdent `fldvec
    let hvec := Lean.mkIdent `hfldvec
    let hvi := Lean.mkIdent `hfld
    let heq := Lean.mkIdent `hfldeq
    let hd := Lean.mkIdent `hflddes
    let pats : Array (Lean.TSyntax `rcasesPat) ←
      (fs ++ #[vec] ++ xs ++ #[heq, hvec] ++ hs ++ #[hd]).mapM
        fun i => `(rcasesPat| $i:ident)
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let steps ← (vs.zip fs).mapM fun (v, f) =>
      `(tactic| (
        step as ⟨$(b v), $(b hvi)⟩
        have hfldv : $v = $f := by simp [$hvi:ident, $hvec:ident]
        subst hfldv
        clear $hvi))
    `(tactic| (
      rcases ($l) with ⟨$pats,*⟩ | ⟨hne, $hd:ident⟩
      case inr => (rw [$hd:ident]; no_match $hinv $hG in $cd)
      subst $heq
      rw [$hd:ident]
      simp only [Std.bind_ok, uncurry_apply_pair]
      clear $hd
      have hfldlen : ($vec).length = $(Lean.quote k) := by
        simp [alloc.vec.Vec.length, $hvec:ident]
      $[$steps];*
      clear hfldlen
      open_more))

/-- `pat_destruct_lit spec as ⟨v, x, hv⟩ storing ⟨s', hinv'⟩ growing hG carrying … else in
cd`: the pattern takes apart an object literal, by `destruct` with its
constructor, which stores a native copy of the literal's value (`spec`
says what it gives; see `Runtime/Literals.lean`). Goes on with the handle
`v` of the native value `x`, the fact `hv`, and the new store; where the
term is no such literal the case ends. -/
syntax "pat_destruct_lit " term " as " "⟨" ident ", " ident ", " ident "⟩" " storing " "⟨" ident
  ", " ident "⟩" " growing " ident " carrying" (ppSpace colGt ident)* " in " ident : tactic
macro_rules
  | `(tactic| pat_destruct_lit $e as ⟨$v, $x, $hv⟩ storing ⟨$s', $hinv'⟩ growing $hG
      carrying $hs* in $cd) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    let hres := Lean.mkIdent `hres
    let vec := Lean.mkIdent `fldvec
    let hvec := Lean.mkIdent `hfldvec
    let f0 := Lean.mkIdent `fld0
    let heq := Lean.mkIdent `hfldeq
    let hvi := Lean.mkIdent `hfld
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv'), $(b hg), $(b hres)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      rcases $r:ident with (_ | $vec:ident) | _
      all_goals first
        | (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv', $hG, trivial⟩; done)
        | (simp only at $hres:ident; nat_no_match $hres $hinv' $hG in $cd; done)
        | (simp only at $hres:ident; no_match $hinv' $hG in $cd; done)
        | skip
      simp only at $hres:ident ⊢
      obtain ⟨$f0, $x, $heq, $hvec, $hv⟩ := $hres
      subst $heq
      have hfldlen : ($vec).length = 1 := by simp [alloc.vec.Vec.length, $hvec:ident]
      step as ⟨$(b v), $(b hvi)⟩
      have hfldv : $v = $f0 := by simp [$hvi:ident, $hvec:ident]
      subst hfldv
      clear $hvi hfldlen
      open_more))

/-- `pat_destruct_lit2 spec as ⟨v, x, hv⟩ ⟨w, y, hw⟩ storing ⟨s', hinv'⟩ growing hG
carrying … in cd`: as `pat_destruct_lit`, for a literal whose `destruct`
stores two native values (a binary literal: its width and its value; see
`Runtime/StringLits.lean`). -/
syntax "pat_destruct_lit2 " term " as " "⟨" ident ", " ident ", " ident "⟩" " ⟨" ident ", "
  ident ", " ident "⟩" " storing " "⟨" ident ", " ident "⟩" " growing " ident " carrying"
  (ppSpace colGt ident)* " in " ident : tactic
macro_rules
  | `(tactic| pat_destruct_lit2 $e as ⟨$v, $x, $hv⟩ ⟨$w, $y, $hw⟩ storing ⟨$s', $hinv'⟩
      growing $hG carrying $hs* in $cd) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    let hres := Lean.mkIdent `hres
    let vec := Lean.mkIdent `fldvec
    let hvec := Lean.mkIdent `hfldvec
    let f0 := Lean.mkIdent `fld0
    let f1 := Lean.mkIdent `fld1
    let heq := Lean.mkIdent `hfldeq
    let hvi := Lean.mkIdent `hfld
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv'), $(b hg), $(b hres)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      rcases $r:ident with (_ | $vec:ident) | _
      all_goals first
        | (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv', $hG, trivial⟩; done)
        | (simp only at $hres:ident; no_match $hinv' $hG in $cd; done)
        | skip
      simp only at $hres:ident ⊢
      obtain ⟨$f0, $f1, $x, $y, $heq, $hvec, $hv, $hw⟩ := $hres
      subst $heq
      have hfldlen : ($vec).length = 2 := by simp [alloc.vec.Vec.length, $hvec:ident]
      step as ⟨$(b v), $(b hvi)⟩
      have hfldv : $v = $f0 := by simp [$hvi:ident, $hvec:ident]
      subst hfldv
      clear $hvi
      step as ⟨$(b w), $(b hvi)⟩
      have hfldw : $w = $f1 := by simp [$hvi:ident, $hvec:ident]
      subst hfldw
      clear $hvi hfldlen
      open_more))

/-- `pat_native_zero spec storing ⟨s', hinv'⟩ growing hG carrying … in cd`:
the pattern `nat.zero` on a natural number, which stores the numeral 0
(`spec` says what it gives; see `Runtime/Nats.lean`). Goes on with the
number replaced by `0` and the new store; where it is another number the
case ends. -/
syntax "pat_native_zero " term " storing " "⟨" ident ", " ident "⟩" " growing " ident
  " carrying" (ppSpace colGt ident)* " in " ident : tactic
macro_rules
  | `(tactic| pat_native_zero $e storing ⟨$s', $hinv'⟩ growing $hG carrying $hs* in $cd) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    let hres := Lean.mkIdent `hres
    let vec := Lean.mkIdent `fldvec
    let heq := Lean.mkIdent `hfldeq
    let hvec := Lean.mkIdent `hfldvec
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv'), $(b hg), $(b hres)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      rcases $r:ident with (_ | $vec:ident) | _
      all_goals first
        | (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv', $hG, trivial⟩; done)
        | (simp only at $hres:ident ⊢
           obtain ⟨$heq, $hvec⟩ := $hres
           subst $heq
           clear $hvec $vec:ident)
        | (simp only at $hres:ident; nat_no_match $hres $hinv' $hG in $cd; done)
      open_more))

/-- `pat_same a b with ha hb using hi else hinv hG in cd`: the generated
`if a != b { return Ok(None) }` on two handles. Goes on where they are
equal, with the values they stand for made one; where they differ the
case ends. -/
syntax "pat_same " ident ppSpace ident " with " ident ppSpace ident " using " ident
  " else " ident ppSpace ident " in " ident : tactic
macro_rules
  | `(tactic| pat_same $a $b with $ha $hb using $hi else $hinv $hG in $cd) =>
    `(tactic| (
      rw [Term.ne_eq]
      simp only [Std.bind_ok]
      have hiff := Represents.eq_iff $hi $ha $hb
      rcases Decidable.em ($a = $b) with hv | hv
      case inr => (
        rw [show decide ($a ≠ $b) = true from by simpa using hv]
        no_match_ne (hiff.not.mp hv) $hinv $hG in $cd)
      rw [show decide ($a ≠ $b) = false from by simp [hv]]
      simp only [Bool.false_eq_true, ite_false]
      have hx := hiff.mp hv
      clear hiff
      first | subst hx | skip
      open_more))

/-- Ends a case that matched: the result `h` speaks of is what the case's
function `cd` answers. -/
syntax "case_done " ident ppSpace ident " with " ident " in " ident " using"
  (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| case_done $hinv $hG with $h in $cd using $facts*) =>
    `(tactic| (
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, _, ?_, $h⟩
      first
        | (simp [$cd:ident, $[$facts:ident],*]; done)
        | (unfold $cd; split <;> simp_all; done)
        -- a result that has the term `eo::requires` compared, where logos
        -- has the one it was compared with
        | (unfold $cd; split <;> (try simp only [requires_ite]) <;> (try split_ifs) <;>
            simp_all; done)
        -- the same where the case builds a variable with `__eo_mk_var` and
        -- logos writes `Term.Var`, and where `simp_all` leaves the
        -- equations of a matched term as a conjunction
        | (unfold $cd; split <;> (try simp only [requires_ite]) <;> (try split_ifs) <;>
            (try simp only [mk_var_of_ne, ne_eq, reduceCtorEq, not_false_eq_true] at *) <;>
            (try simp_all) <;> (try casesm* _ ∧ _) <;> (try subst_vars) <;> simp_all; done)))

/-- Ends a case of a loop that goes round again: the handles `hs` speak of
are the arguments of the next round. -/
syntax "case_again " ident ppSpace ident " with" (ppSpace colGt ident)* " in " ident " using"
  (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| case_again $hinv $hG with $hs* in $cd using $facts*) => do
    let holes ← (hs ++ hs).mapM fun _ => `(_)
    `(tactic| (
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, $holes,*, rfl, $hs,*, ?_⟩
      first
        | (simp [$cd:ident, $[$facts:ident],*]; done)
        | (unfold $cd; split <;> simp_all; done)))

/-- `case_again … goods k`: as `case_again`, for a loop whose `k` state
arguments are assumed OK (Runtime/StateInv.lean): the next round's states
are OK too, by `good_tac`. -/
syntax "case_again " ident ppSpace ident " with" (ppSpace colGt ident)* " goods " num " in "
  ident " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| case_again $hinv $hG with $hs* goods $k in $cd using $facts*) => do
    let holes ← (hs ++ hs).mapM fun _ => `(_)
    let gs ← (List.range k.getNat).toArray.mapM fun _ => `(by good_tac)
    `(tactic| (
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, $holes,*, rfl, $hs,*, $gs,*, ?_⟩
      first
        | (simp [$cd:ident, $[$facts:ident],*]; done)
        | (unfold $cd; split <;> simp_all; done)))

/-! ## A requirement

`eo::requires a b r` is a function of its own in the Rust: equal handles,
not stuck, then `r`. The generated proof states what the function gives (a
handle of logos's `__eo_requires`) and proves it in place. -/

/-- The test `if a != b { return Ok(s.stuck()) }` of a requirement. -/
syntax "req_same " ident ppSpace ident " with " ident ppSpace ident " using " ident ppSpace ident :
  tactic
macro_rules
  | `(tactic| req_same $a $b with $ha $hb using $hinv $hG) =>
    `(tactic| (
      rw [Term.ne_eq]
      simp only [Std.bind_ok]
      have hiff := Represents.eq_iff $hinv $ha $hb
      rcases Decidable.em ($a = $b) with hv | hv
      case inr => (
        rw [show decide ($a ≠ $b) = true from by simpa using hv]
        simp only [ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨$hinv, $hG, ?_⟩
        rw [requires_ne _ _ _ (fun h => hv (hiff.mpr h))]
        exact Store.Inv.rep_stuck $hinv)
      rw [show decide ($a ≠ $b) = false from by simp [hv]]
      simp only [Bool.false_eq_true, ite_false]
      have hx := hiff.mp hv
      clear hiff
      first | subst hx | skip))

/-- The test for the stuck term of a requirement. -/
syntax "req_stuck " ident " as " ident " using " ident ppSpace ident : tactic
macro_rules
  | `(tactic| req_stuck $h as $hq using $hinv $hG) =>
    `(tactic| (
      rw [Store.Rep.is_stuck $h]
      simp only [Std.bind_ok]
      split
      case isTrue => (
        rename_i hq0
        simp only [decide_eq_true_eq] at hq0
        simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨$hinv, $hG, ?_⟩
        first
          -- the whole requirement at once: rewriting with `hq0` alone
          -- fails when the third argument depends on proofs that the
          -- stuck test's term is not stuck
          | (rw [requires_stuck_of hq0]; exact Store.Inv.rep_stuck $hinv)
          | simpa [requires_ite, hq0] using Store.Inv.rep_stuck $hinv)
      rename_i hq0
      simp only [decide_eq_true_eq] at hq0
      have $hq:ident := hq0
      clear hq0))

/-- The end of a requirement that holds: its third argument. -/
syntax "req_done " ident ppSpace ident " with " ident " using " ident : tactic
macro_rules
  | `(tactic| req_done $hinv $hG with $h using $hq) =>
    `(tactic| (
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨$hinv, $hG, ?_⟩
      first
        | (rw [requires_eq _ _ $hq]; exact $h)
        -- the two sides are equal terms that `req_same` could not
        -- substitute (neither is a variable): by its equation
        | (rw [requires_ite, if_pos (by assumption), if_neg $hq]; exact $h)))

/-! ## A conditional

`eo::ite c a b` (and the native `ite`) is a function of its own in the
Rust, `if_k`: the Boolean of the condition, then the branch it names. The
generated proof states what the function gives (a handle of logos's
`__eo_ite`, or `native_ite`) and proves it in place, a bullet per
branch. -/

/-- Enters a branch of a conditional: the Boolean the condition stands for
is the one `hbv` says. -/
syntax "ite_branch " term : tactic
macro_rules
  | `(tactic| ite_branch $hbv) =>
    `(tactic| (
      rw [$hbv:term]
      simp only [Std.bind_ok, Bool.false_eq_true, ite_true, ite_false, ↓reduceIte]))

/-- Ends a branch: its result is the conditional's, by `h`. -/
syntax "ite_done " ident ppSpace ident " with " term : tactic
macro_rules
  | `(tactic| ite_done $hinv $hG with $h) =>
    `(tactic| (
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨$hinv, $hG, $h⟩))

/-- Ends a conditional whose condition is no Boolean: the stuck term. -/
syntax "ite_stuck " ident ppSpace ident " with " term : tactic
macro_rules
  | `(tactic| ite_stuck $hinv $hG with $hx) =>
    `(tactic| (
      simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨$hinv, $hG, eo_ite_stuck_rep _ _ $hx (Store.Inv.rep_stuck $hinv)⟩))

/-! ## Bodies -/

/-- The first of the cases that answers, else `d`: what a generated body
computes, in the functions of the generated case file. -/
def firstSome {α : Type} : List (Option α) → α → α
  | [], d => d
  | some r :: _, _ => r
  | none :: rest, d => firstSome rest d

@[simp] theorem firstSome_nil {α : Type} (d : α) : firstSome [] d = d := rfl
@[simp] theorem firstSome_some {α : Type} (r : α) (rest : List (Option α)) (d : α) :
    firstSome (some r :: rest) d = r := rfl
@[simp] theorem firstSome_none {α : Type} (rest : List (Option α)) (d : α) :
    firstSome (none :: rest) d = firstSome rest d := rfl

theorem firstSome_ite {α : Type} (c : Prop) [Decidable c] (r d : α) :
    firstSome [if c then some r else none] d = if c then r else d := by
  split <;> rfl

-- (after `firstSome_ite`, which the rule names)
macro_rules
  | `(tactic| logos_eq_req) =>
    `(tactic| (
    split
    all_goals first
      | (valid_hyps
         simp (disch := assumption) only [eo_eq_dec, eo_and_bool, requires_ite,
           Eo.Term.Boolean.injEq, Bool.and_eq_true, decide_eq_true_eq, reduceCtorEq,
           ite_false, ← ite_and, firstSome_ite, and_assoc]
         split_ifs <;> first | rfl | contradiction
         done)
      | (simp_all [HasStuck.stuck]; done)
      | (split <;> simp_all [HasStuck.stuck]; done)))

theorem firstSome_append {α : Type} (l₁ l₂ : List (Option α)) (d : α) :
    firstSome (l₁ ++ l₂) d = firstSome l₁ (firstSome l₂ d) := by
  induction l₁ with
  | nil => rfl
  | cons o l ih => cases o <;> simp [firstSome, ih]

/-! ## Large functions

`logos_eq` splits logos's match and, in every branch, simplifies the whole
list of cases: quadratic in simp's steps, and too much for a function of
hundreds of cases (`__eo_typeof`, 209). `logos_eq_large` proves the same
statement by evaluation, with no `simp`, no `split` and no equation lemma
of logos's function or of its match (Lean takes a minute to make
`__eo_typeof`'s, and does not finish making those of the match of
`__eo_cmd_step_proven`, 617 cases).

It goes down the list that `firstSome` tries. A case that evaluates to
`none` on the arguments is dropped; one that evaluates to `some v` ends the
list with `v`; one that does not evaluate, since it matches on a variable,
is kept. With cases kept, it takes cases of the variable the first of them
waits for, and goes on in each branch with the cases kept, which are few
after the first step. With none kept, logos's function evaluates to the
same value, or waits for a variable in turn. Every step is a lemma about
`firstSome` whose hypothesis holds by `rfl`. -/

theorem firstSome_drop {α : Type} {o : Option α} {rest : List (Option α)} {d x : α}
    (h : o = none) (h' : firstSome rest d = x) : firstSome (o :: rest) d = x := by
  subst h; exact h'

theorem firstSome_hit {α : Type} {o : Option α} {rest : List (Option α)} {d v : α}
    (h : o = some v) : firstSome (o :: rest) d = firstSome [] v := by
  subst h; rfl

theorem firstSome_keep {α : Type} {o : Option α} {rest rest' : List (Option α)} {d d' : α}
    (h : firstSome rest d = firstSome rest' d') :
    firstSome (o :: rest) d = firstSome (o :: rest') d' := by
  cases o
  · exact h
  · rfl

namespace LogosEqLarge
open Lean Elab Tactic Meta

/-- The variable that the evaluation of `e` waits for: the one that a
recursor or a match in it is applied to. -/
meta partial def stuckFVar? (e : Expr) (fuel : Nat := 24) : MetaM (Option FVarId) := do
  if fuel == 0 then return none
  let e ← whnf e
  if e.isFVar then return some e.fvarId!
  if let .proj _ _ s := e then return ← stuckFVar? s (fuel - 1)
  let .const n _ := e.getAppFn | return none
  let args := e.getAppArgs
  let env ← getEnv
  if let some (.recInfo r) := env.find? n then
    if h : r.getMajorIdx < args.size then return ← stuckFVar? args[r.getMajorIdx] (fuel - 1)
    return none
  if isCasesOnRecursor env n then
    if let some (.inductInfo i) := env.find? n.getPrefix then
      let idx := i.numParams + 1 + i.numIndices
      if h : idx < args.size then return ← stuckFVar? args[idx] (fuel - 1)
    return none
  if (← getMatcherInfo? n).isSome then
    if let .stuck e' ← reduceMatcher? e then
      if e' != e then return ← stuckFVar? e' (fuel - 1)
    return none
  if (env.find? n).any (·.isCtor) then return none
  -- another function that does not reduce (a recursive function, a
  -- decision, a comparison): one of its arguments is what it waits for
  for a in args.reverse do
    let ty ← whnf (← inferType a)
    if ty.isSort || ty.isForall then continue
    if let some x ← stuckFVar? a (fuel - 1) then return some x
  return none

/-- `(l', d', pf)` with `pf : firstSome l d = firstSome l' d'`, where `l'`
has the cases of `l` that do not evaluate, up to the first that answers
(`d'` is its answer, then). -/
meta partial def filter (α l d : Expr) : MetaM (Expr × Expr × Expr) := do
  let optα := mkApp (mkConst ``Option [Level.zero]) α
  let fs (l d : Expr) := mkApp3 (mkConst ``firstSome) α l d
  let refl (o : Expr) := mkApp2 (mkConst ``Eq.refl [Level.one]) optα o
  -- a long list is written with `let`s
  let l ← whnfCore l
  match_expr l with
  | List.cons _ o rest =>
    let o' ← whnf o
    if o'.isAppOfArity ``Option.none 1 then
      let (l', d', pf) ← filter α rest d
      return (l', d', mkApp7 (mkConst ``firstSome_drop) α o rest d (fs l' d') (refl o') pf)
    else if o'.isAppOfArity ``Option.some 2 then
      let v := o'.appArg!
      return (mkApp (mkConst ``List.nil [Level.zero]) optα, v,
        mkApp6 (mkConst ``firstSome_hit) α o rest d v (refl o'))
    else
      let (l', d', pf) ← filter α rest d
      return (mkApp3 (mkConst ``List.cons [Level.zero]) optα o l', d',
        mkApp7 (mkConst ``firstSome_keep) α o rest l' d d' pf)
  | _ => return (l, d, mkApp2 (mkConst ``Eq.refl [Level.one]) α (fs l d))

/-- The goals of the cases of `x`, a variable of an inductive type that is
no number or string (a case that matches on one of those is not for this
tactic). `depth` bounds the nesting of the cases taken. -/
meta def casesOf (g : MVarId) (x : FVarId) (depth : Nat) : MetaM (Array MVarId) :=
  g.withContext do
    if depth == 0 then
      throwError "logos_eq_large: too many nested cases; the goal is{indentD g}"
    let ty ← whnf (← x.getType)
    let env ← getEnv
    let ok : Bool := match ty.getAppFn with
      | .const n _ => n != ``Nat && n != ``Int && n != ``String &&
          (env.find? n).any (· matches .inductInfo _)
      | _ => false
    unless ok do
      throwError "logos_eq_large: the evaluation waits for {mkFVar x} : {ty}, which has no cases to take"
    return (← g.cases x).map (·.mvarId)

meta partial def go (g : MVarId) (depth : Nat) : MetaM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let some (α, lhs, rhs) := ty.eq?
    | throwError "logos_eq_large: not an equation:{indentExpr ty}"
  if rhs.isAppOfArity ``ite 5 then
    -- a test for the stuck term: decided, or it waits for the argument
    let b ← whnf (mkApp2 (mkConst ``Decidable.decide) (rhs.getArg! 1) (rhs.getArg! 2))
    if b.isConstOf ``Bool.false then
      go (← g.replaceTargetDefEq (← mkEq lhs (rhs.getArg! 4))) depth
    else if b.isConstOf ``Bool.true then
      leaf g lhs (rhs.getArg! 3)
    else
      let some x ← stuckFVar? b
        | throwError "logos_eq_large: the condition does not evaluate:{indentExpr (rhs.getArg! 1)}"
      for s in ← casesOf g x depth do go s (depth - 1)
  else if rhs.isAppOfArity ``firstSome 3 then
    let (l', d', pf) ← filter α (rhs.getArg! 1) (rhs.getArg! 2)
    let g' ← mkFreshExprSyntheticOpaqueMVar
      (← mkEq lhs (mkApp3 (mkConst ``firstSome) α l' d')) (← g.getTag)
    g.assign (← mkEqTrans g' (← mkEqSymm pf))
    match_expr l' with
    | List.cons _ o _ =>
      let some x ← stuckFVar? o
        | throwError "logos_eq_large: the case does not evaluate:{indentExpr o}"
      for s in ← casesOf g'.mvarId! x depth do go s (depth - 1)
    | _ => leaf g'.mvarId! lhs d'
  else leaf g lhs rhs
where
  -- No case is left and the right side is `v` (the goal is `lhs = v` up to
  -- evaluation): logos's function evaluates to it, or waits for a variable.
  leaf (g : MVarId) (lhs v : Expr) : MetaM Unit := g.withContext do
    if ← isDefEq lhs v then
      g.assign (← mkEqRefl lhs)
    else
      let some x ← stuckFVar? lhs
        | throwError "logos_eq_large: the sides differ:{indentExpr lhs}\nand{indentExpr v}"
      for s in ← casesOf g x depth do go s (depth - 1)

end LogosEqLarge

/-- `logos_eq` for a function of very many cases, with nothing unfolded:
by evaluation, taking cases of the variables that the cases match on (see
above). -/
elab "logos_eq_large" : tactic =>
  Lean.Elab.Tactic.liftMetaTactic fun g => do LogosEqLarge.go g 16; return []

/-! ## Groups of cases

A program with more than four cases tries them in groups of four, and the
groups in groups (`cases_<d>_<g>`). A group answers what the first of its
cases that answers does (`∀ d, firstSome [the cases] d = res`), or none of
its cases answers. -/

/-- `group_step with spec as ⟨s', hinv, hc⟩ growing hG carrying … split heq
none pat using …`: a group or a body tries a member (a case or a group)
whose specification is `spec`. If the member answers, so does the whole,
with the same result: `heq` splits the whole's list of cases into those
before the member (which answered `none`, by the facts), the member's and
those after. Goes on where the member answered `none`, with its facts
named by `pat`. -/
syntax "group_step " "with " term " as " "⟨" ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " split " term " otherwise " "⟨" ident,* "⟩"
  " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| group_step with $e as ⟨$s', $hinv, $hc⟩ growing $hG carrying $hs* split $heq
      otherwise ⟨$ns,*⟩ using $facts*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let o := Lean.mkIdent `o
    let hg := Lean.mkIdent `hg
    let ns' := ns.getElems
    let bind ← if ns'.size == 1 then `(tactic| have $(ns'[0]!):ident := $hc)
      else `(tactic| obtain ⟨$ns,*⟩ := $hc)
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b hc)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $o:ident
      cases $o:ident
      case some => (
        simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
        obtain ⟨res, hres, hrep⟩ := $hc
        refine ⟨$hinv, $hG, ?_⟩
        refine ⟨res, fun d => ?_, hrep⟩
        rw [$heq:term, firstSome_append, firstSome_append]
        simp [hres, $[$facts:ident],*])
      simp only at $hc:ident ⊢
      $bind))

/-- The same in a body: the result is the body's. -/
syntax "body_group_step " "with " term " as " "⟨" ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " split " term " otherwise " "⟨" ident,* "⟩"
  " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| body_group_step with $e as ⟨$s', $hinv, $hc⟩ growing $hG carrying $hs* split $heq
      otherwise ⟨$ns,*⟩ using $facts*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let o := Lean.mkIdent `o
    let hg := Lean.mkIdent `hg
    let ns' := ns.getElems
    let bind ← if ns'.size == 1 then `(tactic| have $(ns'[0]!):ident := $hc)
      else `(tactic| obtain ⟨$ns,*⟩ := $hc)
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b hc)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $o:ident
      cases $o:ident
      case some => (
        simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
        obtain ⟨res, hres, hrep⟩ := $hc
        refine ⟨$hinv, $hG, ?_⟩
        rw [$heq:term, firstSome_append, firstSome_append]
        simpa [hres, $[$facts:ident],*] using hrep)
      simp only at $hc:ident ⊢
      $bind))

/-- Ends a group where no member answered: none of its cases does. -/
syntax "group_none " ident ppSpace ident " with " term : tactic
macro_rules
  | `(tactic| group_none $hinv $hG with $h) =>
    `(tactic| (
      simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨$hinv, $hG, $h⟩))

/-- `stuck_check h : x as hs else hinv hG`: the generated
`if s.is_stuck(a)? { return Ok(s.stuck()) }` on a handle of the term `x`.
Goes on with `hs : x ≠ Stuck`; for the stuck term the body ends with the
stuck term. -/
syntax "stuck_check " ident " : " term " as " ident " else " ident ppSpace ident : tactic
macro_rules
  | `(tactic| stuck_check $h : $x as $hs else $hinv $hG) =>
    `(tactic| (
      rw [Store.Rep.is_stuck $h]
      simp only [Std.bind_ok]
      rcases Decidable.em ($x = Eo.Term.Stuck) with $hs | $hs
      case inl => (
        subst $hs
        simp only [decide_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
          WP.uncurry'_pair]
        refine ⟨$hinv, $hG, ?_⟩
        simpa [HasStuck.stuck] using Store.Inv.rep_stuck $hinv)
      simp only [$hs:ident, decide_false, Bool.false_eq_true, ite_false]))

/-- `case_step with spec as ⟨s', hinv, hc⟩ growing hG carrying … using …`: a
body tries a case whose specification is `spec`. If the case answers, the
body ends with its result; goes on where the case answered `none`, with
`hc` saying that its function does. -/
syntax "case_step " "with " term " as " "⟨" ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| case_step with $e as ⟨$s', $hinv, $hc⟩ growing $hG carrying $hs*
      using $facts*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let o := Lean.mkIdent `o
    let hg := Lean.mkIdent `hg
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b hc)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $o:ident
      cases $o:ident
      case some => (
        simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
        obtain ⟨res, hres, hrep⟩ := $hc
        refine ⟨$hinv, $hG, ?_⟩
        simpa [hres, $[$facts:ident],*] using hrep)
      simp only at $hc:ident ⊢))

/-- Ends a body where no case answered: the stuck term. (For a program
with a case for every argument, the hypotheses say that it answered.) -/
syntax "body_stuck " ident ppSpace ident " using" (ppSpace colGt ident)* " in"
  (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| body_stuck $hinv $hG using $facts* in $cds*) =>
    `(tactic| first
      | (simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
         refine ⟨$hinv, $hG, ?_⟩
         simpa [HasStuck.stuck, $[$facts:ident],*] using Store.Inv.rep_stuck $hinv)
      | (exfalso; simp_all [$[$cds:ident],*]; done))

/-- `split_none xs in cds`: no case answered, which cannot be: closes the
goal (after `exfalso`) from the facts that the case functions `cds` gave
`none`, plain or after splitting arguments `xs` into their constructors,
one or several together (for a program whose cases are one per
constructor, or per pair of constructors). -/
syntax "split_none" (ppSpace colGt ident)* " in" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| split_none in $cds*) => `(tactic| (simp_all [$[$cds:ident],*]; done))
  | `(tactic| split_none $x $xs* in $cds*) =>
    `(tactic| first
      | (simp_all [$[$cds:ident],*]; done)
      -- each case of `x` by the rest: the cases may need two variables
      -- split together (`$smtx_dt_num_sels`: the datatype and the index)
      | (cases $x:ident <;> split_none $xs* in $cds*)
      | split_none $xs* in $cds*)

/-- `body_stuck … splitting xs`: for a program whose lemma C gives `default`
where no case applies, the body never gets there. -/
syntax "body_stuck " ident ppSpace ident " using" (ppSpace colGt ident)* " in"
  (ppSpace colGt ident)* " splitting" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| body_stuck $_hinv $_hG using $_facts* in $cds* splitting $xs*) =>
    `(tactic| (exfalso; split_none $xs* in $cds*))

/-! ## Loops -/

/-- `peel_last h then tac`: the goal is `h` but for its last part, under the
same `∃` and `∧`. Takes both apart as far as they go and runs `tac` with
the last part of `h` as `hlast`. -/
syntax "peel_last " ident " then " tacticSeq : tactic
macro_rules
  | `(tactic| peel_last $h then $t) => do
    let hlast := Lean.mkIdent `hlast
    `(tactic| first
      | (obtain ⟨w, h'⟩ := $h
         refine ⟨w, ?_⟩
         peel_last h' then ($t))
      | (have $hlast := $h
         ($t)))

/-- The `tick` that begins a round of a loop. -/
syntax "tick_step " "as " "⟨" ident ", " ident "⟩" " growing " ident " carrying"
  (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| tick_step as ⟨$s', $hinv⟩ growing $hG carrying $hs*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    let hbud := Lean.mkIdent `hbud
    `(tactic| (
      step with Store.tick_spec as ⟨$(b r), $(b s'), hn, hh, hs, hc, hj, hl, hd, hb, $(b hbud)⟩
      have $hinv : Store.Inv $s' := Store.Inv.congr (by assumption) hn hh hs hc hj
      have $hg : Store.Grows _ $s' := ⟨by rw [hn], hl, hd, hb⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg hn hh hs hc hj hl hd hb
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      simp only at $hbud:ident ⊢))

/-- `case_step` in a round of a loop: a case that answers either ends the
loop with a result or names the arguments of the next round, on which the
program has the same result. -/
syntax "round_step " "with " term " as " "⟨" ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| round_step with $e as ⟨$s', $hinv, $hc⟩ growing $hG carrying $hs*
      using $facts*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let o := Lean.mkIdent `o
    let nx := Lean.mkIdent `nx
    let hlast := Lean.mkIdent `hlast
    let hg := Lean.mkIdent `hg
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b hc)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $o:ident
      cases $o:ident
      case some => (
        rename_i $nx:ident
        cases $nx:ident
        case Done => (
          simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
          obtain ⟨res, hres, hrep⟩ := $hc
          refine ⟨$hinv, $hG, ?_⟩
          simpa [hres, $[$facts:ident],*] using hrep)
        case Again => (
          simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
          refine ⟨$hinv, $hG, by assumption, ?_⟩
          peel_last $hc then simp [$hlast:ident, $[$facts:ident],*]))
      simp only at $hc:ident ⊢))

/-- `group_step` in a group of a loop's cases: a member that answers either
ends the loop with a result or names the arguments of the next round, on
which the program has the same result. -/
syntax "group_round_step " "with " term " as " "⟨" ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " split " term " otherwise " "⟨" ident,* "⟩"
  " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| group_round_step with $e as ⟨$s', $hinv, $hc⟩ growing $hG carrying $hs* split $heq
      otherwise ⟨$ns,*⟩ using $facts*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let o := Lean.mkIdent `o
    let nx := Lean.mkIdent `nx
    let hlast := Lean.mkIdent `hlast
    let hg := Lean.mkIdent `hg
    let ns' := ns.getElems
    let bind ← if ns'.size == 1 then `(tactic| have $(ns'[0]!):ident := $hc)
      else `(tactic| obtain ⟨$ns,*⟩ := $hc)
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b hc)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $o:ident
      cases $o:ident
      case some => (
        rename_i $nx:ident
        cases $nx:ident
        case Done => (
          simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
          obtain ⟨res, hres, hrep⟩ := $hc
          refine ⟨$hinv, $hG, ?_⟩
          refine ⟨res, fun d => ?_, hrep⟩
          rw [$heq:term, firstSome_append, firstSome_append]
          simp [hres, $[$facts:ident],*])
        case Again => (
          simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
          refine ⟨$hinv, $hG, ?_⟩
          peel_last $hc then (
            intro d
            rw [$heq:term, firstSome_append, firstSome_append]
            simp [$hlast:ident, $[$facts:ident],*])))
      simp only at $hc:ident ⊢
      $bind))

/-- `body_group_step` in a round of a loop: the round's result is the
member's, the end of the loop or its next round. -/
syntax "body_group_round_step " "with " term " as " "⟨" ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* " split " term " otherwise " "⟨" ident,* "⟩"
  " using" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| body_group_round_step with $e as ⟨$s', $hinv, $hc⟩ growing $hG carrying $hs*
      split $heq otherwise ⟨$ns,*⟩ using $facts*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let o := Lean.mkIdent `o
    let nx := Lean.mkIdent `nx
    let hlast := Lean.mkIdent `hlast
    let hg := Lean.mkIdent `hg
    let ns' := ns.getElems
    let bind ← if ns'.size == 1 then `(tactic| have $(ns'[0]!):ident := $hc)
      else `(tactic| obtain ⟨$ns,*⟩ := $hc)
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b hc)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $o:ident
      cases $o:ident
      case some => (
        rename_i $nx:ident
        cases $nx:ident
        case Done => (
          simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
          obtain ⟨res, hres, hrep⟩ := $hc
          refine ⟨$hinv, $hG, ?_⟩
          rw [$heq:term, firstSome_append, firstSome_append]
          simpa [hres, $[$facts:ident],*] using hrep)
        case Again => (
          simp only [WP.dspec_ok, WP.uncurry'_pair] at $hc:ident ⊢
          refine ⟨$hinv, $hG, by assumption, ?_⟩
          peel_last $hc then (
            rw [$heq:term, firstSome_append, firstSome_append]
            simp [$hlast:ident, $[$facts:ident],*])))
      simp only at $hc:ident ⊢
      $bind))

/-- Ends a round where no case answered. -/
syntax "round_stuck " ident ppSpace ident " using" (ppSpace colGt ident)* " in"
  (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| round_stuck $hinv $hG using $facts* in $cds*) =>
    `(tactic| first
      | (simp only [Store.stuck_eq, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
         refine ⟨$hinv, $hG, ?_⟩
         simpa [HasStuck.stuck, $[$facts:ident],*] using Store.Inv.rep_stuck $hinv)
      | (exfalso; simp_all [$[$cds:ident],*]; done))

/-- `round_stuck … splitting xs`: as `body_stuck … splitting xs`, for a
round of a loop. -/
syntax "round_stuck " ident ppSpace ident " using" (ppSpace colGt ident)* " in"
  (ppSpace colGt ident)* " splitting" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| round_stuck $_hinv $_hG using $_facts* in $cds* splitting $xs*) =>
    `(tactic| (exfalso; split_none $xs* in $cds*))

/-- Ends the induction step of a loop that goes round again: the rest of
the loop, by the induction hypothesis, on arguments with the same result
(`heq`), from a store that has grown (`hg`). -/
syntax "loop_close " ident ppSpace ident : tactic
macro_rules
  | `(tactic| loop_close $hg $heq) =>
    `(tactic| (
      rintro ⟨r', s'⟩ ⟨hinv', hg', hres⟩
      simp only [WP.uncurry'_pair] at hres ⊢
      refine ⟨hinv', Store.Grows.trans $hg hg', ?_⟩
      cases r' with
      | Err e => trivial
      | Ok t => simp only at hres ⊢; rw [$heq:ident]; exact hres))

end pathos_compiled_checker
