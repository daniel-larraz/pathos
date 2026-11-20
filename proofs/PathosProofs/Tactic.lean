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

/-- Closes the statement that logos's function is what the generated body
does, after both sides are unfolded: by cases on the function's
arguments; a function of one body, by its definition. -/
macro "logos_eq" : tactic =>
  `(tactic| first
    | (split <;> simp_all [HasStuck.stuck]; done)
    | (split <;> simp_all [HasStuck.stuck, requires_ite] <;> (try split_ifs) <;>
        simp_all [eo_eq_of_ne, eo_eq_true]; done)
    | rfl)

/-- A term is not the stuck term: said by a hypothesis, or plain from its
form. -/
macro "ns_tac" : tactic =>
  `(tactic| first
    | assumption
    | (intro h; cases h)
    | (simp; done))

/-- Carries the facts named over to a store that has grown. -/
syntax "transport " term " at " (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| transport $hg at $hs*) => do
    let ts ← hs.mapM fun h => `(tactic| carry_one $h $hg)
    `(tactic| ($[$ts];*))

/-- `store_step with spec as ⟨v, s', hinv, h⟩ growing hG carrying h1 h2 …`:
one operation on the store whose specification `spec` says that the new
store has the invariant, has grown, and what the result is on `Ok`. Leaves
the `Ok` case with the result `v`, the store `s'`, its invariant `hinv`
and the fact `h` about `v`; `hG` is extended, and the facts after
`carrying` are carried over. An `Err` ends the function, with nothing to
prove about its result. -/
syntax "store_step " "with " term " as " "⟨" ident ", " ident ", " ident ", " ident "⟩"
  " growing " ident " carrying" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| store_step with $e as ⟨$v, $s', $hinv, $h⟩ growing $hG carrying $hs*) => do
    let b (i : Lean.Ident) : Lean.TSyntax ``Lean.binderIdent :=
      ⟨Lean.mkNode ``Lean.binderIdent #[i]⟩
    let r := Lean.mkIdent `r
    let hg := Lean.mkIdent `hg
    `(tactic| (
      step with $e as ⟨$(b r), $(b s'), $(b hinv), $(b hg), $(b h)⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      cases $r:ident
      case Err => (simp only [WP.dspec_ok, WP.uncurry'_pair]; exact ⟨$hinv, $hG, trivial⟩)
      rename_i $v:ident
      simp only at $h:ident ⊢
      clear $hg))

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
      obtain ⟨$hnf, $hna⟩ := Store.Rep.apply_ne_stuck $hi $h))

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
        ⟨fun ⟨_, he⟩ => ($inv (by simpa only [Embed.embedded_enc_Term] using he)).1,
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
      subst hv))

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
      clear hfldlen))

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
      clear $hvi hfldlen))

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
        | (simp only at $hres:ident; nat_no_match $hres $hinv' $hG in $cd; done)))

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
        no_match $hinv $hG in $cd)
      rw [show decide ($a ≠ $b) = false from by simp [hv]]
      simp only [Bool.false_eq_true, ite_false]
      have hx := hiff.mp hv
      clear hiff
      first | subst hx | skip))

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
        | (unfold $cd; split <;> simp_all; done)))

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
        simpa [requires_ite, hq0] using Store.Inv.rep_stuck $hinv)
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
      rw [requires_eq _ _ $hq]
      exact $h))

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

theorem firstSome_append {α : Type} (l₁ l₂ : List (Option α)) (d : α) :
    firstSome (l₁ ++ l₂) d = firstSome l₁ (firstSome l₂ d) := by
  induction l₁ with
  | nil => rfl
  | cons o l ih => cases o <;> simp [firstSome, ih]

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
`none`, plain or after splitting one of the arguments `xs` into its
constructors (for a program whose cases are one per constructor). -/
syntax "split_none" (ppSpace colGt ident)* " in" (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| split_none in $cds*) => `(tactic| (simp_all [$[$cds:ident],*]; done))
  | `(tactic| split_none $x $xs* in $cds*) =>
    `(tactic| first
      | (simp_all [$[$cds:ident],*]; done)
      | (cases $x:ident <;> simp_all [$[$cds:ident],*]; done)
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
      step with Store.tick_spec as ⟨$(b r), $(b s'), hn, hh, hs, hc, hl, hd, hb, $(b hbud)⟩
      have $hinv : Store.Inv $s' := Store.Inv.congr (by assumption) hn hh hs hc
      have $hg : Store.Grows _ $s' := ⟨by rw [hn], hl, hd, hb⟩
      transport $hg at $hs*
      replace $hG:ident := Store.Grows.trans $hG $hg
      clear $hg hn hh hs hc hl hd hb
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
