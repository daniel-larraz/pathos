module
public import MiniChecker
public import CpcMini.Logos
import all CpcMini.Logos
public import PathosProofs.Util
public import PathosProofs.Store.Sem
public import PathosProofs.Runtime.Frame
public import PathosProofs.Runtime.Ops
public import PathosProofs.Runtime.Embed
public import PathosProofs.Runtime.Natives
public import PathosProofs.Runtime.CalcSimp

/-!
# Lists of an operator: the runtime's walk, against logos

The runtime's list builtins (`lists.rs`) take a list of an operator `f`
apart into its elements and where its applications of `f` end
(`list_parts`), then build a result (`list_build`). logos's lists are
right-nested: `(f x1 (f x2 … nil))`, a list exactly when the end is a nil
of `f` (`__eo_get_nil_rec`, `__eo_is_list_nil`). Here: one step of the walk
(`list_step_spec`), the walk (`list_elements_loop_spec`), and the parts of
a list (`list_parts_spec`), for an operator that nests to the right (in
CpcMini every operator does; an operator that nests to the left has no nil
in logos, so is never a list there). They are meant to serve every list
builtin; `eo::cons` uses them (`Store.builtin_spec_cons`).

The end of the walk is asked of the generated `$eo_is_list_nil`, so
`list_parts_spec` takes what is proved of it (its `Spec`, from the
generated proofs' `Specs n`) as a hypothesis.

Written by hand.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- logos's list of `f` with the elements `xs`, ending in `e`. -/
def eoList (f e : Eo.Term) : List Eo.Term → Eo.Term
  | [] => e
  | x :: xs => Eo.Term.Apply (Eo.Term.Apply f x) (eoList f e xs)

/-- `!=` on handles. -/
theorem term_ne (a b : Term) :
    core.cmp.PartialEq.ne.trait_default Term.Insts.CoreCmpPartialEqTerm a b =
      ok (!decide (a = b)) := by
  unfold core.cmp.PartialEq.ne.trait_default
  have h := core.cmp.PartialEq.ne.default.spec Term.Insts.CoreCmpPartialEqTerm.eq a b
    (by simp [Term.Insts.CoreCmpPartialEqTerm.eq])
  obtain ⟨r, hr, hiff⟩ := spec_returns h
  rw [hr]
  by_cases hab : a = b <;> cases r <;> simp_all

/-- The fields of an application are earlier handles. -/
theorem Store.unapply_lt {s : Store} (hinv : s.Inv) {t f a : Term}
    (hu : Store.unapply s t = ok (core.result.Result.Ok (some (f, a)))) :
    f.val < t.val ∧ a.val < t.val := by
  rw [Store.unapply_eq] at hu
  by_cases hlt : t.val < s.nodes.length
  · simp only [hlt, ite_true] at hu
    have hwf := hinv.terms.wf t.val hlt
    unfold Store.data at hu
    cases hd : s.nodes.val[t.val]! <;> simp [hd] at hu
    obtain ⟨rfl, rfl⟩ := hu
    rw [hd] at hwf
    obtain ⟨h1, h2, _⟩ := hwf
    simp only [List.length_take] at h1 h2
    omega
  · simp [hlt] at hu

/-- One step down a list of `f`: the element and the rest where the term is
an application of `f` (two applications), nothing otherwise. -/
theorem list_step_spec (s : Store) (hinv : s.Inv) {fh lh : Term} {xf xl : Eo.Term}
    (hf : s.Rep fh xf) (hl : s.Rep lh xl) (count : Std.Usize) :
    generated.part0.Store.list_step s fh false lh count ⦃ r =>
      match r with
      | core.result.Result.Ok (some (a, b)) =>
        ∃ xa xb, xl = Eo.Term.Apply (Eo.Term.Apply xf xa) xb ∧ s.Rep a xa ∧ s.Rep b xb ∧
          b.val < lh.val
      | core.result.Result.Ok none => ∀ xa xb, xl ≠ Eo.Term.Apply (Eo.Term.Apply xf xa) xb
      | core.result.Result.Err _ => True ⦄ := by
  unfold generated.part0.Store.list_step
  rcases Store.Rep.unapply hl with ⟨g, b, xg, xb, rfl, hg, hb, hu⟩ | ⟨hne, hu⟩
  · simp only [hu, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rcases Store.Rep.unapply hg with ⟨hd, a, xh, xa, rfl, hh, ha, hu2⟩ | ⟨hne2, hu2⟩
    · simp [hu2, core.result.Result.Insts.CoreOpsTry.branch, term_ne]
      have hiff := Represents.eq_iff hinv hf hh
      by_cases hfh : fh = hd
      · have hx : xf = xh := hiff.mp hfh
        simp only [hfh, decide_true, Bool.not_true, Bool.false_eq_true, ite_false, lift,
          Std.bind_ok]
        have hblt := (Store.unapply_lt hinv hu).2
        split_ifs <;> simp [hx, ha, hb, hblt]
      · have hx : xh ≠ xf := fun h => hfh (hiff.mpr h.symm)
        have hv : ¬ ((fh.val : Nat) = (hd.val : Nat)) := fun h => hfh (UScalar.eq_of_val_eq h)
        simp [hv]
        exact hx
    · simp [hu2, core.result.Result.Insts.CoreOpsTry.branch]
      intro xa h
      exact hne2 _ _ h
  · simp only [hu, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, WP.spec_ok]
    intro xa xb he
    exact hne _ _ he

/-- The walk down a list of `f`, from `out` and `lh` on: the elements
taken, and where the applications of `f` end. -/
theorem list_elements_loop_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) {fh : Term}
    {xf : Eo.Term} (hf : s.Rep fh xf) :
    ∀ (out : alloc.vec.Vec Term) (lh : Term) (more : Bool) (xs : List Eo.Term) (xl : Eo.Term),
      List.Forall₂ s.Rep out.val xs → s.Rep lh xl → out.val.length + lh.val < s.nodes.length + 1 →
      generated.part0.Store.list_elements_loop s fh false out lh more ⦃ r =>
        match r with
        | core.result.Result.Ok (out', rest) =>
          ∃ ys xr, List.Forall₂ s.Rep out'.val (xs ++ ys) ∧ s.Rep rest xr ∧
            xl = eoList xf xr ys ∧
            (more = true → ∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) ∧
            (more = false → out' = out ∧ rest = lh) ∧
            out'.val.length + rest.val < s.nodes.length + 1
        | core.result.Result.Err _ => True ⦄div := by
  apply generated.part0.Store.list_elements_loop.fixpoint_induct s fh false
    (motive := fun loop => ∀ (out : alloc.vec.Vec Term) (lh : Term) (more : Bool)
      (xs : List Eo.Term) (xl : Eo.Term),
      List.Forall₂ s.Rep out.val xs → s.Rep lh xl → out.val.length + lh.val < s.nodes.length + 1 →
      loop out lh more ⦃ r =>
        match r with
        | core.result.Result.Ok (out', rest) =>
          ∃ ys xr, List.Forall₂ s.Rep out'.val (xs ++ ys) ∧ s.Rep rest xr ∧
            xl = eoList xf xr ys ∧
            (more = true → ∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) ∧
            (more = false → out' = out ∧ rest = lh) ∧
            out'.val.length + rest.val < s.nodes.length + 1
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih out lh more xs xl hout hl hsz
    simp only
    split
    · rename_i hmore
      subst hmore
      step with list_step_spec s hinv hf hl (alloc.vec.Vec.len out) as ⟨r, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
      | Ok o =>
        cases o with
        | none =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
          apply WP.dspec_mono (ih out lh false xs xl hout hl hsz)
          rintro (⟨out', rest⟩ | e) h
          · obtain ⟨ys, xr, h1, h2, h3, _, h5, h6⟩ := h
            obtain ⟨rfl, rfl⟩ := h5 rfl
            refine ⟨[], xl, by simpa using hout, hl, rfl, ?_, (fun h => by cases h), h6⟩
            simpa using hr
          · trivial
        | some p =>
          obtain ⟨a, b⟩ := p
          obtain ⟨xa, xb, hxl, ha, hb, hblt⟩ := hr
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
          show (do let out1 ← out.push a; loop out1 b true) ⦃ r => _ ⦄div
          have hmax := hinv.table.hmax
          have hcap : out.val.length < Usize.max := by
            have : (2 : Nat) ^ 40 ≤ Usize.max := h64
            simp only [alloc.vec.Vec.length] at hmax hsz
            have : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
            omega
          step with alloc.vec.Vec.push_spec out a hcap as ⟨out1, hout1⟩
          have hout1' : List.Forall₂ s.Rep out1.val (xs ++ [xa]) := by
            rw [hout1]; exact List.rel_append hout (List.Forall₂.cons ha List.Forall₂.nil)
          have hsz1 : out1.val.length + b.val < s.nodes.length + 1 := by
            rw [hout1]; simp only [List.length_append, List.length_singleton]; omega
          apply WP.dspec_mono (ih out1 b true (xs ++ [xa]) xb hout1' hb hsz1)
          rintro (⟨out', rest⟩ | e) h
          · obtain ⟨ys, xr, h1, h2, h3, h4, _, h6⟩ := h
            refine ⟨xa :: ys, xr, by simpa using h1, h2, by rw [hxl, h3]; rfl, h4 rfl,
              (fun h => by cases h), h6⟩
          · trivial
    · rename_i hmore
      simp only [WP.dspec_ok]
      exact ⟨[], xl, by simpa using hout, hl, by rfl, fun h => absurd h hmore,
        fun _ => ⟨trivial, trivial⟩, hsz⟩

/-- `is_left_assoc` where no constructor of the signature nests to the
left (CpcMini: `schema.Constructor.is_left_assoc` is `false`). -/
theorem is_left_assoc_false (s : Store) {fh : Term} {xf : Eo.Term} (hf : s.Rep fh xf)
    (hleft : ∀ c, schema.Constructor.is_left_assoc c = ok false) :
    generated.part0.Store.is_left_assoc s fh = ok (core.result.Result.Ok false) := by
  unfold generated.part0.Store.is_left_assoc
  rw [Store.view_eq]
  simp only [hf.lt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  split <;> simp [hleft]

/-- What `$eo_is_list_nil` is proved to compute (the generated
`eo__24eo_5fis_5flist_5fnil.Spec n`, written out). -/
def IsListNilSpec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 x_a1 : Eo.Term), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    generated.part0.eo__24eo_5fis_5flist_5fnil s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_is_list_nil x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- The parts of a list of `f`: its elements and its nil, where the walk
ends at a nil of `f`; nothing where it ends elsewhere. -/
theorem list_parts_spec (n : Nat) (hnil : IsListNilSpec n) (s : Store) (hinv : s.Inv)
    (h64 : Platform64) (hrem : s.remaining ≤ n) {fh lh : Term} {xf xl : Eo.Term}
    (hf : s.Rep fh xf) (hl : s.Rep lh xl)
    (hleft : ∀ c, schema.Constructor.is_left_assoc c = ok false) :
    generated.part0.Store.list_parts s fh lh ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some (out, rest)) =>
        ∃ ys xr, List.Forall₂ s'.Rep out.val ys ∧ s'.Rep rest xr ∧ xl = eoList xf xr ys ∧
          (∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) ∧
          Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true ∧ out.val.length ≤ s.nodes.length
      | core.result.Result.Ok none =>
        ∃ ys xr, xl = eoList xf xr ys ∧ (∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) ∧
          Eo.__eo_is_list_nil xf xr ≠ Eo.Term.Boolean true
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.Store.list_parts
  rw [is_left_assoc_false s hf hleft]
  simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  unfold generated.part0.Store.list_elements
  have hsz : (alloc.vec.Vec.new Term).val.length + lh.val < s.nodes.length + 1 := by
    have := hl.lt; simp only [alloc.vec.Vec.new, alloc.vec.Vec.length] at this ⊢; simp; omega
  step with list_elements_loop_spec s hinv h64 hf (alloc.vec.Vec.new Term) lh true [] xl
    (by simp [alloc.vec.Vec.new]) hl hsz as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok p =>
    obtain ⟨out, rest⟩ := p
    obtain ⟨ys, xr, hys, hrest, hxl, hend, _, hsz'⟩ := hr
    simp only [List.nil_append] at hys
    simp only
    step with hnil s fh rest xf xr hinv h64 hrem hf hrest as ⟨r2, s1, hinv1, hg1, hr2⟩
    cases r2 with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact ⟨hinv1, hg1⟩
    | Ok v =>
      simp only at hr2
      rcases Store.boolean_value_term hr2 with ⟨hv, hb⟩ | ⟨hv, hb⟩ | ⟨hv, hb⟩
      · simp only [hb, Std.bind_ok, ite_true, WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv1, hg1, ys, xr, ?_, Represents.grows hrest hg1, hxl, hend, hv, by omega⟩
        exact hys.imp (fun {_ _} h => Represents.grows h hg1)
      · simp only [hb, Std.bind_ok, Bool.false_eq_true, ite_false, WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, ys, xr, hxl, hend, by rw [hv]; simp⟩
      · simp only [hb, Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
        exact ⟨hinv1, hg1, ys, xr, hxl, hend, hv true⟩

/-- One node of a list of `f`, built again: `(f e) tail`. -/
theorem list_cons_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) {fh eh th : Term}
    {xf xe xt : Eo.Term} (hf : s.Rep fh xf) (he : s.Rep eh xe) (ht : s.Rep th xt)
    (hnf : xf ≠ Eo.Term.Stuck) (hne : xe ≠ Eo.Term.Stuck) (hnt : xt ≠ Eo.Term.Stuck) :
    generated.part0.Store.list_cons s fh false eh th ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.Term.Apply (Eo.Term.Apply xf xe) xt)
      | core.result.Result.Err _ => True ⦄div := by
  unfold generated.part0.Store.list_cons
  simp only [Bool.false_eq_true, ite_false]
  step with Store.apply_rep s fh eh xf xe hinv h64 hf he hnf hne as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv1, hg1⟩
  | Ok g =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Bool.false_eq_true,
      ite_false]
    apply WP.dspec_mono (Store.apply_rep s1 g th _ xt hinv1 h64 hr (Represents.grows ht hg1)
      (by intro h; cases h) hnt)
    rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
    exact ⟨hinv2, hg1.trans hg2, hr2⟩

/-- The list of `f` built again from its elements, from the last to the
first, onto the end `xr`. -/
theorem list_build_loop_spec (s0 : Store) (h64 : Platform64) {fh : Term} {xf xr : Eo.Term}
    (elems : Slice Term) (ys : List Eo.Term) (hys : List.Forall₂ s0.Rep elems.val ys)
    (hnf : xf ≠ Eo.Term.Stuck) (hny : ∀ y ∈ ys, y ≠ Eo.Term.Stuck) (hnr : xr ≠ Eo.Term.Stuck) :
    ∀ (s : Store) (lh : Term) (i : Std.Usize), s.Inv → s0.Grows s → s.Rep fh xf →
      i.val ≤ ys.length → s.Rep lh (eoList xf xr (ys.drop i.val)) →
      generated.part0.Store.list_build_loop s fh elems false lh i ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok t => s'.Rep t (eoList xf xr ys)
        | core.result.Result.Err _ => True ⦄div := by
  have hlen : elems.val.length = ys.length := hys.length_eq
  have hne_list : ∀ k, eoList xf xr (ys.drop k) ≠ Eo.Term.Stuck := by
    intro k
    cases h : ys.drop k with
    | nil => simpa [eoList] using hnr
    | cons y ys' => simp [eoList]
  apply generated.part0.Store.list_build_loop.fixpoint_induct fh elems false
    (motive := fun loop => ∀ (s : Store) (lh : Term) (i : Std.Usize), s.Inv → s0.Grows s →
      s.Rep fh xf → i.val ≤ ys.length → s.Rep lh (eoList xf xr (ys.drop i.val)) →
      loop s lh i ⦃ r s' =>
        s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok t => s'.Rep t (eoList xf xr ys)
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih s lh i hinv hg hf hi hl
    simp only
    split
    · rename_i hpos
      step as ⟨i1, hi1⟩
      have hi1lt : i1.val < elems.val.length := by rw [hlen]; scalar_tac
      step as ⟨t, ht⟩
      have hyt : s.Rep t (ys[i1.val]'(by rw [← hlen]; exact hi1lt)) := by
        have := (List.forall₂_iff_get.mp hys).2 i1.val hi1lt (by rw [← hlen]; exact hi1lt)
        rw [ht]
        simpa [Slice.getElem_Nat_eq] using Represents.grows this hg
      have hdrop : ys.drop i1.val = ys[i1.val]'(by rw [← hlen]; exact hi1lt) :: ys.drop i.val := by
        rw [List.drop_eq_getElem_cons (by rw [← hlen]; exact hi1lt)]; congr 2; scalar_tac
      step with list_cons_spec s hinv h64 hf hyt hl hnf (hny _ (List.getElem_mem _))
        (hne_list _) as ⟨r, s1, hinv1, hg1, hr⟩
      cases r with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          core.convert.FromSame.from]
        exact ⟨hinv1, hg1⟩
      | Ok v =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        have hv : s1.Rep v (eoList xf xr (ys.drop i1.val)) := by rw [hdrop]; exact hr
        apply WP.dspec_mono (ih s1 v i1 hinv1 (hg.trans hg1) (Represents.grows hf hg1)
          (by scalar_tac) hv)
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        exact ⟨hinv2, hg1.trans hg2, hr2⟩
    · rename_i hz
      have hi0 : i.val = 0 := by scalar_tac
      simp only [WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      simpa [hi0] using hl

/-! ## logos's side -/

/-- logos's walk to the nil goes down a list of `f` to its end. -/
theorem get_nil_rec_eoList {xf : Eo.Term} (hnf : xf ≠ Eo.Term.Stuck) (xr : Eo.Term) :
    ∀ ys, Eo.__eo_get_nil_rec xf (eoList xf xr ys) = Eo.__eo_get_nil_rec xf xr := by
  intro ys
  induction ys with
  | nil => rfl
  | cons y ys ih =>
    simp only [eoList]
    rw [Eo.__eo_get_nil_rec.eq_def]
    simp [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not, hnf, ih]

/-- A nil of an operator is no application of two arguments (CpcMini's
nils are `true` and the empty `List`; another calculus's are decided by the
helpers of `Runtime/CalcSimp.lean`). -/
theorem is_list_nil_not_apply {xf xr : Eo.Term}
    (h : Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true) :
    ∀ g a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply g a) b := by
  intro g a b he
  subst he
  revert h
  unfold Eo.__eo_is_list_nil
  split <;> simp_all [eo_list_nil]

/-- logos's `eo::cons` on a list of `f`, given by its end. -/
theorem eo_cons_eoList {xf xe xr : Eo.Term} (ys : List Eo.Term) (hnf : xf ≠ Eo.Term.Stuck)
    (hnr : eoList xf xr ys ≠ Eo.Term.Stuck)
    (hend : ∀ a b, xr ≠ Eo.Term.Apply (Eo.Term.Apply xf a) b) :
    Eo.__eo_cons xf xe (eoList xf xr ys) =
      if Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true then
        Eo.Term.Apply (Eo.Term.Apply xf xe) (eoList xf xr ys)
      else Eo.Term.Stuck := by
  have hrec := get_nil_rec_eoList hnf xr ys
  have hsplit : Eo.__eo_is_list xf (eoList xf xr ys) = Eo.__eo_is_ok (Eo.__eo_get_nil_rec xf xr) := by
    unfold Eo.__eo_is_list; split <;> simp_all
  show Eo.__eo_requires (Eo.__eo_is_list xf (eoList xf xr ys)) (Eo.Term.Boolean true)
    (Eo.Term.Apply (Eo.Term.Apply xf xe) (eoList xf xr ys)) = _
  rw [hsplit]
  by_cases hn : Eo.__eo_is_list_nil xf xr = Eo.Term.Boolean true
  · have hna := is_list_nil_not_apply hn
    have hxr : xr ≠ Eo.Term.Stuck := by
      intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
    have hg : Eo.__eo_get_nil_rec xf xr = xr := by
      unfold Eo.__eo_get_nil_rec
      split <;> simp_all [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
    simp [hg, hn, Eo.__eo_is_ok, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq,
      SmtEval.native_not, hxr]
  · have hg : Eo.__eo_get_nil_rec xf xr = Eo.Term.Stuck := by
      unfold Eo.__eo_get_nil_rec
      split <;> simp_all [Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq, SmtEval.native_not]
      intro h; exact absurd h.symm hend
    simp [hg, hn, Eo.__eo_is_ok, Eo.__eo_requires, SmtEval.native_ite, Eo.native_teq,
      SmtEval.native_not]

/-! ## The runtime's `eo::cons` -/

/-- `any_stuck` on the handles of three terms. -/
theorem Store.any_stuck_three {s : Store} {args : Slice Term} {a b c : Term} {x y z : Eo.Term}
    (hargs : args.val = [a, b, c]) (ha : s.Rep a x) (hb : s.Rep b y) (hc : s.Rep c z) :
    Store.any_stuck s args ⦃ r => r = (decide (x = Eo.Term.Stuck) || decide (y = Eo.Term.Stuck) ||
      decide (z = Eo.Term.Stuck)) ⦄ := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  unfold Store.any_stuck
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt0 : (0#usize : Std.Usize) < 3#usize := by scalar_tac
  simp only [hlt0, ite_true]
  have hite : ∀ c : Bool, (if c = true then (ok true : Result Bool) else ok false) = ok c := by
    intro c; cases c <;> rfl
  have hite' : ∀ c d : Bool, (if c = true then (ok true : Result Bool) else ok d) = ok (c || d) := by
    intro c d; cases c <;> rfl
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  simp only [h0, Store.stuck_or_foreign_rep ha, Std.bind_ok, hite]
  step as ⟨i1, hi1⟩
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt1 : i1 < 3#usize := by scalar_tac
  have h1 : Slice.index_usize args i1 = ok b := by
    simp [Slice.index_usize, hargs, show i1.val = 1 by scalar_tac]
  simp only [hlt1, ite_true, h1, Store.stuck_or_foreign_rep hb, Std.bind_ok, hite']
  step as ⟨i2, hi2⟩
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt2 : i2 < 3#usize := by scalar_tac
  have h2 : Slice.index_usize args i2 = ok c := by
    simp [Slice.index_usize, hargs, show i2.val = 2 by scalar_tac]
  simp only [hlt2, ite_true, h2, Store.stuck_or_foreign_rep hc, Std.bind_ok, hite']
  step as ⟨i3, hi3⟩
  unfold Store.any_stuck_loop
  simp only [hlen]
  have hlt3 : ¬ (i3 < 3#usize) := by scalar_tac
  simp only [hlt3, ite_false]
  cases decide (x = Eo.Term.Stuck) <;> cases decide (y = Eo.Term.Stuck) <;>
    cases decide (z = Eo.Term.Stuck) <;> simp

/-- `append_terms`: the vector with the slice after it. -/
theorem append_terms_loop_spec (src : Slice Term) :
    ∀ (dst : alloc.vec.Vec Term) (i : Std.Usize), i.val ≤ src.length →
      dst.val.length + (src.length - i.val) < Usize.max →
      append_terms_loop dst src i ⦃ r => r.val = dst.val ++ src.val.drop i.val ⦄div := by
  apply append_terms_loop.fixpoint_induct src
    (motive := fun loop => ∀ (dst : alloc.vec.Vec Term) (i : Std.Usize), i.val ≤ src.length →
      dst.val.length + (src.length - i.val) < Usize.max →
      loop dst i ⦃ r => r.val = dst.val ++ src.val.drop i.val ⦄div)
  · prove_adm
  · intro loop ih dst i hi hcap
    simp only
    split
    · rename_i hlt
      have hlt' : i.val < src.length := by scalar_tac
      step as ⟨t, ht⟩
      have hcap1 : dst.val.length < Usize.max := by omega
      step with alloc.vec.Vec.push_spec dst t hcap1 as ⟨dst1, hdst1⟩
      step as ⟨i2, hi2⟩
      have hi2v : i2.val = i.val + 1 := by scalar_tac
      apply WP.dspec_mono (ih dst1 i2 (by scalar_tac) (by
        rw [hdst1, hi2v]; simp only [List.length_append, List.length_singleton]
        simp only [Slice.length] at hlt' hcap ⊢; omega))
      intro r hr
      have hlt'' : i.val < src.val.length := by simpa [Slice.length] using hlt'
      have hd : src.val.drop i.val = src.val[i.val] :: src.val.drop (i.val + 1) :=
        List.drop_eq_getElem_cons hlt''
      rw [hr, hdst1, hi2v, List.append_assoc, hd, ht]
      simp [Slice.getElem!_Nat_eq, getElem!_eq _ _ hlt'']
    · rename_i hge
      simp only [WP.dspec_ok]
      have : src.val.drop i.val = [] := List.drop_eq_nil_of_le (by scalar_tac)
      simp [this]

/-- The elements of a list that a handle stands for are not stuck. -/
theorem eoList_valid_elems {xf xr : Eo.Term} :
    ∀ ys, TermValid (eoList xf xr ys) → ∀ y ∈ ys, y ≠ Eo.Term.Stuck := by
  intro ys
  induction ys with
  | nil => intro _ y hy; cases hy
  | cons y ys ih =>
    intro hv z hz
    rw [eoList] at hv
    unfold TermValid at hv
    obtain ⟨_, _, h3, h4⟩ := hv
    unfold TermValid at h3
    obtain ⟨_, hy, _, _⟩ := h3
    rcases List.mem_cons.mp hz with rfl | hz
    · exact hy
    · exact ih h4 z hz

/-- `eo::cons` on handles of an operator, an element that is not stuck and a
list: logos's `__eo_cons`. The element must not be stuck: logos's
`__eo_cons` catches a stuck list but not a stuck element (docs/proofs.md,
"Stuck terms under an application"), and the runtime gives the stuck term
for either. -/
theorem Store.builtin_spec_cons (n : Nat) (hnil : IsListNilSpec n) (s : Store)
    (args : Slice Term) {a b c : Term} {xf xe xa : Eo.Term} (hargs : args.val = [a, b, c])
    (ha : s.Rep a xf) (hb : s.Rep b xe) (hc : s.Rep c xa) (hne : xe ≠ Eo.Term.Stuck)
    (hinv : s.Inv) (h64 : Platform64) (hrem : s.remaining ≤ n)
    (hleft : ∀ c, schema.Constructor.is_left_assoc c = ok false) :
    generated.part0.Store.builtin_list s kind.EvalOp.Cons args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_cons xf xe xa)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 3#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have htakes : Store.takes kind.EvalOp.Cons 3#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold generated.part0.Store.builtin_list
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  unfold Store.check_handles
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
    step with Store.any_stuck_three hargs ha hb hc as ⟨b1, hb1⟩
    subst hb1
    by_cases hxf : xf = Eo.Term.Stuck
    · subst hxf
      simp only [decide_true, Bool.true_or, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_cons Eo.Term.Stuck xe xa = Eo.Term.Stuck := by
        simp [Eo.__eo_cons, Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite,
          Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    by_cases hxa : xa = Eo.Term.Stuck
    · subst hxa
      simp only [decide_true, Bool.or_true, ite_true, Store.stuck_eq, Std.bind_ok, WP.dspec_ok,
        WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      have : Eo.__eo_cons xf xe Eo.Term.Stuck = Eo.Term.Stuck := by
        simp [Eo.__eo_cons, Eo.__eo_is_list, Eo.__eo_requires, SmtEval.native_ite,
          Eo.native_teq]
      rw [this]; exact hinv.rep_stuck
    simp only [hxf, hxa, hne, decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
    unfold generated.part0.Store.list_builtin
    have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
    have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
    have h2 : Slice.index_usize args 2#usize = ok c := by simp [Slice.index_usize, hargs]
    simp only [h0, h1, h2, Std.bind_ok]
    unfold generated.part0.Store.list_cons_op
    step with list_parts_spec n hnil s hinv h64 hrem ha hc hleft as ⟨r, s1, hinv1, hg1, hr⟩
    have hva : TermValid xa := Store.Rep.valid' hinv hc
    cases r with
    | Err e =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      exact ⟨hinv1, hg1⟩
    | Ok o =>
      cases o with
      | none =>
        obtain ⟨ys, xr, hxl, hend, hn⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, Store.stuck_eq,
          WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv1, hg1, ?_⟩
        have : Eo.__eo_cons xf xe xa = Eo.Term.Stuck := by
          rw [hxl, eo_cons_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
          simp [hn]
        rw [this]; exact hinv1.rep_stuck
      | some p =>
        obtain ⟨tail, rest⟩ := p
        obtain ⟨ys, xr, hys, hrest, hxl, hend, hn, hsz⟩ := hr
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok]
        show (do
          let i1 ← tail.len + 1#usize
          let elems1 ← (alloc.vec.Vec.with_capacity Term i1).push b
          let elems2 ← append_terms elems1 tail.deref
          generated.part0.Store.list_build s1 a elems2.deref rest) ⦃ r s' => _ ⦄div
        have hmax := hinv.table.hmax
        have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
        have hnodes : s.nodes.val.length ≤ 2 ^ 32 := by scalar_tac
        have htl : tail.val.length ≤ 2 ^ 32 := by
          simp only [alloc.vec.Vec.length] at hsz; omega
        step as ⟨i1, hi1⟩
        have hwc : (alloc.vec.Vec.with_capacity Term i1).val = [] := by
          simp [alloc.vec.Vec.with_capacity]
        step with alloc.vec.Vec.push_spec (alloc.vec.Vec.with_capacity Term i1) b
          (by rw [hwc]; simp; omega) as ⟨elems1, he1⟩
        rw [hwc] at he1
        unfold append_terms
        step with append_terms_loop_spec tail.deref elems1 0#usize (by simp)
          (by rw [he1]; simp [alloc.vec.Vec.deref, Slice.length]; omega) as ⟨elems2, he2⟩
        simp only [List.nil_append, List.drop_zero] at he1 he2
        have he2' : elems2.val = b :: tail.val := by
          rw [he2, he1]; simp [alloc.vec.Vec.deref]
        have hxr : xr ≠ Eo.Term.Stuck := by
          intro h; subst h; revert hn; unfold Eo.__eo_is_list_nil; split <;> simp_all
        have hys' : List.Forall₂ s1.Rep (alloc.vec.Vec.deref elems2).val (xe :: ys) := by
          have : (alloc.vec.Vec.deref elems2).val = elems2.val := by simp [alloc.vec.Vec.deref]
          rw [this, he2']
          exact List.Forall₂.cons (Represents.grows hb hg1) hys
        have hny : ∀ y ∈ xe :: ys, y ≠ Eo.Term.Stuck := by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hne
          · exact eoList_valid_elems ys (hxl ▸ hva) y hy
        unfold generated.part0.Store.list_build
        rw [is_left_assoc_false s1 (Represents.grows ha hg1) hleft]
        simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
        have hlenE : (Slice.len (alloc.vec.Vec.deref elems2)).val = (xe :: ys).length := by
          have := hys'.length_eq; simp [Slice.len, Slice.length] at this ⊢; omega
        apply WP.dspec_mono (list_build_loop_spec s1 h64 (alloc.vec.Vec.deref elems2) (xe :: ys)
          hys' hxf hny hxr s1 rest (Slice.len (alloc.vec.Vec.deref elems2)) hinv1
          (Store.Grows.refl s1) (Represents.grows ha hg1) (by omega)
          (by rw [hlenE, List.drop_length]; exact hrest))
        rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
        refine ⟨hinv2, hg1.trans hg2, ?_⟩
        cases r2 with
        | Err e => trivial
        | Ok t =>
          simp only at hr2 ⊢
          have : Eo.__eo_cons xf xe xa = eoList xf xr (xe :: ys) := by
            rw [hxl, eo_cons_eoList ys hxf (by rw [← hxl]; exact hxa) hend]
            simp [hn, eoList]
          rw [this]; exact hr2

end pathos_compiled_checker
