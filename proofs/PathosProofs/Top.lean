module
public import MiniProofs
public import CpcMini.Proofs.Checker
import all CpcMini.Logos
import all CpcMini.TranslationChecks
public import PathosProofs.Tactic

/-!
# CpcMini's top-level theorem

If the compiled checker for CpcMini says `Correct` on handles of the
assumptions `F` and the proof `pf`, then `F` is unsatisfiable, as logos
defines it: `check_proof_correct`, through logos's
`correct___eo_is_refutation` (`CpcMini/Proofs/Checker.lean`).

The side conditions of logos's theorem, `TranslatableAssumptionList F`
and `CmdListTranslationOk pf`, are what `check_proof_inner` checks after
the refutation (`arguments_translate` and its loop over the commands),
through the proved `$eo_to_smt` and `$smtx_typeof`.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result
open generated generated.part0

/-- What the generated proofs give of `$eo_checker_is_refutation`: the
`Spec` rust-meta writes for it, word for word, so that once the program is
proved `fun n => (specs n).eo__24eo_5fchecker_5fis_5frefutation` is this. -/
def CheckerIsRefutationSpec (n : Nat) : Prop :=
  ∀ (s : Store) (a0 a1 : Term) (x_a0 : _) (x_a1 : _), s.Inv → Platform64 → s.remaining ≤ n →
    Represents.rep s a0 x_a0 → Represents.rep s a1 x_a1 →
    eo__24eo_5fchecker_5fis_5frefutation s a0 a1 ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => Represents.rep s' t (Eo.__eo_checker_is_refutation x_a0 x_a1)
      | core.result.Result.Err _ => True ⦄div

/-- `is_native_true` of a handle of a native Boolean: the Boolean. -/
theorem Store.is_native_true_rep {s : Store} {t : Term} {b : Bool} (h : Represents.rep s t b) :
    Store.is_native_true s t = ok (core.result.Result.Ok b) := by
  unfold Store.is_native_true
  rcases Store.boolean_value_native h with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ <;>
    simp [hb, core.result.Result.Insts.CoreOpsTry.branch]

/-- The refutation: `true` only where logos's checker says so. -/
theorem check_refutation_inner_spec (hchk : ∀ n, CheckerIsRefutationSpec n)
    (s : Store) (hinv : s.Inv) (h64 : Platform64) (a c : Term)
    (F : Eo.CArgList) (pf : Eo.CCmdList)
    (hF : Represents.rep s a F) (hpf : Represents.rep s c pf) :
    Store.check_refutation_inner s a c ⦃ r s' => s'.Inv ∧ s.nodes.val <+: s'.nodes.val ∧
      match r with
      | core.result.Result.Ok b => b = true → Eo.eo_is_refutation F pf
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.check_refutation_inner
  have hinv0 := hinv.with_calls 0#u64
  step with hchk _ { s with calls := 0#u64 } a c F pf hinv0 h64 le_rfl hF hpf
    as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      -List.prefix_iff_eq_append]
    first
      | exact ⟨hinv1, hg1.nodes⟩
      | exact ⟨hinv1, hg1.nodes, trivial⟩
      | (refine ⟨hinv1, ?_⟩; obtain ⟨l, hl⟩ := hg1.nodes; exact ⟨l, hl⟩)
  | Ok t =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr ⊢
    rw [Store.is_native_true_rep hr]
    simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
    refine ⟨hinv1, hg1.nodes, fun h => ?_⟩
    exact Eo.eo_is_refutation.intro F pf h

/-- A store that grows keeps its terms. -/
theorem prefix_of_grows {s s' : Store} (h : s.Grows s') : s.nodes.val <+: s'.nodes.val := h.nodes

/-- `$smtx_typeof` of `$eo_to_smt`: a handle of the SMT type of the
translation, from what is proved of the two programs. -/
theorem translation_type_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) (t : Term)
    (x : Eo.Term) (h : s.Rep t x) :
    Store.translation_type s t ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok ty => Represents.rep s' ty (Smtm.__smtx_typeof (__eo_to_smt x))
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.translation_type
  have hS := specs s.remaining
  step with hS.eo__24eo_5fto_5fsmt s t x hinv h64 le_rfl h as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv1, hg1⟩
  | Ok u =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr ⊢
    apply WP.dspec_mono (hS.eo__24smtx_5ftypeof s1 u _ hinv1 h64 (hg1.rem le_rfl) hr)
    rintro ⟨r2, s2⟩ ⟨hinv2, hg2, hr2⟩
    exact ⟨hinv2, hg1.trans hg2, hr2⟩

/-- `has_translation`: `true` only of a term whose translation has an SMT
type, logos's `eoHasSmtTranslation`. -/
theorem has_translation_spec (s : Store) (hinv : s.Inv) (h64 : Platform64) (t : Term)
    (x : Eo.Term) (h : s.Rep t x) :
    Store.has_translation s t ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok b => b = true → eoHasSmtTranslation x
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.has_translation
  step with translation_type_spec s hinv h64 t x h as ⟨r, s1, hinv1, hg1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
    exact ⟨hinv1, hg1⟩
  | Ok ty =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr ⊢
    have hnode : ∃ c xs, Embedded.enc (Smtm.__smtx_typeof (__eo_to_smt x)) = Tree.node c xs := by
      cases Smtm.__smtx_typeof (__eo_to_smt x) <;> exact ⟨_, _, rfl⟩
    have hst : Store.is_stuck s1 ty = ok (core.result.Result.Ok false) := by
      rw [Store.is_stuck_eq, if_pos hr.lt]
      obtain ⟨c, xs, hc⟩ := hnode
      have hh := hr.1
      rw [hc] at hh
      cases hh with
      | node _ _ v _ _ hd _ => simp [Store.data, hd, TermData.isStuck]
    rw [hst]
    simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch, Bool.false_eq_true,
      ite_false]
    · obtain ⟨b, hb, hiff⟩ := Store.is_node_holds schema.Constructor.eo__24emb_5ftsm_2eNone hr.1
      rw [hb]
      simp only [Std.bind_ok, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv1, hg1, fun hnb => ?_⟩
      intro hnone
      have : b = true := by
        apply hiff.mpr
        rw [hnone]
        exact ⟨[], rfl⟩
      simp [this] at hnb

/-! ## Walking the input lists -/

/-- `node_fields` on a handle of a node of the constructor asked for: its
fields. -/
theorem Store.node_fields_holds {s : Store} {t : Term} {c : schema.Constructor} {xs : List Tree}
    (h : Holds s.nodes.val t.val (Tree.node c xs)) :
    ∃ v : alloc.vec.Vec Term, Store.node_fields s t (some c) = ok (core.result.Result.Ok (some v)) ∧
      HoldsList s.nodes.val v.val xs ∧ s.nodes.val[t.val]! = TermData.Node c v := by
  unfold Store.node_fields
  rw [Store.view_eq]
  have hlt := h.lt
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  cases h with
  | node _ _ v _ _ hd hl =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec c
    simp only [h1, Std.bind_ok, ite_true, alloc.vec.CloneVec.clone_terms]
    exact ⟨v, rfl, hl, rfl⟩

/-- `node_fields` on a handle of a node of another constructor: none. -/
theorem Store.node_fields_other {s : Store} {t : Term} {c d : schema.Constructor} {xs : List Tree}
    (h : Holds s.nodes.val t.val (Tree.node d xs)) (hcd : d ≠ c) :
    Store.node_fields s t (some c) = ok (core.result.Result.Ok none) := by
  unfold Store.node_fields
  rw [Store.view_eq]
  have hlt := h.lt
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  cases h with
  | node _ _ v _ _ hd hl =>
    simp only [hd]
    obtain ⟨n1, h1, _⟩ := schema.Constructor.code_spec c
    obtain ⟨n2, h2, _⟩ := schema.Constructor.code_spec d
    simp only [h1, h2, Std.bind_ok]
    have : n2 ≠ n1 := by
      intro he; subst he; exact hcd (schema.Constructor.code_inj h2 h1)
    simp [this]

/-- The loop of `arguments_translate` without a mask: `true` only where
every argument has a translation. -/
theorem arguments_translate_loop_spec (h64 : Platform64) :
    ∀ (s : Store) (args : Term) (mask : Option (schema.Constructor × Std.Usize))
      (i : Std.Usize) (xs : Eo.CArgList),
      mask = none → s.Inv → Represents.rep s args xs → i.val + args.val < 2 ^ 32 →
      Store.arguments_translate_loop s args mask i ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok b => b = true → cArgListTranslationOk xs
        | core.result.Result.Err _ => True ⦄div := by
  apply Store.arguments_translate_loop.fixpoint_induct
    (motive := fun loop => ∀ (s : Store) (args : Term)
      (mask : Option (schema.Constructor × Std.Usize)) (i : Std.Usize) (xs : Eo.CArgList),
      mask = none → s.Inv → Represents.rep s args xs → i.val + args.val < 2 ^ 32 →
      loop s args mask i ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok b => b = true → cArgListTranslationOk xs
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih s args mask i xs hmask hinv hxs hbound
    subst hmask
    simp only
    obtain ⟨bn, hbn, hiffn⟩ := Store.is_node_holds schema.Constructor.eo__24emb_5fal_2enil hxs.1
    rw [hbn]
    simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    cases xs with
    | nil =>
      have : bn = true := hiffn.mpr ⟨[], rfl⟩
      simp only [this, ite_true, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun _ => trivial⟩
    | cons x rest =>
      have hbf : bn = false := by
        cases bn
        · rfl
        · obtain ⟨ys, hys⟩ := hiffn.mp rfl; cases hys
      simp only [hbf, Bool.false_eq_true, ite_false]
      obtain ⟨hh, hemb⟩ := hxs
      obtain ⟨v, hv, hl, hdat⟩ := Store.node_fields_holds hh
      rw [hv]
      simp only [Std.bind_ok]
      generalize hvv : v.val = l at hl
      cases hl with
      | cons a _ _ _ ha hl =>
        cases hl with
        | cons b _ _ _ hb hl =>
          cases hl with
          | nil =>
            obtain ⟨ex, erest⟩ := hemb
            step as ⟨a', ha'⟩
            have hav : a' = a := by rw [ha']; simp [hvv]
            subst hav
            unfold generated.part0.Store.argument_translates
            step with has_translation_spec s hinv h64 a' x ⟨ha, ex⟩ as ⟨r2, s1, hinv1, hg1, hr2⟩
            cases r2 with
            | Err e =>
              simp [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
              exact ⟨hinv1, hg1⟩
            | Ok b2 =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr2 ⊢
              split
              · rename_i hb2
                step as ⟨b', hb'⟩
                have hbv : b' = b := by rw [hb']; simp [hvv]
                subst hbv
                have hlt : b'.val < args.val := by
                  have hwf := hinv.terms.wf args.val hh.lt
                  rw [hdat] at hwf
                  have hmem : b' ∈ v.val := by rw [hvv]; simp
                  have := hwf.1 b' hmem
                  simp only [List.length_take] at this
                  omega
                step as ⟨i1, hi1⟩
                apply WP.dspec_mono (ih s1 b' none i1 rest rfl hinv1
                  (Represents.grows ⟨hb, erest⟩ hg1) (by scalar_tac))
                rintro ⟨r3, s3⟩ ⟨hinv3, hg3, hr3⟩
                refine ⟨hinv3, hg1.trans hg3, ?_⟩
                cases r3 with
                | Ok b3 => exact fun h3 => ⟨hr2 hb2, hr3 h3⟩
                | Err _ => trivial
              · simp only [WP.dspec_ok, WP.uncurry'_pair]
                exact ⟨hinv1, hg1, fun h => by cases h⟩

/-- `arguments_translate`: no rule of CpcMini has a mask, so every
argument is checked as a term. -/
theorem arguments_translate_spec (h64 : Platform64) (s : Store) (hinv : s.Inv) (args : Term)
    (rule : Option schema.Constructor) (xs : Eo.CArgList) (h : Represents.rep s args xs) :
    Store.arguments_translate s args rule ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok b => b = true → cArgListTranslationOk xs
      | core.result.Result.Err _ => True ⦄div := by
  have hb : 0 + args.val < 2 ^ 32 := by
    have : args.val < 2 ^ 32 := by scalar_tac
    simpa using this
  unfold Store.arguments_translate
  cases rule with
  | none =>
    simp only [Std.bind_ok]
    exact arguments_translate_loop_spec h64 s args none 0#usize xs rfl hinv h hb
  | some r =>
    simp only [Store.mask_len, Std.bind_ok]
    exact arguments_translate_loop_spec h64 s args none 0#usize xs rfl hinv h hb

/-- A handle of a rule is a node. -/
theorem rule_node {s : Store} {t : Term} {x : Eo.CRule} (h : Represents.rep s t x) :
    ∃ c v, s.nodes.val[t.val]! = TermData.Node c v := by
  obtain ⟨hh, _⟩ := h
  change Holds s.nodes.val t.val (Embed.enc_CRule x) at hh
  cases x <;> (simp only [Embed.enc_CRule] at hh; cases hh with | node _ _ v _ _ hd _ => exact ⟨_, v, hd⟩)

/-- The loop over the commands: `Correct` only where every command meets
logos's side condition. -/
theorem check_proof_inner_loop_spec (h64 : Platform64) :
    ∀ (s : Store) (list : Term) (pf : Eo.CCmdList), s.Inv → Represents.rep s list pf →
      Store.check_proof_inner_loop s list ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok v => v = Verdict.Correct → CmdListTranslationOk pf
        | core.result.Result.Err _ => True ⦄div := by
  apply Store.check_proof_inner_loop.fixpoint_induct
    (motive := fun loop => ∀ (s : Store) (list : Term) (pf : Eo.CCmdList), s.Inv →
      Represents.rep s list pf →
      loop s list ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
        match r with
        | core.result.Result.Ok v => v = Verdict.Correct → CmdListTranslationOk pf
        | core.result.Result.Err _ => True ⦄div)
  · prove_adm
  · intro loop ih s list pf hinv hpf
    simp only
    obtain ⟨bn, hbn, hiffn⟩ := Store.is_node_holds schema.Constructor.eo__24emb_5fcmdl_2enil hpf.1
    rw [hbn]
    simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    cases pf with
    | nil =>
      have : bn = true := hiffn.mpr ⟨[], rfl⟩
      simp only [this, ite_true, WP.dspec_ok, WP.uncurry'_pair]
      exact ⟨hinv, Store.Grows.refl s, fun _ => CmdListTranslationOk.nil⟩
    | cons cmd rest =>
      have hbf : bn = false := by
        cases bn
        · rfl
        · obtain ⟨ys, hys⟩ := hiffn.mp rfl; cases hys
      simp only [hbf, Bool.false_eq_true, ite_false]
      obtain ⟨hh, hemb⟩ := hpf
      obtain ⟨v, hv, hl, _⟩ := Store.node_fields_holds hh
      rw [hv]
      simp only [Std.bind_ok]
      generalize hvv : v.val = l at hl
      cases hl with
      | cons a _ _ _ ha hl =>
        cases hl with
        | cons b _ _ _ hb hl =>
          cases hl with
          | nil =>
            obtain ⟨ecmd, erest⟩ := hemb
            step as ⟨a', ha'⟩
            have hav : a' = a := by rw [ha']; simp [hvv]
            subst hav
            -- the rest of the list, from a store that grew
            have hnext : ∀ (s1 : Store), s1.Inv → s.Grows s1 → cmdTranslationOk cmd →
                (do
                  let list1 ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice Term) v 1#usize
                  loop s1 list1) ⦃ r s' => s'.Inv ∧ s.Grows s' ∧
                  match r with
                  | core.result.Result.Ok v => v = Verdict.Correct →
                      CmdListTranslationOk (Eo.CCmdList.cons cmd rest)
                  | core.result.Result.Err _ => True ⦄div := by
              intro s1 hinv1 hg1 hok
              step as ⟨b', hb'⟩
              have hbv : b' = b := by rw [hb']; simp [hvv]
              subst hbv
              apply WP.dspec_mono (ih s1 b' rest hinv1 (Represents.grows ⟨hb, erest⟩ hg1))
              rintro ⟨r3, s3⟩ ⟨hinv3, hg3, hr3⟩
              refine ⟨hinv3, hg1.trans hg3, ?_⟩
              cases r3 with
              | Ok v3 => exact fun h3 => CmdListTranslationOk.cons _ _ hok (hr3 h3)
              | Err _ => trivial
            have hcmd : Holds s.nodes.val a'.val (Embed.enc_CCmd cmd) := ha
            cases cmd with
            | assume_push A =>
              simp only [Embed.enc_CCmd] at hcmd
              obtain ⟨w, hw, hwl, _⟩ := Store.node_fields_holds hcmd
              rw [hw]
              simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
              generalize hww : w.val = lw at hwl
              cases hwl with
              | cons f _ _ _ hf hwl =>
                cases hwl with
                | nil =>
                  step as ⟨f', hf'⟩
                  have hfv : f' = f := by rw [hf']; simp [hww]
                  subst hfv
                  step with has_translation_spec s hinv h64 f' A ⟨hf, ecmd⟩
                    as ⟨r2, s1, hinv1, hg1, hr2⟩
                  cases r2 with
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                    exact ⟨hinv1, hg1⟩
                  | Ok b2 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr2 ⊢
                    split
                    · rename_i hb2
                      exact hnext s1 hinv1 hg1 (hr2 hb2)
                    · simp only [WP.dspec_ok, WP.uncurry'_pair]
                      exact ⟨hinv1, hg1, fun h => by cases h⟩
            | step r args prem =>
              simp only [Embed.enc_CCmd] at hcmd
              rw [Store.node_fields_other hcmd (by decide)]
              simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
              obtain ⟨w, hw, hwl, _⟩ := Store.node_fields_holds hcmd
              rw [hw]
              simp only [Std.bind_ok]
              obtain ⟨er, eargs, _⟩ := ecmd
              generalize hww : w.val = lw at hwl
              cases hwl with
              | cons f _ _ _ hf hwl =>
                cases hwl with
                | cons g _ _ _ hg hwl =>
                  step as ⟨f', hf'⟩
                  have hfv : f' = f := by rw [hf']; simp [hww]
                  subst hfv
                  obtain ⟨rc, rv, hrd⟩ := rule_node (s := s) (t := f') (x := r) ⟨hf, er⟩
                  rw [Store.view_eq, if_pos hf.lt]
                  simp only [hrd, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
                  step as ⟨g', hg'⟩
                  have hgv : g' = g := by rw [hg']; simp [hww]
                  subst hgv
                  step with arguments_translate_spec h64 s hinv g' (some rc) args ⟨hg, eargs⟩
                    as ⟨r2, s1, hinv1, hg1, hr2⟩
                  cases r2 with
                  | Err e =>
                    simp [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
                    exact ⟨hinv1, hg1⟩
                  | Ok b2 =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr2 ⊢
                    split
                    · rename_i hb2
                      exact hnext s1 hinv1 hg1 (hr2 hb2)
                    · simp only [WP.dspec_ok, WP.uncurry'_pair]
                      exact ⟨hinv1, hg1, fun h => by cases h⟩
            | check_proven A =>
              simp only [Embed.enc_CCmd] at hcmd
              rw [Store.node_fields_other hcmd (by decide)]
              simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
              rw [Store.node_fields_other hcmd (by decide)]
              simp only [Std.bind_ok]
              exact hnext s hinv (Store.Grows.refl s) trivial
            | step_pop r args prem =>
              simp only [Embed.enc_CCmd] at hcmd
              rw [Store.node_fields_other hcmd (by decide)]
              simp only [Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
              rw [Store.node_fields_other hcmd (by decide)]
              simp only [Std.bind_ok]
              exact hnext s hinv (Store.Grows.refl s) trivial

/-! ## The entry and the theorem -/

/-- `check_proof_inner`: `Correct` only where logos's checker says the
proof refutes the assumptions, and both of logos's side conditions hold. -/
theorem check_proof_inner_spec (hchk : ∀ n, CheckerIsRefutationSpec n)
    (s : Store) (hinv : s.Inv) (h64 : Platform64) (a c : Term)
    (F : Eo.CArgList) (pf : Eo.CCmdList)
    (hF : Represents.rep s a F) (hpf : Represents.rep s c pf) :
    Store.check_proof_inner s a c ⦃ r s' =>
      match r with
      | core.result.Result.Ok v => v = Verdict.Correct →
          TranslatableAssumptionList F ∧ CmdListTranslationOk pf ∧ Eo.eo_is_refutation F pf
      | core.result.Result.Err _ => True ⦄div := by
  unfold Store.check_proof_inner
  step with check_refutation_inner_spec hchk s hinv h64 a c F pf hF hpf
    as ⟨r, s1, hinv1, hpre1, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  | Ok b =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr ⊢
    split
    · rename_i hb
      have hF1 : Represents.rep s1 a F := Rep.mono hpre1 hF
      have hpf1 : Represents.rep s1 c pf := Rep.mono hpre1 hpf
      step with arguments_translate_spec h64 s1 hinv1 a none F hF1 as ⟨r2, s2, hinv2, hg2, hr2⟩
      cases r2 with
      | Err e =>
        simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
      | Ok b2 =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok] at hr2 ⊢
        split
        · rename_i hb2
          apply WP.dspec_mono (check_proof_inner_loop_spec h64 s2 c pf hinv2
            (Represents.grows hpf1 hg2))
          rintro ⟨r3, s3⟩ ⟨_, _, hr3⟩
          cases r3 with
          | Ok v => exact fun hv => ⟨hr2 hb2, hr3 hv, hr hb⟩
          | Err _ => trivial
        · simp
    · simp

/-- The top-level theorem, from any proof of `$eo_checker_is_refutation`'s
spec (`hchk`); `check_proof_correct` below is it with the generated one. -/
theorem check_proof_correct_of_spec (hchk : ∀ n, CheckerIsRefutationSpec n)
    (s : Store) (hinv : s.Inv) (h64 : Platform64) (a c : Term)
    (F : Eo.CArgList) (pf : Eo.CCmdList)
    (hF : Represents.rep s a F) (hpf : Represents.rep s c pf) (s' : Store)
    (hrun : Store.check_proof_inner s a c = ok (core.result.Result.Ok Verdict.Correct, s')) :
    eo_satisfiability (argListAssumes F) false := by
  have h := check_proof_inner_spec hchk s hinv h64 a c F pf hF hpf
  rw [hrun] at h
  simp only [WP.dspec_ok, WP.uncurry'_pair] at h
  obtain ⟨hT, hC, hR⟩ := h trivial
  exact correct___eo_is_refutation F pf hT hC hR

/-- **The top-level theorem for CpcMini.** If the compiled checker says
`Correct` on handles of the assumptions `F` and the proof `pf`, then `F` is
unsatisfiable, as logos defines it (`eo_satisfiability`).

Its boundary:
- It is about `check_proof_inner`. `Store::check_proof` is that function
  run by `with_checker_stack` on a thread with a larger stack; both are in
  `front.rs`, which is not translated.
- CpcMini has no front end: `crates/pathos` builds the full CPC's checker.
  The theorem holds of any store with the invariant and any handles that
  stand for some `F` and `pf`.
- It is partial correctness: of a run that returns `Correct`. Other
  verdicts, errors and runs that do not return are not covered.
- `Platform64` (a 64-bit `usize`) is assumed, as in every spec. -/
theorem check_proof_correct
    (s : Store) (hinv : s.Inv) (h64 : Platform64) (a c : Term)
    (F : Eo.CArgList) (pf : Eo.CCmdList)
    (hF : Represents.rep s a F) (hpf : Represents.rep s c pf) (s' : Store)
    (hrun : Store.check_proof_inner s a c = ok (core.result.Result.Ok Verdict.Correct, s')) :
    eo_satisfiability (argListAssumes F) false :=
  check_proof_correct_of_spec (fun n => (specs n).eo__24eo_5fchecker_5fis_5frefutation)
    s hinv h64 a c F pf hF hpf s' hrun

end pathos_compiled_checker
