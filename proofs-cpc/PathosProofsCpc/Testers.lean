module
public import CpcChecker
public import Cpc.Logos
import all Cpc.Logos
public import Cpc.SmtEval
import all Cpc.SmtEval
public import PathosProofs.Runtime.Natives

/-!
# The recognizers of CPC (CPC only)

`eo::is_z` and the others, which CpcMini's logos does not define, so the
shared library cannot state them (milestone 6, option (b)): the runtime's
`recognizes` looks at a handle's literal, and logos's `__eo_is_z` at the
term's form. No split over the terms: a handle of a literal is one of the
literal forms (`Embed.inv_Term_lit`), and of anything else is not one.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `recognizes` with `IsBool` on a handle of a term: logos's `__eo_is_bool`. -/
theorem Store.recognizes_is_bool {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    ∃ b, Store.recognizes s kind.EvalOp.IsBool t = ok (core.result.Result.Ok b) ∧
      Eo.__eo_is_bool x = Eo.Term.Boolean b := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.recognizes
  have hv : kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq kind.EvalOp.IsBool kind.EvalOp.IsVar =
      ok false := by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant]
  simp only [hv, Std.bind_ok, Bool.false_eq_true, ite_false]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have hnot : (∀ l, tx ≠ Tree.lit l) → Eo.__eo_is_bool x = Eo.Term.Boolean false := by
    intro hl
    have hN : ∀ x0, x ≠ Eo.Term.Boolean x0 := by
      intro x0 hi; subst hi
      apply hl (lit.Lit.Boolean x0)
      rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term]
    by_cases hS : x = Eo.Term.Stuck
    · subst hS; simp [Eo.__eo_is_bool, Eo.__eo_is_bool_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]
    have hi : Eo.__eo_is_bool_internal x = Eo.Term.Boolean false := by
      unfold Eo.__eo_is_bool_internal; split <;> simp_all
    simp [Eo.__eo_is_bool, hi, Eo.native_teq, SmtEval.native_and, SmtEval.native_not, hS]
  cases hh
  case lit l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · refine ⟨true, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bool, Eo.__eo_is_bool_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bool, Eo.__eo_is_bool_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bool, Eo.__eo_is_bool_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bool, Eo.__eo_is_bool_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bool, Eo.__eo_is_bool_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
  all_goals
    rename_i hd
    simp only [hd]
    exact ⟨false, rfl, hnot (fun l h => by cases h)⟩

/-- `eo::is_bool` on a handle of a term: a handle of logos's `__eo_is_bool`. -/
theorem Store.builtin_spec_is_bool (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsBool args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_bool x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsBool 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    obtain ⟨b, hrec, hb⟩ := Store.recognizes_is_bool ha
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0, hrec, Store.boolean]
    rw [hb]
    exact Store.literal_boolean_spec s _ hinv h64

/-- `recognizes` with `IsZ` on a handle of a term: logos's `__eo_is_z`. -/
theorem Store.recognizes_is_z {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    ∃ b, Store.recognizes s kind.EvalOp.IsZ t = ok (core.result.Result.Ok b) ∧
      Eo.__eo_is_z x = Eo.Term.Boolean b := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.recognizes
  have hv : kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq kind.EvalOp.IsZ kind.EvalOp.IsVar =
      ok false := by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant]
  simp only [hv, Std.bind_ok, Bool.false_eq_true, ite_false]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have hnot : (∀ l, tx ≠ Tree.lit l) → Eo.__eo_is_z x = Eo.Term.Boolean false := by
    intro hl
    have hN : ∀ x0, x ≠ Eo.Term.Numeral x0 := by
      intro x0 hi; subst hi
      apply hl (lit.Lit.Numeral (num.Integer.ofInt x0))
      rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term]
    by_cases hS : x = Eo.Term.Stuck
    · subst hS; simp [Eo.__eo_is_z, Eo.__eo_is_z_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]
    have hi : Eo.__eo_is_z_internal x = Eo.Term.Boolean false := by
      unfold Eo.__eo_is_z_internal; split <;> simp_all
    simp [Eo.__eo_is_z, hi, Eo.native_teq, SmtEval.native_and, SmtEval.native_not, hS]
  cases hh
  case lit l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_z, Eo.__eo_is_z_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨true, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_z, Eo.__eo_is_z_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_z, Eo.__eo_is_z_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_z, Eo.__eo_is_z_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_z, Eo.__eo_is_z_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
  all_goals
    rename_i hd
    simp only [hd]
    exact ⟨false, rfl, hnot (fun l h => by cases h)⟩

/-- `eo::is_z` on a handle of a term: a handle of logos's `__eo_is_z`. -/
theorem Store.builtin_spec_is_z (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsZ args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_z x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsZ 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    obtain ⟨b, hrec, hb⟩ := Store.recognizes_is_z ha
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0, hrec, Store.boolean]
    rw [hb]
    exact Store.literal_boolean_spec s _ hinv h64

/-- `recognizes` with `IsQ` on a handle of a term: logos's `__eo_is_q`. -/
theorem Store.recognizes_is_q {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    ∃ b, Store.recognizes s kind.EvalOp.IsQ t = ok (core.result.Result.Ok b) ∧
      Eo.__eo_is_q x = Eo.Term.Boolean b := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.recognizes
  have hv : kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq kind.EvalOp.IsQ kind.EvalOp.IsVar =
      ok false := by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant]
  simp only [hv, Std.bind_ok, Bool.false_eq_true, ite_false]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have hnot : (∀ l, tx ≠ Tree.lit l) → Eo.__eo_is_q x = Eo.Term.Boolean false := by
    intro hl
    have hN : ∀ x0, x ≠ Eo.Term.Rational x0 := by
      intro x0 hi; subst hi
      apply hl (lit.Lit.Rational (num.Rational.ofRat x0))
      rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term]
    by_cases hS : x = Eo.Term.Stuck
    · subst hS; simp [Eo.__eo_is_q, Eo.__eo_is_q_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]
    have hi : Eo.__eo_is_q_internal x = Eo.Term.Boolean false := by
      unfold Eo.__eo_is_q_internal; split <;> simp_all
    simp [Eo.__eo_is_q, hi, Eo.native_teq, SmtEval.native_and, SmtEval.native_not, hS]
  cases hh
  case lit l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_q, Eo.__eo_is_q_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_q, Eo.__eo_is_q_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨true, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_q, Eo.__eo_is_q_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_q, Eo.__eo_is_q_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_q, Eo.__eo_is_q_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
  all_goals
    rename_i hd
    simp only [hd]
    exact ⟨false, rfl, hnot (fun l h => by cases h)⟩

/-- `eo::is_q` on a handle of a term: a handle of logos's `__eo_is_q`. -/
theorem Store.builtin_spec_is_q (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsQ args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_q x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsQ 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    obtain ⟨b, hrec, hb⟩ := Store.recognizes_is_q ha
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0, hrec, Store.boolean]
    rw [hb]
    exact Store.literal_boolean_spec s _ hinv h64

/-- `recognizes` with `IsStr` on a handle of a term: logos's `__eo_is_str`. -/
theorem Store.recognizes_is_str {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    ∃ b, Store.recognizes s kind.EvalOp.IsStr t = ok (core.result.Result.Ok b) ∧
      Eo.__eo_is_str x = Eo.Term.Boolean b := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.recognizes
  have hv : kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq kind.EvalOp.IsStr kind.EvalOp.IsVar =
      ok false := by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant]
  simp only [hv, Std.bind_ok, Bool.false_eq_true, ite_false]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have hnot : (∀ l, tx ≠ Tree.lit l) → Eo.__eo_is_str x = Eo.Term.Boolean false := by
    intro hl
    have hN : ∀ x0, x ≠ Eo.Term.String x0 := by
      intro x0 hi; subst hi
      apply hl (lit.Lit.Str (Tree.strOf x0))
      rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term]
    by_cases hS : x = Eo.Term.Stuck
    · subst hS; simp [Eo.__eo_is_str, Eo.__eo_is_str_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]
    have hi : Eo.__eo_is_str_internal x = Eo.Term.Boolean false := by
      unfold Eo.__eo_is_str_internal; split <;> simp_all
    simp [Eo.__eo_is_str, hi, Eo.native_teq, SmtEval.native_and, SmtEval.native_not, hS]
  cases hh
  case lit l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_str, Eo.__eo_is_str_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_str, Eo.__eo_is_str_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_str, Eo.__eo_is_str_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨true, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_str, Eo.__eo_is_str_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_str, Eo.__eo_is_str_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
  all_goals
    rename_i hd
    simp only [hd]
    exact ⟨false, rfl, hnot (fun l h => by cases h)⟩

/-- `eo::is_str` on a handle of a term: a handle of logos's `__eo_is_str`. -/
theorem Store.builtin_spec_is_str (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsStr args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_str x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsStr 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    obtain ⟨b, hrec, hb⟩ := Store.recognizes_is_str ha
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0, hrec, Store.boolean]
    rw [hb]
    exact Store.literal_boolean_spec s _ hinv h64

/-- `recognizes` with `IsBin` on a handle of a term: logos's `__eo_is_bin`. -/
theorem Store.recognizes_is_bin {s : Store} {t : Term} {x : Eo.Term} (h : s.Rep t x) :
    ∃ b, Store.recognizes s kind.EvalOp.IsBin t = ok (core.result.Result.Ok b) ∧
      Eo.__eo_is_bin x = Eo.Term.Boolean b := by
  have hlt := h.lt
  obtain ⟨hh, _⟩ := h
  unfold Store.recognizes
  have hv : kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq kind.EvalOp.IsBin kind.EvalOp.IsVar =
      ok false := by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant]
  simp only [hv, Std.bind_ok, Bool.false_eq_true, ite_false]
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  generalize hx : Embedded.enc x = tx at hh
  have hnot : (∀ l, tx ≠ Tree.lit l) → Eo.__eo_is_bin x = Eo.Term.Boolean false := by
    intro hl
    have hN : ∀ x0 x1, x ≠ Eo.Term.Binary x0 x1 := by
      intro x0 x1 hi; subst hi
      apply hl (lit.Lit.Binary (Tree.bvOf x0 x1))
      rw [← hx]; simp [Embed.embedded_enc_Term, Embed.enc_Term]
    by_cases hS : x = Eo.Term.Stuck
    · subst hS; simp [Eo.__eo_is_bin, Eo.__eo_is_bin_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]
    have hi : Eo.__eo_is_bin_internal x = Eo.Term.Boolean false := by
      unfold Eo.__eo_is_bin_internal; split <;> simp_all
    simp [Eo.__eo_is_bin, hi, Eo.native_teq, SmtEval.native_and, SmtEval.native_not, hS]
  cases hh
  case lit l _ hd =>
    simp only [hd]
    rcases Embed.inv_Term_lit hx with ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ | ⟨_, rfl, rfl⟩ |
      ⟨_, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bin, Eo.__eo_is_bin_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bin, Eo.__eo_is_bin_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bin, Eo.__eo_is_bin_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨false, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bin, Eo.__eo_is_bin_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
    · refine ⟨true, by simp [kind.EvalOp.Insts.CoreCmpPartialEqEvalOp.eq, kind.EvalOp.read_discriminant], by simp [Eo.__eo_is_bin, Eo.__eo_is_bin_internal, Eo.native_teq, SmtEval.native_and, SmtEval.native_not]⟩
  all_goals
    rename_i hd
    simp only [hd]
    exact ⟨false, rfl, hnot (fun l h => by cases h)⟩

/-- `eo::is_bin` on a handle of a term: a handle of logos's `__eo_is_bin`. -/
theorem Store.builtin_spec_is_bin (s : Store) (args : Slice Term) {a : Term} {x : Eo.Term}
    (hargs : args.val = [a]) (ha : s.Rep a x) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsBin args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_bin x)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 1#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsBin 1#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    obtain ⟨b, hrec, hb⟩ := Store.recognizes_is_bin ha
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0, hrec, Store.boolean]
    rw [hb]
    exact Store.literal_boolean_spec s _ hinv h64

/-- `eo::is_eq` on handles of two terms: whether they are the same term, not stuck. -/
theorem Store.builtin_spec_is_eq (s : Store) (args : Slice Term) {a b : Term} {x y : Eo.Term}
    (hargs : args.val = [a, b]) (ha : s.Rep a x) (hb : s.Rep b y) (hinv : s.Inv) (h64 : Platform64) :
    Store.builtin_core s kind.EvalOp.IsEq args ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok t => s'.Rep t (Eo.__eo_is_eq x y)
      | core.result.Result.Err _ => True ⦄div := by
  have hlen : Slice.len args = 2#usize := by
    apply UScalar.eq_of_val_eq; simp [Slice.len, hargs]
  have h0 : Slice.index_usize args 0#usize = ok a := by simp [Slice.index_usize, hargs]
  have h1 : Slice.index_usize args 1#usize = ok b := by simp [Slice.index_usize, hargs]
  have htakes : Store.takes kind.EvalOp.IsEq 2#usize = ok true := by
    simp [Store.takes, kind.EvalOp.is_nary]
  unfold Store.builtin_core
  simp only [hlen, htakes, Std.bind_ok, ite_true]
  step with Store.check_handles_loop_spec s args 0#usize as ⟨r, hr⟩
  cases r with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from]
    exact ⟨hinv, Store.Grows.refl s⟩
  | Ok u =>
    have hv : Eo.__eo_is_eq x y = Eo.Term.Boolean
        (!decide (x = Eo.Term.Stuck) && (!decide (y = Eo.Term.Stuck) && decide (x = y))) := by
      simp [Eo.__eo_is_eq, Eo.native_teq, SmtEval.native_and, SmtEval.native_not, eq_comm]
    rw [hv]
    have hd : decide (a = b) = decide (x = y) := by simp [Represents.eq_iff hinv ha hb]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, h0, h1,
      Store.Rep.is_stuck ha, Store.Rep.is_stuck hb, Store.boolean,
      Term.Insts.CoreCmpPartialEqTerm.eq, hd]
    by_cases hx : x = Eo.Term.Stuck <;> by_cases hy : y = Eo.Term.Stuck <;>
      simp only [hx, hy, decide_true, decide_false, Bool.not_true, Bool.not_false,
        Bool.false_eq_true, Bool.false_and, Bool.true_and, ite_true, ite_false,
        Std.bind_ok, Bool.and_false, not_false_eq_true] <;>
      exact Store.literal_boolean_spec s _ hinv h64

end pathos_compiled_checker
