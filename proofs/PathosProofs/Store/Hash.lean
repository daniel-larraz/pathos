module
public import MiniChecker
public import PathosProofs.Util
public import PathosProofs.Trusted
public import PathosProofs.Store.SameData

/-!
# The hash of a term's data does not fail

The table of terms needs nothing of a hash's value: a search compares the
data it finds. What it needs is that computing one does not panic.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

@[step]
theorem table.mix_spec (h w : Std.U64) : table.mix h w ⦃ _ => True ⦄ := by
  unfold table.mix
  step*

@[step]
theorem table.fold_spec (h : Std.U64) : table.fold h ⦃ _ => True ⦄ := by
  unfold table.fold
  step*

@[step]
theorem num.Integer.hash_code_ok (a : num.Integer) :
    num.Integer.hash_code a ⦃ _ => True ⦄ := by
  obtain ⟨h, hh⟩ := num.Integer.hash_code_spec a
  rw [hh]; simp

@[step]
theorem num.Rational.hash_code_ok (a : num.Rational) :
    num.Rational.hash_code a ⦃ _ => True ⦄ := by
  obtain ⟨h, hh⟩ := num.Rational.hash_code_spec a
  rw [hh]; simp

theorem lit.Lit.hash_code_loop_spec (codes : Slice Std.U32) (h : Std.U64) (i : Std.Usize) :
    lit.Lit.hash_code_loop codes h i ⦃ _ => True ⦄div := by
  revert h i
  apply lit.Lit.hash_code_loop.fixpoint_induct codes
    (motive := fun f => ∀ (h : Std.U64) (i : Std.Usize), f h i ⦃ _ => True ⦄div)
  · prove_adm
  · intro loop ih h i
    simp only
    split
    · step*
    · simp

@[step]
theorem lit.Lit.hash_code_spec (l : lit.Lit) : lit.Lit.hash_code l ⦃ _ => True ⦄div := by
  unfold lit.Lit.hash_code
  cases l <;> simp only
  case Hex b => unfold bitvec.BitVec.impl.size bitvec.BitVec.impl.value; step*
  case Binary b => unfold bitvec.BitVec.impl.size bitvec.BitVec.impl.value; step*
  case Str s =>
    unfold eostring.EoString.code_points
    step*
    apply lit.Lit.hash_code_loop_spec
  all_goals step*

theorem Store.data_hash_loop_spec (fields : alloc.vec.Vec Term) (h : Std.U64) (i : Std.Usize) :
    Store.data_hash_loop fields h i ⦃ _ => True ⦄div := by
  revert h i
  apply Store.data_hash_loop.fixpoint_induct fields
    (motive := fun f => ∀ (h : Std.U64) (i : Std.Usize), f h i ⦃ _ => True ⦄div)
  · prove_adm
  · intro loop ih h i
    simp only
    split
    · step*
    · simp

/-- Computing the hash of a term's data does not fail. -/
@[step]
theorem Store.data_hash_spec (data : TermData) : Store.data_hash data ⦃ _ => True ⦄div := by
  unfold Store.data_hash
  cases data <;> simp only
  case UserOp c =>
    obtain ⟨n, hn, _⟩ := schema.Constructor.code_spec c
    rw [hn]; step*
  case Node c fields =>
    obtain ⟨n, hn, _⟩ := schema.Constructor.code_spec c
    rw [hn]
    step
    step
    step with Store.data_hash_loop_spec
    step*
  all_goals step*

end pathos_compiled_checker
