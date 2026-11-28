module
public import PathosProofs.Runtime.CompareTerm
public import PathosProofs.Runtime.Node

/-!
# `destruct` of a user operator's wrapper view

A pattern `($emb_UOp<k> op i1 … ik)` takes a term of a user operator with
`k` indices apart: the runtime's `destruct` (`destruct_user`) answers for a
node of any user operator with `k` fields, with a fresh handle of the
operator itself (`TermData.UserOp`), then the handles of the fields.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `destruct` with a constructor of the wrapper view of user operators
(`$emb_UOp<k>`, whose embedding is `UOp`) on a handle of the tree `x`: if
`x` is a node of a user operator with one field fewer than the constructor
takes, a handle of the operator, then the handles of the node's fields;
nothing for any other tree. The store may grow by the operator's handle. -/
theorem Store.destruct_user_holds (s : Store) (c : schema.Constructor) (t : Term) {x : Tree}
    (hc : c.embedding = ok Embedding.UOp) (h : Holds s.nodes.val t.val x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s c t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (d : schema.Constructor) (op : Term) (fields : List Term) (xs : List Tree)
          (n : Std.Usize),
          x = Tree.node d xs ∧ d.is_user = ok true ∧ c.arity = ok n ∧
          n.val = xs.length + 1 ∧ v.val = op :: fields ∧ HoldsList s'.nodes.val fields xs
      | core.result.Result.Ok none =>
        ∀ d xs, x = Tree.node d xs → d.is_user = ok true → ∀ n, c.arity = ok n →
          n.val ≠ xs.length + 1
      | core.result.Result.Err _ => True ⦄div := by
  have hlt := h.lt
  unfold Store.destruct
  rw [hc]
  simp only [Std.bind_ok]
  unfold Store.destruct_user
  rw [Store.view_eq]
  simp only [hlt, ite_true, Std.bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
  have none_ok : ∀ (hx : ∀ d xs, x = Tree.node d xs → False),
      ∀ d xs, x = Tree.node d xs → d.is_user = ok true → ∀ n, c.arity = ok n →
        n.val ≠ xs.length + 1 := fun hx d xs he _ _ _ => (hx d xs he).elim
  cases h with
  | node _ d v xs _ hd hl =>
    simp only [hd]
    obtain ⟨b, hb⟩ := schema.Constructor.is_user_ok d
    rw [hb]
    simp only [Std.bind_ok]
    have hvl : v.val.length = xs.length := hl.length
    cases b
    · simp only [Bool.false_eq_true, ite_false, WP.dspec_ok, WP.uncurry'_pair]
      refine ⟨hinv, Store.Grows.refl s, ?_⟩
      intro d' xs' he hu
      injection he with h1 _
      subst h1
      rw [hb] at hu
      exact (Bool.false_ne_true (Result.ok_injective hu)).elim
    · simp only [ite_true]
      -- the node's fields are as many as its constructor takes: at most 100
      have hwf := hinv.terms.wf t.val hlt
      rw [hd] at hwf
      obtain ⟨-, ⟨m, hm, hml⟩, -⟩ := hwf
      have hm100 := arity_le d m hm
      have h40 : (2 : Nat) ^ 40 ≤ Usize.max := h64
      have hvlen : v.length ≤ 100 := by
        simp only [alloc.vec.Vec.length] at hml ⊢; omega
      step as ⟨i1, hi1⟩
      obtain ⟨n, hn⟩ := schema.Constructor.arity_ok c
      rw [hn]
      simp only [Std.bind_ok]
      by_cases heq : i1 = n
      · subst heq
        rw [if_pos rfl, alloc.vec.CloneVec.clone_terms]
        erw [Std.bind_ok]
        have hwfu : (TermData.UserOp d).Wf s.nodes.val := by simp [TermData.Wf]
        step with Store.intern_inv s (TermData.UserOp d) hinv hwfu h64 as ⟨r, s1, hinv1, hext, hres⟩
        cases r with
        | Err e =>
          simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          exact ⟨hinv1, hext.grows⟩
        | Ok op =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, Std.bind_ok, bind_tc_ok]
          step as ⟨i3, hi3⟩
          have hwc : (alloc.vec.Vec.with_capacity Term i3).val = [] := by
            simp [alloc.vec.Vec.with_capacity]
          step with alloc.vec.Vec.push_spec (alloc.vec.Vec.with_capacity Term i3) op
            (by rw [hwc]; simp; omega) as ⟨args1, ha1⟩
          rw [hwc] at ha1
          unfold alloc.vec.Vec.extend_from_slice
          have hsum : args1.length + (alloc.vec.Vec.deref v).length ≤ Usize.max := by
            simp only [alloc.vec.Vec.length, alloc.vec.Vec.deref, Slice.length, ha1] at hvlen ⊢
            simp; omega
          simp only [hsum, _root_.dite_true]
          obtain ⟨l', hcl, hl'⟩ := spec_returns (List.clone_spec
            (clone := Term.Insts.CoreCloneClone.clone) (l := (alloc.vec.Vec.deref v).val)
            (fun _ _ => rfl))
          rw [hcl]
          erw [bind_tc_ok]
          first | erw [Std.bind_ok] | simp only [Std.bind_ok, bind_tc_ok]
          simp only [WP.dspec_ok, WP.uncurry'_pair]
          refine ⟨hinv1, hext.grows, d, op, v.val, xs, i1, rfl, hb, rfl, ?_, ?_,
            HoldsList.mono hext.1 hl⟩
          · rw [alloc.vec.Vec.len_val] at hi1
            simp only [alloc.vec.Vec.length] at hi1; omega
          · have ha1' : args1.slice.val = [op] := by simpa [alloc.vec.Vec.val] using ha1
            simp [alloc.vec.Vec.from, alloc.vec.Vec.val, ha1', hl', alloc.vec.Vec.deref]
      · rw [if_neg heq]
        simp only [WP.dspec_ok, WP.uncurry'_pair]
        refine ⟨hinv, Store.Grows.refl s, ?_⟩
        intro d' xs' he _ n' hn'
        injection he with _ h2
        subst h2
        obtain rfl := Result.ok_injective hn'
        intro hval
        apply heq
        apply UScalar.eq_of_val_eq
        rw [alloc.vec.Vec.len_val] at hi1
        simp only [alloc.vec.Vec.length] at hi1
        omega
  | stuck _ _ hd =>
    simp only [hd, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ he => by cases he)⟩
  | lit _ _ _ hd =>
    simp only [hd, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ he => by cases he)⟩
  | native _ _ _ hd =>
    simp only [hd, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ he => by cases he)⟩
  | userop _ _ _ hd =>
    simp only [hd, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ he => by cases he)⟩
  | apply _ _ _ _ _ _ hd _ _ =>
    simp only [hd, WP.dspec_ok, WP.uncurry'_pair]
    exact ⟨hinv, Store.Grows.refl s, none_ok (fun _ _ he => by cases he)⟩

end pathos_compiled_checker
