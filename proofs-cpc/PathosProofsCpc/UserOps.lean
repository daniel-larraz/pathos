module
public import CpcEmbed
public import PathosProofs.Runtime.UserOps

/-!
# The terms of user operators with indices (CPC only)

`Store.destruct_user_holds` (PathosProofs/Runtime/UserOps.lean) says what
`destruct` with `$emb_UOp<k>` gives on a handle of a tree. Here: on a handle
of a term, it gives the operator's handle and the indices' for a term
`UOp<k> u x0 …`, and nothing for any other term (`Store.destruct_uop<k>_spec`),
as CpcMini's logos has no user operators with indices.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

open Embed in
theorem not_user_of {c : schema.Constructor} (hu : c.is_user = ok true)
    (h : c.is_user = ok false) : False :=
  Bool.false_ne_true (Result.ok_injective (h.symm.trans hu))

open Embed in
theorem uop_is_user (u : Eo.UserOp) : (uop u).is_user = ok true := by
  cases u <;> rfl

open Embed in
theorem uop1_is_user (u : Eo.UserOp1) : (uop1 u).is_user = ok true := by
  cases u <;> rfl

open Embed in
theorem uop2_is_user (u : Eo.UserOp2) : (uop2 u).is_user = ok true := by
  cases u <;> rfl

open Embed in
theorem uop3_is_user (u : Eo.UserOp3) : (uop3 u).is_user = ok true := by
  cases u <;> rfl

open Embed in
/-- The nodes of user operators that `enc` makes are the terms of user
operators: with as many fields as the operator has indices. -/
theorem enc_Term_user_node {x : Eo.Term} {c : schema.Constructor} {ts : List Tree}
    (h : enc_Term x = Tree.node c ts) (hu : c.is_user = ok true) :
    (∃ u, x = Eo.Term.UOp u ∧ ts = []) ∨
    (∃ u x0, x = Eo.Term.UOp1 u x0 ∧ ts = [enc_Term x0]) ∨
    (∃ u x0 x1, x = Eo.Term.UOp2 u x0 x1 ∧ ts = [enc_Term x0, enc_Term x1]) ∨
    (∃ u x0 x1 x2, x = Eo.Term.UOp3 u x0 x1 x2 ∧
      ts = [enc_Term x0, enc_Term x1, enc_Term x2]) := by
  cases x <;> simp only [enc_Term, Tree.node.injEq, reduceCtorEq] at h
  all_goals first
    | exact (not_user_of hu rfl).elim
    | (obtain ⟨rfl, -⟩ := h; exact (not_user_of hu rfl).elim)
    | (obtain ⟨rfl, rfl⟩ := h; simp; done)

open Embed in
/-- `destruct` with `$emb_UOp1` on a handle of a term: a handle of the
operator and one of the index, for a term of a user operator with one
index, and nothing for any other term. -/
theorem Store.destruct_uop1_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fUOp1 t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (op f0 : Term) (u : Eo.UserOp1) (x0 : Eo.Term), x = Eo.Term.UOp1 u x0 ∧
          v.val = [op, f0] ∧ Represents.rep s' f0 x0
      | core.result.Result.Ok none => ∀ u x0, x ≠ Eo.Term.UOp1 u x0
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.destruct_user_holds s _ t rfl h.1 hinv h64)
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  refine ⟨hinv', hg, ?_⟩
  rcases r with (_ | v) | e
  · intro u x0 hx
    subst hx
    exact hr _ [enc_Term x0] (by simp [Embed.embedded_enc_Term, enc_Term]) (uop1_is_user u) _ rfl
      (by simp)
  · obtain ⟨d, op, fields, xs, n, hx, hu, hn, hlen, hv, hl⟩ := hr
    obtain rfl := Result.ok_injective hn
    rw [Embed.embedded_enc_Term] at hx
    have he := h.2
    rcases enc_Term_user_node hx hu with ⟨u, rfl, rfl⟩ | ⟨u, x0, rfl, rfl⟩ |
      ⟨u, x0, x1, rfl, rfl⟩ | ⟨u, x0, x1, x2, rfl, rfl⟩
    all_goals simp at hlen
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0
      exact ⟨op, f0, u, x0, rfl, hv, h0, by simpa [emb_Term] using he⟩
  · trivial

open Embed in
/-- `destruct` with `$emb_UOp2`: as `$emb_UOp1`, for two indices. -/
theorem Store.destruct_uop2_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fUOp2 t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (op f0 f1 : Term) (u : Eo.UserOp2) (x0 x1 : Eo.Term), x = Eo.Term.UOp2 u x0 x1 ∧
          v.val = [op, f0, f1] ∧ Represents.rep s' f0 x0 ∧ Represents.rep s' f1 x1
      | core.result.Result.Ok none => ∀ u x0 x1, x ≠ Eo.Term.UOp2 u x0 x1
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.destruct_user_holds s _ t rfl h.1 hinv h64)
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  refine ⟨hinv', hg, ?_⟩
  rcases r with (_ | v) | e
  · intro u x0 x1 hx
    subst hx
    exact hr _ [enc_Term x0, enc_Term x1] (by simp [Embed.embedded_enc_Term, enc_Term])
      (uop2_is_user u) _ rfl
      (by simp)
  · obtain ⟨d, op, fields, xs, n, hx, hu, hn, hlen, hv, hl⟩ := hr
    obtain rfl := Result.ok_injective hn
    rw [Embed.embedded_enc_Term] at hx
    have he := h.2
    rcases enc_Term_user_node hx hu with ⟨u, rfl, rfl⟩ | ⟨u, x0, rfl, rfl⟩ |
      ⟨u, x0, x1, rfl, rfl⟩ | ⟨u, x0, x1, x2, rfl, rfl⟩
    all_goals simp at hlen
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1
        simp only [embedded_emb_Term, emb_Term] at he
        exact ⟨op, f0, f1, u, x0, x1, rfl, hv, ⟨h0, he.1⟩, ⟨h1, he.2⟩⟩
  · trivial

open Embed in
/-- `destruct` with `$emb_UOp3`: as `$emb_UOp1`, for three indices. -/
theorem Store.destruct_uop3_spec (s : Store) (t : Term) {x : Eo.Term} (h : s.Rep t x)
    (hinv : s.Inv) (h64 : Platform64) :
    Store.destruct s schema.Constructor.eo__24emb_5fUOp3 t ⦃ r s' =>
      s'.Inv ∧ s.Grows s' ∧
      match r with
      | core.result.Result.Ok (some v) =>
        ∃ (op f0 f1 f2 : Term) (u : Eo.UserOp3) (x0 x1 x2 : Eo.Term),
          x = Eo.Term.UOp3 u x0 x1 x2 ∧ v.val = [op, f0, f1, f2] ∧
          Represents.rep s' f0 x0 ∧ Represents.rep s' f1 x1 ∧ Represents.rep s' f2 x2
      | core.result.Result.Ok none => ∀ u x0 x1 x2, x ≠ Eo.Term.UOp3 u x0 x1 x2
      | core.result.Result.Err _ => True ⦄div := by
  apply WP.dspec_mono (Store.destruct_user_holds s _ t rfl h.1 hinv h64)
  rintro ⟨r, s'⟩ ⟨hinv', hg, hr⟩
  refine ⟨hinv', hg, ?_⟩
  rcases r with (_ | v) | e
  · intro u x0 x1 x2 hx
    subst hx
    exact hr _ [enc_Term x0, enc_Term x1, enc_Term x2]
      (by simp [Embed.embedded_enc_Term, enc_Term]) (uop3_is_user u) _ rfl
      (by simp)
  · obtain ⟨d, op, fields, xs, n, hx, hu, hn, hlen, hv, hl⟩ := hr
    obtain rfl := Result.ok_injective hn
    rw [Embed.embedded_enc_Term] at hx
    have he := h.2
    rcases enc_Term_user_node hx hu with ⟨u, rfl, rfl⟩ | ⟨u, x0, rfl, rfl⟩ |
      ⟨u, x0, x1, rfl, rfl⟩ | ⟨u, x0, x1, x2, rfl, rfl⟩
    all_goals simp at hlen
    cases hl with
    | cons f0 _ _ _ h0 hn0 =>
      cases hn0 with
      | cons f1 _ _ _ h1 hn1 =>
        cases hn1 with
        | cons f2 _ _ _ h2 hn2 =>
          cases hn2
          simp only [embedded_emb_Term, emb_Term] at he
          exact ⟨op, f0, f1, f2, u, x0, x1, x2, rfl, hv, ⟨h0, he.1⟩, ⟨h1, he.2.1⟩, ⟨h2, he.2.2⟩⟩
  · trivial

end pathos_compiled_checker
