module
public import $CHECKER$
public import $CALC$.Logos
public import PathosProofs.Store.Rep

/-!
# What the cache of program results holds

Written by Ethos's rust-meta with the functions: for each program whose results
are cached, that an entry's result is the program's on the entry's arguments.
Do not edit.
-/

@[expose] public section

namespace pathos_compiled_checker

open Aeneas Aeneas.Std Result

/-- `$mk_trans`. -/
def ProgramSem.p58 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ xs : List Eo.Term, RepList nodes args xs ∧
    match xs with
    | [x0, x1, x2] => Rep nodes res.val (Eo.__mk_trans x0 x1 x2)
    | _ => False

theorem ProgramSem.p58.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p58 nodes args res) :
    ProgramSem.p58 nodes' args res := by
  obtain ⟨xs, hl, hr⟩ := h
  refine ⟨xs, RepList.mono hpre hl, ?_⟩
  split at hr
  · exact Rep.mono hpre hr
  · exact hr.elim

/-- What an entry of the program `pid` with the arguments `args` and the result
`res` says, in a store whose terms are `nodes`. -/
def ProgramSem (nodes : List TermData) (pid : Nat) (args : List Term) (res : Term) : Prop :=
  (pid = 58 → ProgramSem.p58 nodes args res) ∧
  True

theorem ProgramSem.mono {nodes nodes' : List TermData} {pid : Nat} {args : List Term}
    {res : Term} (hpre : nodes <+: nodes') (h : ProgramSem nodes pid args res) :
    ProgramSem nodes' pid args res :=
  ⟨fun e => ProgramSem.p58.mono hpre (h.1 e), trivial⟩

theorem ProgramSem.of_58 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 58 args res) : ProgramSem.p58 nodes args res :=
  h.1 rfl

theorem ProgramSem.to_58 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p58 nodes args res) : ProgramSem nodes 58 args res := by
  unfold ProgramSem
  refine ⟨?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

end pathos_compiled_checker
