module
public import $CHECKER$
public import $CALC$.Logos
public import $CALC$.SmtTranslate
public import $CALC$.SmtModel
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
open Eo hiding Term
open Smtm

/-- `$mk_trans`. -/
def ProgramSem.p58 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_trans x0 x1 x2)

theorem ProgramSem.p58.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p58 nodes args res) :
    ProgramSem.p58 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

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
