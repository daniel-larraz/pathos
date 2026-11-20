module
public import MiniChecker
public import CpcMini.Logos
public import CpcMini.SmtTranslate
public import CpcMini.SmtModel
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

/-- `$eo_dd_lookup`. -/
def ProgramSem.p6 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dd_lookup x0 x1)

theorem ProgramSem.p6.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p6 nodes args res) :
    ProgramSem.p6 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_dt_resolve`. -/
def ProgramSem.p10 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dt_resolve x0 x1)

theorem ProgramSem.p10.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p10 nodes args res) :
    ProgramSem.p10 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_dtc_resolve`. -/
def ProgramSem.p13 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dtc_resolve x0 x1)

theorem ProgramSem.p13.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p13 nodes args res) :
    ProgramSem.p13 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_trans`. -/
def ProgramSem.p58 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_trans x0 x1 x2)

theorem ProgramSem.p58.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p58 nodes args res) :
    ProgramSem.p58 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$smtx_dd_has_dt`. -/
def ProgramSem.p59 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dd_has_dt x0 x1)

theorem ProgramSem.p59.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p59 nodes args res) :
    ProgramSem.p59 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dd_lookup`. -/
def ProgramSem.p60 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dd_lookup x0 x1)

theorem ProgramSem.p60.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p60 nodes args res) :
    ProgramSem.p60 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_resolve`. -/
def ProgramSem.p66 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_resolve x0 x1)

theorem ProgramSem.p66.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p66 nodes args res) :
    ProgramSem.p66 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dtc_resolve`. -/
def ProgramSem.p68 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dtc_resolve x0 x1)

theorem ProgramSem.p68.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p68 nodes args res) :
    ProgramSem.p68 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- What an entry of the program `pid` with the arguments `args` and the result
`res` says, in a store whose terms are `nodes`. -/
def ProgramSem (nodes : List TermData) (pid : Nat) (args : List Term) (res : Term) : Prop :=
  (pid = 6 → ProgramSem.p6 nodes args res) ∧
  (pid = 10 → ProgramSem.p10 nodes args res) ∧
  (pid = 13 → ProgramSem.p13 nodes args res) ∧
  (pid = 58 → ProgramSem.p58 nodes args res) ∧
  (pid = 59 → ProgramSem.p59 nodes args res) ∧
  (pid = 60 → ProgramSem.p60 nodes args res) ∧
  (pid = 66 → ProgramSem.p66 nodes args res) ∧
  (pid = 68 → ProgramSem.p68 nodes args res) ∧
  True

theorem ProgramSem.mono {nodes nodes' : List TermData} {pid : Nat} {args : List Term}
    {res : Term} (hpre : nodes <+: nodes') (h : ProgramSem nodes pid args res) :
    ProgramSem nodes' pid args res :=
  ⟨fun e => ProgramSem.p6.mono hpre (h.1 e), fun e => ProgramSem.p10.mono hpre (h.2.1 e), fun e => ProgramSem.p13.mono hpre (h.2.2.1 e), fun e => ProgramSem.p58.mono hpre (h.2.2.2.1 e), fun e => ProgramSem.p59.mono hpre (h.2.2.2.2.1 e), fun e => ProgramSem.p60.mono hpre (h.2.2.2.2.2.1 e), fun e => ProgramSem.p66.mono hpre (h.2.2.2.2.2.2.1 e), fun e => ProgramSem.p68.mono hpre (h.2.2.2.2.2.2.2.1 e), trivial⟩

theorem ProgramSem.of_6 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 6 args res) : ProgramSem.p6 nodes args res :=
  h.1 rfl

theorem ProgramSem.to_6 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p6 nodes args res) : ProgramSem nodes 6 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_10 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 10 args res) : ProgramSem.p10 nodes args res :=
  h.2.1 rfl

theorem ProgramSem.to_10 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p10 nodes args res) : ProgramSem nodes 10 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_13 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 13 args res) : ProgramSem.p13 nodes args res :=
  h.2.2.1 rfl

theorem ProgramSem.to_13 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p13 nodes args res) : ProgramSem nodes 13 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_58 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 58 args res) : ProgramSem.p58 nodes args res :=
  h.2.2.2.1 rfl

theorem ProgramSem.to_58 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p58 nodes args res) : ProgramSem nodes 58 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_59 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 59 args res) : ProgramSem.p59 nodes args res :=
  h.2.2.2.2.1 rfl

theorem ProgramSem.to_59 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p59 nodes args res) : ProgramSem nodes 59 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_60 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 60 args res) : ProgramSem.p60 nodes args res :=
  h.2.2.2.2.2.1 rfl

theorem ProgramSem.to_60 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p60 nodes args res) : ProgramSem nodes 60 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_66 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 66 args res) : ProgramSem.p66 nodes args res :=
  h.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_66 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p66 nodes args res) : ProgramSem nodes 66 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_68 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 68 args res) : ProgramSem.p68 nodes args res :=
  h.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_68 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p68 nodes args res) : ProgramSem nodes 68 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

end pathos_compiled_checker
