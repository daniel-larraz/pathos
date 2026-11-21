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

/-- `$eo_is_closed_rec`. -/
def ProgramSem.p21 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_is_closed_rec x0 x1)

theorem ProgramSem.p21.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p21 nodes args res) :
    ProgramSem.p21 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_to_smt`. -/
def ProgramSem.p41 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt x0)

theorem ProgramSem.p41.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p41 nodes args res) :
    ProgramSem.p41 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_datatype`. -/
def ProgramSem.p42 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_datatype x0)

theorem ProgramSem.p42.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p42 nodes args res) :
    ProgramSem.p42 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_datatype_cons`. -/
def ProgramSem.p43 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_datatype_cons x0)

theorem ProgramSem.p43.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p43 nodes args res) :
    ProgramSem.p43 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_datatype_decl`. -/
def ProgramSem.p44 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_datatype_decl x0)

theorem ProgramSem.p44.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p44 nodes args res) :
    ProgramSem.p44 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_type`. -/
def ProgramSem.p46 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_type x0)

theorem ProgramSem.p46.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p46 nodes args res) :
    ProgramSem.p46 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_typeof_dt_cons_rec`. -/
def ProgramSem.p53 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_typeof_dt_cons_rec x0 x1 x2)

theorem ProgramSem.p53.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p53 nodes args res) :
    ProgramSem.p53 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_typeof_dt_sel_return`. -/
def ProgramSem.p54 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_typeof_dt_sel_return x0 x1 x2)

theorem ProgramSem.p54.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p54 nodes args res) :
    ProgramSem.p54 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

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

/-- `$smtx_decl_inhabited`. -/
def ProgramSem.p61 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_decl_inhabited x0 x1)

theorem ProgramSem.p61.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p61 nodes args res) :
    ProgramSem.p61 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_decl_wf_rec`. -/
def ProgramSem.p62 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_decl_wf_rec x0 x1)

theorem ProgramSem.p62.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p62 nodes args res) :
    ProgramSem.p62 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_cons_inhabited`. -/
def ProgramSem.p63 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_cons_inhabited x0 x1)

theorem ProgramSem.p63.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p63 nodes args res) :
    ProgramSem.p63 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_cons_wf_rec`. -/
def ProgramSem.p64 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_cons_wf_rec x0 x1)

theorem ProgramSem.p64.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p64 nodes args res) :
    ProgramSem.p64 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_inhabited`. -/
def ProgramSem.p65 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_inhabited x0 x1)

theorem ProgramSem.p65.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p65 nodes args res) :
    ProgramSem.p65 nodes' args res := by
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

/-- `$smtx_dt_wf_rec`. -/
def ProgramSem.p67 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_wf_rec x0 x1)

theorem ProgramSem.p67.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p67 nodes args res) :
    ProgramSem.p67 nodes' args res := by
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

/-- `$smtx_inhabited_type`. -/
def ProgramSem.p69 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_inhabited_type x0)

theorem ProgramSem.p69.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p69 nodes args res) :
    ProgramSem.p69 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_ret_typeof_sel_rec`. -/
def ProgramSem.p71 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__smtx_ret_typeof_sel_rec x0 x1 x2)

theorem ProgramSem.p71.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p71 nodes args res) :
    ProgramSem.p71 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$smtx_type_wf`. -/
def ProgramSem.p72 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_type_wf x0)

theorem ProgramSem.p72.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p72 nodes args res) :
    ProgramSem.p72 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_type_wf_rec`. -/
def ProgramSem.p74 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_type_wf_rec x0)

theorem ProgramSem.p74.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p74 nodes args res) :
    ProgramSem.p74 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_typeof_dt_cons_rec`. -/
def ProgramSem.p78 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__smtx_typeof_dt_cons_rec x0 x1 x2)

theorem ProgramSem.p78.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p78 nodes args res) :
    ProgramSem.p78 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_typeof`. -/
def ProgramSem.p4294967296 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_typeof x0)

theorem ProgramSem.p4294967296.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p4294967296 nodes args res) :
    ProgramSem.p4294967296 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_typeof`. -/
def ProgramSem.p4294967297 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_typeof x0)

theorem ProgramSem.p4294967297.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p4294967297 nodes args res) :
    ProgramSem.p4294967297 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- What an entry of the program `pid` with the arguments `args` and the result
`res` says, in a store whose terms are `nodes`. -/
def ProgramSem (nodes : List TermData) (pid : Nat) (args : List Term) (res : Term) : Prop :=
  (pid = 6 → ProgramSem.p6 nodes args res) ∧
  (pid = 10 → ProgramSem.p10 nodes args res) ∧
  (pid = 13 → ProgramSem.p13 nodes args res) ∧
  (pid = 21 → ProgramSem.p21 nodes args res) ∧
  (pid = 41 → ProgramSem.p41 nodes args res) ∧
  (pid = 42 → ProgramSem.p42 nodes args res) ∧
  (pid = 43 → ProgramSem.p43 nodes args res) ∧
  (pid = 44 → ProgramSem.p44 nodes args res) ∧
  (pid = 46 → ProgramSem.p46 nodes args res) ∧
  (pid = 53 → ProgramSem.p53 nodes args res) ∧
  (pid = 54 → ProgramSem.p54 nodes args res) ∧
  (pid = 58 → ProgramSem.p58 nodes args res) ∧
  (pid = 59 → ProgramSem.p59 nodes args res) ∧
  (pid = 60 → ProgramSem.p60 nodes args res) ∧
  (pid = 61 → ProgramSem.p61 nodes args res) ∧
  (pid = 62 → ProgramSem.p62 nodes args res) ∧
  (pid = 63 → ProgramSem.p63 nodes args res) ∧
  (pid = 64 → ProgramSem.p64 nodes args res) ∧
  (pid = 65 → ProgramSem.p65 nodes args res) ∧
  (pid = 66 → ProgramSem.p66 nodes args res) ∧
  (pid = 67 → ProgramSem.p67 nodes args res) ∧
  (pid = 68 → ProgramSem.p68 nodes args res) ∧
  (pid = 69 → ProgramSem.p69 nodes args res) ∧
  (pid = 71 → ProgramSem.p71 nodes args res) ∧
  (pid = 72 → ProgramSem.p72 nodes args res) ∧
  (pid = 74 → ProgramSem.p74 nodes args res) ∧
  (pid = 78 → ProgramSem.p78 nodes args res) ∧
  (pid = 4294967296 → ProgramSem.p4294967296 nodes args res) ∧
  (pid = 4294967297 → ProgramSem.p4294967297 nodes args res) ∧
  True

theorem ProgramSem.mono {nodes nodes' : List TermData} {pid : Nat} {args : List Term}
    {res : Term} (hpre : nodes <+: nodes') (h : ProgramSem nodes pid args res) :
    ProgramSem nodes' pid args res :=
  ⟨fun e => ProgramSem.p6.mono hpre (h.1 e), fun e => ProgramSem.p10.mono hpre (h.2.1 e), fun e => ProgramSem.p13.mono hpre (h.2.2.1 e), fun e => ProgramSem.p21.mono hpre (h.2.2.2.1 e), fun e => ProgramSem.p41.mono hpre (h.2.2.2.2.1 e), fun e => ProgramSem.p42.mono hpre (h.2.2.2.2.2.1 e), fun e => ProgramSem.p43.mono hpre (h.2.2.2.2.2.2.1 e), fun e => ProgramSem.p44.mono hpre (h.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p46.mono hpre (h.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p53.mono hpre (h.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p54.mono hpre (h.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p58.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p59.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p60.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p61.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p62.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p63.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p64.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p65.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p66.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p67.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p68.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p69.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p71.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p72.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p74.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p78.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p4294967296.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p4294967297.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), trivial⟩

theorem ProgramSem.of_6 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 6 args res) : ProgramSem.p6 nodes args res :=
  h.1 rfl

theorem ProgramSem.to_6 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p6 nodes args res) : ProgramSem nodes 6 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_10 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 10 args res) : ProgramSem.p10 nodes args res :=
  h.2.1 rfl

theorem ProgramSem.to_10 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p10 nodes args res) : ProgramSem nodes 10 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_13 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 13 args res) : ProgramSem.p13 nodes args res :=
  h.2.2.1 rfl

theorem ProgramSem.to_13 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p13 nodes args res) : ProgramSem nodes 13 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_21 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 21 args res) : ProgramSem.p21 nodes args res :=
  h.2.2.2.1 rfl

theorem ProgramSem.to_21 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p21 nodes args res) : ProgramSem nodes 21 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_41 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 41 args res) : ProgramSem.p41 nodes args res :=
  h.2.2.2.2.1 rfl

theorem ProgramSem.to_41 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p41 nodes args res) : ProgramSem nodes 41 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_42 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 42 args res) : ProgramSem.p42 nodes args res :=
  h.2.2.2.2.2.1 rfl

theorem ProgramSem.to_42 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p42 nodes args res) : ProgramSem nodes 42 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_43 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 43 args res) : ProgramSem.p43 nodes args res :=
  h.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_43 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p43 nodes args res) : ProgramSem nodes 43 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_44 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 44 args res) : ProgramSem.p44 nodes args res :=
  h.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_44 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p44 nodes args res) : ProgramSem nodes 44 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_46 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 46 args res) : ProgramSem.p46 nodes args res :=
  h.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_46 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p46 nodes args res) : ProgramSem nodes 46 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_53 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 53 args res) : ProgramSem.p53 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_53 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p53 nodes args res) : ProgramSem nodes 53 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_54 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 54 args res) : ProgramSem.p54 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_54 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p54 nodes args res) : ProgramSem nodes 54 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_58 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 58 args res) : ProgramSem.p58 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_58 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p58 nodes args res) : ProgramSem nodes 58 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_59 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 59 args res) : ProgramSem.p59 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_59 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p59 nodes args res) : ProgramSem nodes 59 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_60 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 60 args res) : ProgramSem.p60 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_60 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p60 nodes args res) : ProgramSem nodes 60 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_61 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 61 args res) : ProgramSem.p61 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_61 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p61 nodes args res) : ProgramSem nodes 61 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_62 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 62 args res) : ProgramSem.p62 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_62 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p62 nodes args res) : ProgramSem nodes 62 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_63 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 63 args res) : ProgramSem.p63 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_63 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p63 nodes args res) : ProgramSem nodes 63 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_64 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 64 args res) : ProgramSem.p64 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_64 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p64 nodes args res) : ProgramSem nodes 64 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_65 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 65 args res) : ProgramSem.p65 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_65 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p65 nodes args res) : ProgramSem nodes 65 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_66 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 66 args res) : ProgramSem.p66 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_66 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p66 nodes args res) : ProgramSem nodes 66 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_67 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 67 args res) : ProgramSem.p67 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_67 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p67 nodes args res) : ProgramSem nodes 67 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_68 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 68 args res) : ProgramSem.p68 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_68 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p68 nodes args res) : ProgramSem nodes 68 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_69 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 69 args res) : ProgramSem.p69 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_69 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p69 nodes args res) : ProgramSem nodes 69 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_71 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 71 args res) : ProgramSem.p71 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_71 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p71 nodes args res) : ProgramSem nodes 71 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_72 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 72 args res) : ProgramSem.p72 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_72 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p72 nodes args res) : ProgramSem nodes 72 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_74 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 74 args res) : ProgramSem.p74 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_74 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p74 nodes args res) : ProgramSem nodes 74 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_78 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 78 args res) : ProgramSem.p78 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_78 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p78 nodes args res) : ProgramSem nodes 78 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_4294967296 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 4294967296 args res) : ProgramSem.p4294967296 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_4294967296 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p4294967296 nodes args res) : ProgramSem nodes 4294967296 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_4294967297 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 4294967297 args res) : ProgramSem.p4294967297 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_4294967297 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p4294967297 nodes args res) : ProgramSem nodes 4294967297 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

end pathos_compiled_checker
