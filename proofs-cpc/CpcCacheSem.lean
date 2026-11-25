module
public import CpcChecker
public import Cpc.Logos
public import Cpc.SmtTranslate
public import Cpc.SmtModel
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

/-- `$abconv_int_to_bv_elim`. -/
def ProgramSem.p0 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__abconv_int_to_bv_elim x0 x1 x2)

theorem ProgramSem.p0.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p0 nodes args res) :
    ProgramSem.p0 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$abconv_ubv_to_int_elim`. -/
def ProgramSem.p1 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__abconv_ubv_to_int_elim x0 x1 x2)

theorem ProgramSem.p1.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1 nodes args res) :
    ProgramSem.p1 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$assoc_nil_nth`. -/
def ProgramSem.p14 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__assoc_nil_nth x0 x1 x2)

theorem ProgramSem.p14.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p14 nodes args res) :
    ProgramSem.p14 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$assoc_nil_nth_type`. -/
def ProgramSem.p15 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__assoc_nil_nth_type x0 x1 x2)

theorem ProgramSem.p15.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p15 nodes args res) :
    ProgramSem.p15 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$bv_bitblast_apply_binary`. -/
def ProgramSem.p17 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__bv_bitblast_apply_binary x0 x1 x2)

theorem ProgramSem.p17.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p17 nodes args res) :
    ProgramSem.p17 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$bv_bitblast_apply_ite`. -/
def ProgramSem.p18 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__bv_bitblast_apply_ite x0 x1 x2)

theorem ProgramSem.p18.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p18 nodes args res) :
    ProgramSem.p18 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$bv_bitblast_apply_unary`. -/
def ProgramSem.p19 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__bv_bitblast_apply_unary x0 x1)

theorem ProgramSem.p19.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p19 nodes args res) :
    ProgramSem.p19 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$bv_bitblast_concat`. -/
def ProgramSem.p21 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__bv_bitblast_concat x0 x1)

theorem ProgramSem.p21.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p21 nodes args res) :
    ProgramSem.p21 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$bv_bitblast_prefix`. -/
def ProgramSem.p23 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__bv_bitblast_prefix x0 x1)

theorem ProgramSem.p23.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p23 nodes args res) :
    ProgramSem.p23 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$bv_bitblast_subsequence`. -/
def ProgramSem.p25 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__bv_bitblast_subsequence x0 x1 x2)

theorem ProgramSem.p25.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p25 nodes args res) :
    ProgramSem.p25 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$bv_bitblast_ult_rec`. -/
def ProgramSem.p28 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__bv_bitblast_ult_rec x0 x1 x2)

theorem ProgramSem.p28.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p28 nodes args res) :
    ProgramSem.p28 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$bv_get_first_const_child`. -/
def ProgramSem.p33 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__bv_get_first_const_child x0)

theorem ProgramSem.p33.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p33 nodes args res) :
    ProgramSem.p33 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$bv_mk_bitblast_step_add`. -/
def ProgramSem.p35 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__bv_mk_bitblast_step_add x0 x1)

theorem ProgramSem.p35.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p35 nodes args res) :
    ProgramSem.p35 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$bv_mk_bitblast_step_concat`. -/
def ProgramSem.p37 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__bv_mk_bitblast_step_concat x0)

theorem ProgramSem.p37.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p37 nodes args res) :
    ProgramSem.p37 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$bv_mk_bitblast_step_eq_rec`. -/
def ProgramSem.p38 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__bv_mk_bitblast_step_eq_rec x0 x1)

theorem ProgramSem.p38.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p38 nodes args res) :
    ProgramSem.p38 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$bv_mk_bitblast_step_ite`. -/
def ProgramSem.p39 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__bv_mk_bitblast_step_ite x0 x1 x2)

theorem ProgramSem.p39.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p39 nodes args res) :
    ProgramSem.p39 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$bv_mk_bitblast_step_var_rec`. -/
def ProgramSem.p45 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__bv_mk_bitblast_step_var_rec x0 x1)

theorem ProgramSem.p45.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p45 nodes args res) :
    ProgramSem.p45 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$bv_mk_bitwise_slicing_rec`. -/
def ProgramSem.p47 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (a4 : Term) (a5 : Term) (a6 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _) (x4 : _) (x5 : _) (x6 : _), args = [a0, a1, a2, a3, a4, a5, a6] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧ Rep nodes a4.val x4 ∧ Rep nodes a5.val x5 ∧ Rep nodes a6.val x6 ∧
    Rep nodes res.val (__bv_mk_bitwise_slicing_rec x0 x1 x2 x3 x4 x5 x6)

theorem ProgramSem.p47.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p47 nodes args res) :
    ProgramSem.p47 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, x0, x1, x2, x3, x4, x5, x6, hargs, h0, h1, h2, h3, h4, h5, h6, hr⟩ := h
  exact ⟨a0, a1, a2, a3, a4, a5, a6, x0, x1, x2, x3, x4, x5, x6, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre h4, Rep.mono hpre h5, Rep.mono hpre h6, Rep.mono hpre hr⟩

/-- `$bv_ripple_carry_adder_2`. -/
def ProgramSem.p48 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _), args = [a0, a1, a2, a3] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧
    Rep nodes res.val (__bv_ripple_carry_adder_2 x0 x1 x2 x3)

theorem ProgramSem.p48.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p48 nodes args res) :
    ProgramSem.p48 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, h0, h1, h2, h3, hr⟩ := h
  exact ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre hr⟩

/-- `$bv_smulo_elim_rec`. -/
def ProgramSem.p52 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (a4 : Term) (a5 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _) (x4 : _) (x5 : _), args = [a0, a1, a2, a3, a4, a5] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧ Rep nodes a4.val x4 ∧ Rep nodes a5.val x5 ∧
    Rep nodes res.val (__bv_smulo_elim_rec x0 x1 x2 x3 x4 x5)

theorem ProgramSem.p52.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p52 nodes args res) :
    ProgramSem.p52 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, a4, a5, x0, x1, x2, x3, x4, x5, hargs, h0, h1, h2, h3, h4, h5, hr⟩ := h
  exact ⟨a0, a1, a2, a3, a4, a5, x0, x1, x2, x3, x4, x5, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre h4, Rep.mono hpre h5, Rep.mono hpre hr⟩

/-- `$bv_umulo_elim_rec`. -/
def ProgramSem.p53 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (a4 : Term) (a5 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _) (x4 : _) (x5 : _), args = [a0, a1, a2, a3, a4, a5] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧ Rep nodes a4.val x4 ∧ Rep nodes a5.val x5 ∧
    Rep nodes res.val (__bv_umulo_elim_rec x0 x1 x2 x3 x4 x5)

theorem ProgramSem.p53.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p53 nodes args res) :
    ProgramSem.p53 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, a4, a5, x0, x1, x2, x3, x4, x5, hargs, h0, h1, h2, h3, h4, h5, hr⟩ := h
  exact ⟨a0, a1, a2, a3, a4, a5, x0, x1, x2, x3, x4, x5, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre h4, Rep.mono hpre h5, Rep.mono hpre hr⟩

/-- `$chain_m_resolve_rec`. -/
def ProgramSem.p56 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__chain_m_resolve_rec x0 x1 x2)

theorem ProgramSem.p56.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p56 nodes args res) :
    ProgramSem.p56 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$dt_collapse_updater_rhs`. -/
def ProgramSem.p62 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__dt_collapse_updater_rhs x0 x1 x2)

theorem ProgramSem.p62.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p62 nodes args res) :
    ProgramSem.p62 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_dd_lookup`. -/
def ProgramSem.p76 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dd_lookup x0 x1)

theorem ProgramSem.p76.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p76 nodes args res) :
    ProgramSem.p76 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_dt_resolve`. -/
def ProgramSem.p82 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dt_resolve x0 x1)

theorem ProgramSem.p82.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p82 nodes args res) :
    ProgramSem.p82 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_dtc_resolve`. -/
def ProgramSem.p85 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dtc_resolve x0 x1)

theorem ProgramSem.p85.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p85 nodes args res) :
    ProgramSem.p85 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_to_smt_datatype`. -/
def ProgramSem.p749 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_datatype x0)

theorem ProgramSem.p749.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p749 nodes args res) :
    ProgramSem.p749 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_datatype_cons`. -/
def ProgramSem.p750 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_datatype_cons x0)

theorem ProgramSem.p750.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p750 nodes args res) :
    ProgramSem.p750 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_datatype_decl`. -/
def ProgramSem.p751 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_datatype_decl x0)

theorem ProgramSem.p751.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p751 nodes args res) :
    ProgramSem.p751 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_exists`. -/
def ProgramSem.p754 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_to_smt_exists x0 x1)

theorem ProgramSem.p754.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p754 nodes args res) :
    ProgramSem.p754 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_to_smt_lambda_curry`. -/
def ProgramSem.p755 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_to_smt_lambda_curry x0 x1)

theorem ProgramSem.p755.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p755 nodes args res) :
    ProgramSem.p755 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_to_smt_quantifiers_skolemize`. -/
def ProgramSem.p758 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_to_smt_quantifiers_skolemize x0 x1 x2)

theorem ProgramSem.p758.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p758 nodes args res) :
    ProgramSem.p758 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_to_smt_re_unfold_pos_component`. -/
def ProgramSem.p759 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_to_smt_re_unfold_pos_component x0 x1 x2)

theorem ProgramSem.p759.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p759 nodes args res) :
    ProgramSem.p759 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_to_smt_tuple_prepend_rec`. -/
def ProgramSem.p769 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (a4 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _) (x4 : _), args = [a0, a1, a2, a3, a4] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧ Rep nodes a4.val x4 ∧
    Rep nodes res.val (__eo_to_smt_tuple_prepend_rec x0 x1 x2 x3 x4)

theorem ProgramSem.p769.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p769 nodes args res) :
    ProgramSem.p769 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, a4, x0, x1, x2, x3, x4, hargs, h0, h1, h2, h3, h4, hr⟩ := h
  exact ⟨a0, a1, a2, a3, a4, x0, x1, x2, x3, x4, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre h4, Rep.mono hpre hr⟩

/-- `$eo_to_smt_type`. -/
def ProgramSem.p772 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_to_smt_type x0)

theorem ProgramSem.p772.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p772 nodes args res) :
    ProgramSem.p772 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$eo_to_smt_updater_rec`. -/
def ProgramSem.p776 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (a4 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _) (x4 : _), args = [a0, a1, a2, a3, a4] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧ Rep nodes a4.val x4 ∧
    Rep nodes res.val (__eo_to_smt_updater_rec x0 x1 x2 x3 x4)

theorem ProgramSem.p776.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p776 nodes args res) :
    ProgramSem.p776 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, a4, x0, x1, x2, x3, x4, hargs, h0, h1, h2, h3, h4, hr⟩ := h
  exact ⟨a0, a1, a2, a3, a4, x0, x1, x2, x3, x4, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre h4, Rep.mono hpre hr⟩

/-- `$eo_typeof_@quantifiers_skolemize`. -/
def ProgramSem.p796 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _), args = [a0, a1, a2, a3] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧
    Rep nodes res.val (__eo_typeof__at_quantifiers_skolemize x0 x1 x2 x3)

theorem ProgramSem.p796.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p796 nodes args res) :
    ProgramSem.p796 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, h0, h1, h2, h3, hr⟩ := h
  exact ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre hr⟩

/-- `$eo_typeof_dt_cons_rec`. -/
def ProgramSem.p820 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_typeof_dt_cons_rec x0 x1 x2)

theorem ProgramSem.p820.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p820 nodes args res) :
    ProgramSem.p820 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_typeof_dt_sel_return`. -/
def ProgramSem.p821 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_typeof_dt_sel_return x0 x1 x2)

theorem ProgramSem.p821.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p821 nodes args res) :
    ProgramSem.p821 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_typeof_tuple`. -/
def ProgramSem.p874 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_typeof_tuple x0 x1)

theorem ProgramSem.p874.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p874 nodes args res) :
    ProgramSem.p874 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_typeof_tuple.select`. -/
def ProgramSem.p875 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__eo_typeof_tuple_select x0 x1 x2)

theorem ProgramSem.p875.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p875 nodes args res) :
    ProgramSem.p875 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_typeof_tuple.update`. -/
def ProgramSem.p876 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _), args = [a0, a1, a2, a3] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧
    Rep nodes res.val (__eo_typeof_tuple_update x0 x1 x2 x3)

theorem ProgramSem.p876.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p876 nodes args res) :
    ProgramSem.p876 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, h0, h1, h2, h3, hr⟩ := h
  exact ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre hr⟩

/-- `$extract_antec_rec`. -/
def ProgramSem.p883 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__extract_antec_rec x0 x1)

theorem ProgramSem.p883.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p883 nodes args res) :
    ProgramSem.p883 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$get_arg_list_rec`. -/
def ProgramSem.p890 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__get_arg_list_rec x0 x1)

theorem ProgramSem.p890.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p890 nodes args res) :
    ProgramSem.p890 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$get_lambda_type`. -/
def ProgramSem.p893 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__get_lambda_type x0 x1)

theorem ProgramSem.p893.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p893 nodes args res) :
    ProgramSem.p893 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$get_nth_var_type`. -/
def ProgramSem.p894 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__get_nth_var_type x0 x1)

theorem ProgramSem.p894.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p894 nodes args res) :
    ProgramSem.p894 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$iota_rec`. -/
def ProgramSem.p899 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__iota_rec x0 x1)

theorem ProgramSem.p899.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p899 nodes args res) :
    ProgramSem.p899 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$is_instantiation`. -/
def ProgramSem.p906 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__is_instantiation x0 x1)

theorem ProgramSem.p906.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p906 nodes args res) :
    ProgramSem.p906 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$is_seq_const_rec`. -/
def ProgramSem.p914 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__is_seq_const_rec x0)

theorem ProgramSem.p914.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p914 nodes args res) :
    ProgramSem.p914 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$lower_not_and`. -/
def ProgramSem.p917 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__lower_not_and x0)

theorem ProgramSem.p917.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p917 nodes args res) :
    ProgramSem.p917 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$mk_arith_sum_ub_rec`. -/
def ProgramSem.p924 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_arith_sum_ub_rec x0 x1)

theorem ProgramSem.p924.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p924 nodes args res) :
    ProgramSem.p924 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_cong_rhs`. -/
def ProgramSem.p926 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_cong_rhs x0 x1)

theorem ProgramSem.p926.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p926 nodes args res) :
    ProgramSem.p926 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_distinct_elim`. -/
def ProgramSem.p927 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__mk_distinct_elim x0)

theorem ProgramSem.p927.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p927 nodes args res) :
    ProgramSem.p927 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$mk_distinct_elim_rec`. -/
def ProgramSem.p928 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_distinct_elim_rec x0 x1 x2)

theorem ProgramSem.p928.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p928 nodes args res) :
    ProgramSem.p928 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_dt_inst_rec`. -/
def ProgramSem.p933 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_dt_inst_rec x0 x1 x2)

theorem ProgramSem.p933.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p933 nodes args res) :
    ProgramSem.p933 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_dt_inst_tuple_rec`. -/
def ProgramSem.p935 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_dt_inst_tuple_rec x0 x1 x2)

theorem ProgramSem.p935.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p935 nodes args res) :
    ProgramSem.p935 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_dt_split`. -/
def ProgramSem.p936 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_dt_split x0 x1)

theorem ProgramSem.p936.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p936 nodes args res) :
    ProgramSem.p936 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_ho_cong`. -/
def ProgramSem.p939 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_ho_cong x0 x1 x2)

theorem ProgramSem.p939.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p939 nodes args res) :
    ProgramSem.p939 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_nary_cong_rhs`. -/
def ProgramSem.p940 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_nary_cong_rhs x0 x1)

theorem ProgramSem.p940.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p940 nodes args res) :
    ProgramSem.p940 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_quant_merge_prenex`. -/
def ProgramSem.p941 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_quant_merge_prenex x0 x1 x2)

theorem ProgramSem.p941.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p941 nodes args res) :
    ProgramSem.p941 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_quant_miniscope_and`. -/
def ProgramSem.p942 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_quant_miniscope_and x0 x1)

theorem ProgramSem.p942.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p942 nodes args res) :
    ProgramSem.p942 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_re_concat`. -/
def ProgramSem.p944 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_re_concat x0 x1)

theorem ProgramSem.p944.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p944 nodes args res) :
    ProgramSem.p944 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_skolems`. -/
def ProgramSem.p949 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_skolems x0 x1 x2)

theorem ProgramSem.p949.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p949 nodes args res) :
    ProgramSem.p949 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_trans`. -/
def ProgramSem.p952 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_trans x0 x1 x2)

theorem ProgramSem.p952.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p952 nodes args res) :
    ProgramSem.p952 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$poly_mod_coeffs`. -/
def ProgramSem.p958 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__poly_mod_coeffs x0 x1)

theorem ProgramSem.p958.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p958 nodes args res) :
    ProgramSem.p958 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$poly_neg`. -/
def ProgramSem.p961 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__poly_neg x0)

theorem ProgramSem.p961.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p961 nodes args res) :
    ProgramSem.p961 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$re_is_unbound_wildcard`. -/
def ProgramSem.p965 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__re_is_unbound_wildcard x0)

theorem ProgramSem.p965.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p965 nodes args res) :
    ProgramSem.p965 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$re_nullable`. -/
def ProgramSem.p966 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__re_nullable x0)

theorem ProgramSem.p966.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p966 nodes args res) :
    ProgramSem.p966 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$re_rev_comp`. -/
def ProgramSem.p967 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__re_rev_comp x0)

theorem ProgramSem.p967.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p967 nodes args res) :
    ProgramSem.p967 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$re_rev_map_rev`. -/
def ProgramSem.p968 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__re_rev_map_rev x0 x1)

theorem ProgramSem.p968.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p968 nodes args res) :
    ProgramSem.p968 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$re_split_str_to_re`. -/
def ProgramSem.p969 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__re_split_str_to_re x0 x1)

theorem ProgramSem.p969.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p969 nodes args res) :
    ProgramSem.p969 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$re_unfold_pos_concat_rec`. -/
def ProgramSem.p972 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _), args = [a0, a1, a2, a3] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧
    Rep nodes res.val (__re_unfold_pos_concat_rec x0 x1 x2 x3)

theorem ProgramSem.p972.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p972 nodes args res) :
    ProgramSem.p972 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, h0, h1, h2, h3, hr⟩ := h
  exact ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre hr⟩

/-- `$seq_subsequence_rec`. -/
def ProgramSem.p983 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__seq_subsequence_rec x0 x1 x2)

theorem ProgramSem.p983.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p983 nodes args res) :
    ProgramSem.p983 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$set_union_to_list`. -/
def ProgramSem.p985 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__set_union_to_list x0)

theorem ProgramSem.p985.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p985 nodes args res) :
    ProgramSem.p985 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_dd_has_dt`. -/
def ProgramSem.p986 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dd_has_dt x0 x1)

theorem ProgramSem.p986.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p986 nodes args res) :
    ProgramSem.p986 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dd_lookup`. -/
def ProgramSem.p987 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dd_lookup x0 x1)

theorem ProgramSem.p987.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p987 nodes args res) :
    ProgramSem.p987 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_decl_inhabited`. -/
def ProgramSem.p988 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_decl_inhabited x0 x1)

theorem ProgramSem.p988.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p988 nodes args res) :
    ProgramSem.p988 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_decl_wf_rec`. -/
def ProgramSem.p989 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_decl_wf_rec x0 x1)

theorem ProgramSem.p989.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p989 nodes args res) :
    ProgramSem.p989 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_cons_inhabited`. -/
def ProgramSem.p990 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_cons_inhabited x0 x1)

theorem ProgramSem.p990.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p990 nodes args res) :
    ProgramSem.p990 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_cons_wf_rec`. -/
def ProgramSem.p991 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_cons_wf_rec x0 x1)

theorem ProgramSem.p991.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p991 nodes args res) :
    ProgramSem.p991 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_inhabited`. -/
def ProgramSem.p992 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_inhabited x0 x1)

theorem ProgramSem.p992.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p992 nodes args res) :
    ProgramSem.p992 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_resolve`. -/
def ProgramSem.p994 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_resolve x0 x1)

theorem ProgramSem.p994.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p994 nodes args res) :
    ProgramSem.p994 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_wf_rec`. -/
def ProgramSem.p995 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_wf_rec x0 x1)

theorem ProgramSem.p995.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p995 nodes args res) :
    ProgramSem.p995 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dtc_num_sels`. -/
def ProgramSem.p996 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_dtc_num_sels x0)

theorem ProgramSem.p996.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p996 nodes args res) :
    ProgramSem.p996 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_dtc_resolve`. -/
def ProgramSem.p997 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dtc_resolve x0 x1)

theorem ProgramSem.p997.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p997 nodes args res) :
    ProgramSem.p997 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_inhabited_type`. -/
def ProgramSem.p998 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_inhabited_type x0)

theorem ProgramSem.p998.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p998 nodes args res) :
    ProgramSem.p998 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_ret_typeof_sel_rec`. -/
def ProgramSem.p1000 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__smtx_ret_typeof_sel_rec x0 x1 x2)

theorem ProgramSem.p1000.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1000 nodes args res) :
    ProgramSem.p1000 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$smtx_type_wf`. -/
def ProgramSem.p1001 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_type_wf x0)

theorem ProgramSem.p1001.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1001 nodes args res) :
    ProgramSem.p1001 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_type_wf_rec`. -/
def ProgramSem.p1003 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_type_wf_rec x0)

theorem ProgramSem.p1003.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1003 nodes args res) :
    ProgramSem.p1003 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_typeof_dt_cons_rec`. -/
def ProgramSem.p1016 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__smtx_typeof_dt_cons_rec x0 x1 x2)

theorem ProgramSem.p1016.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1016 nodes args res) :
    ProgramSem.p1016 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$str_arith_entail_simple_rec`. -/
def ProgramSem.p1049 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__str_arith_entail_simple_rec x0)

theorem ProgramSem.p1049.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1049 nodes args res) :
    ProgramSem.p1049 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$str_fixed_len_re`. -/
def ProgramSem.p1059 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__str_fixed_len_re x0)

theorem ProgramSem.p1059.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1059 nodes args res) :
    ProgramSem.p1059 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$str_is_prefix_flat`. -/
def ProgramSem.p1067 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__str_is_prefix_flat x0 x1)

theorem ProgramSem.p1067.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1067 nodes args res) :
    ProgramSem.p1067 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$str_leq_eval_rec`. -/
def ProgramSem.p1068 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__str_leq_eval_rec x0 x1)

theorem ProgramSem.p1068.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1068 nodes args res) :
    ProgramSem.p1068 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$str_mk_re_loop_elim_rec`. -/
def ProgramSem.p1072 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__str_mk_re_loop_elim_rec x0 x1 x2)

theorem ProgramSem.p1072.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1072 nodes args res) :
    ProgramSem.p1072 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$str_mk_str_in_re_concat_star_char`. -/
def ProgramSem.p1073 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__str_mk_str_in_re_concat_star_char x0 x1)

theorem ProgramSem.p1073.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1073 nodes args res) :
    ProgramSem.p1073 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$str_mk_str_in_re_sigma_rec`. -/
def ProgramSem.p1074 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (a3 : Term) (x0 : _) (x1 : _) (x2 : _) (x3 : _), args = [a0, a1, a2, a3] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧ Rep nodes a3.val x3 ∧
    Rep nodes res.val (__str_mk_str_in_re_sigma_rec x0 x1 x2 x3)

theorem ProgramSem.p1074.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1074 nodes args res) :
    ProgramSem.p1074 nodes' args res := by
  obtain ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, h0, h1, h2, h3, hr⟩ := h
  exact ⟨a0, a1, a2, a3, x0, x1, x2, x3, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre h3, Rep.mono hpre hr⟩

/-- `$str_mk_str_in_re_sigma_star_rec`. -/
def ProgramSem.p1075 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__str_mk_str_in_re_sigma_star_rec x0 x1 x2)

theorem ProgramSem.p1075.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1075 nodes args res) :
    ProgramSem.p1075 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$str_multiset_overapprox_word`. -/
def ProgramSem.p1077 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__str_multiset_overapprox_word x0)

theorem ProgramSem.p1077.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1077 nodes args res) :
    ProgramSem.p1077 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$str_strip_prefix`. -/
def ProgramSem.p1090 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__str_strip_prefix x0 x1)

theorem ProgramSem.p1090.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1090 nodes args res) :
    ProgramSem.p1090 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$str_to_int_eval_rec`. -/
def ProgramSem.p1091 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__str_to_int_eval_rec x0 x1 x2)

theorem ProgramSem.p1091.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1091 nodes args res) :
    ProgramSem.p1091 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$strip_even_exponent`. -/
def ProgramSem.p1094 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__strip_even_exponent x0 x1)

theorem ProgramSem.p1094.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1094 nodes args res) :
    ProgramSem.p1094 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$tuple_arg_list`. -/
def ProgramSem.p1098 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__tuple_arg_list x0)

theorem ProgramSem.p1098.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1098 nodes args res) :
    ProgramSem.p1098 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$tuple_collapse_updater_rhs`. -/
def ProgramSem.p1099 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__tuple_collapse_updater_rhs x0 x1 x2)

theorem ProgramSem.p1099.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1099 nodes args res) :
    ProgramSem.p1099 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$tuple_get_selectors_rec`. -/
def ProgramSem.p1100 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__tuple_get_selectors_rec x0 x1)

theorem ProgramSem.p1100.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1100 nodes args res) :
    ProgramSem.p1100 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_typeof`. -/
def ProgramSem.p4294967296 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__eo_typeof x0)

theorem ProgramSem.p4294967296.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p4294967296 nodes args res) :
    ProgramSem.p4294967296 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- What an entry of the program `pid` with the arguments `args` and the result
`res` says, in a store whose terms are `nodes`. -/
def ProgramSem (nodes : List TermData) (pid : Nat) (args : List Term) (res : Term) : Prop :=
  (pid = 0 → ProgramSem.p0 nodes args res) ∧
  (pid = 1 → ProgramSem.p1 nodes args res) ∧
  (pid = 14 → ProgramSem.p14 nodes args res) ∧
  (pid = 15 → ProgramSem.p15 nodes args res) ∧
  (pid = 17 → ProgramSem.p17 nodes args res) ∧
  (pid = 18 → ProgramSem.p18 nodes args res) ∧
  (pid = 19 → ProgramSem.p19 nodes args res) ∧
  (pid = 21 → ProgramSem.p21 nodes args res) ∧
  (pid = 23 → ProgramSem.p23 nodes args res) ∧
  (pid = 25 → ProgramSem.p25 nodes args res) ∧
  (pid = 28 → ProgramSem.p28 nodes args res) ∧
  (pid = 33 → ProgramSem.p33 nodes args res) ∧
  (pid = 35 → ProgramSem.p35 nodes args res) ∧
  (pid = 37 → ProgramSem.p37 nodes args res) ∧
  (pid = 38 → ProgramSem.p38 nodes args res) ∧
  (pid = 39 → ProgramSem.p39 nodes args res) ∧
  (pid = 45 → ProgramSem.p45 nodes args res) ∧
  (pid = 47 → ProgramSem.p47 nodes args res) ∧
  (pid = 48 → ProgramSem.p48 nodes args res) ∧
  (pid = 52 → ProgramSem.p52 nodes args res) ∧
  (pid = 53 → ProgramSem.p53 nodes args res) ∧
  (pid = 56 → ProgramSem.p56 nodes args res) ∧
  (pid = 62 → ProgramSem.p62 nodes args res) ∧
  (pid = 76 → ProgramSem.p76 nodes args res) ∧
  (pid = 82 → ProgramSem.p82 nodes args res) ∧
  (pid = 85 → ProgramSem.p85 nodes args res) ∧
  (pid = 749 → ProgramSem.p749 nodes args res) ∧
  (pid = 750 → ProgramSem.p750 nodes args res) ∧
  (pid = 751 → ProgramSem.p751 nodes args res) ∧
  (pid = 754 → ProgramSem.p754 nodes args res) ∧
  (pid = 755 → ProgramSem.p755 nodes args res) ∧
  (pid = 758 → ProgramSem.p758 nodes args res) ∧
  (pid = 759 → ProgramSem.p759 nodes args res) ∧
  (pid = 769 → ProgramSem.p769 nodes args res) ∧
  (pid = 772 → ProgramSem.p772 nodes args res) ∧
  (pid = 776 → ProgramSem.p776 nodes args res) ∧
  (pid = 796 → ProgramSem.p796 nodes args res) ∧
  (pid = 820 → ProgramSem.p820 nodes args res) ∧
  (pid = 821 → ProgramSem.p821 nodes args res) ∧
  (pid = 874 → ProgramSem.p874 nodes args res) ∧
  (pid = 875 → ProgramSem.p875 nodes args res) ∧
  (pid = 876 → ProgramSem.p876 nodes args res) ∧
  (pid = 883 → ProgramSem.p883 nodes args res) ∧
  (pid = 890 → ProgramSem.p890 nodes args res) ∧
  (pid = 893 → ProgramSem.p893 nodes args res) ∧
  (pid = 894 → ProgramSem.p894 nodes args res) ∧
  (pid = 899 → ProgramSem.p899 nodes args res) ∧
  (pid = 906 → ProgramSem.p906 nodes args res) ∧
  (pid = 914 → ProgramSem.p914 nodes args res) ∧
  (pid = 917 → ProgramSem.p917 nodes args res) ∧
  (pid = 924 → ProgramSem.p924 nodes args res) ∧
  (pid = 926 → ProgramSem.p926 nodes args res) ∧
  (pid = 927 → ProgramSem.p927 nodes args res) ∧
  (pid = 928 → ProgramSem.p928 nodes args res) ∧
  (pid = 933 → ProgramSem.p933 nodes args res) ∧
  (pid = 935 → ProgramSem.p935 nodes args res) ∧
  (pid = 936 → ProgramSem.p936 nodes args res) ∧
  (pid = 939 → ProgramSem.p939 nodes args res) ∧
  (pid = 940 → ProgramSem.p940 nodes args res) ∧
  (pid = 941 → ProgramSem.p941 nodes args res) ∧
  (pid = 942 → ProgramSem.p942 nodes args res) ∧
  (pid = 944 → ProgramSem.p944 nodes args res) ∧
  (pid = 949 → ProgramSem.p949 nodes args res) ∧
  (pid = 952 → ProgramSem.p952 nodes args res) ∧
  (pid = 958 → ProgramSem.p958 nodes args res) ∧
  (pid = 961 → ProgramSem.p961 nodes args res) ∧
  (pid = 965 → ProgramSem.p965 nodes args res) ∧
  (pid = 966 → ProgramSem.p966 nodes args res) ∧
  (pid = 967 → ProgramSem.p967 nodes args res) ∧
  (pid = 968 → ProgramSem.p968 nodes args res) ∧
  (pid = 969 → ProgramSem.p969 nodes args res) ∧
  (pid = 972 → ProgramSem.p972 nodes args res) ∧
  (pid = 983 → ProgramSem.p983 nodes args res) ∧
  (pid = 985 → ProgramSem.p985 nodes args res) ∧
  (pid = 986 → ProgramSem.p986 nodes args res) ∧
  (pid = 987 → ProgramSem.p987 nodes args res) ∧
  (pid = 988 → ProgramSem.p988 nodes args res) ∧
  (pid = 989 → ProgramSem.p989 nodes args res) ∧
  (pid = 990 → ProgramSem.p990 nodes args res) ∧
  (pid = 991 → ProgramSem.p991 nodes args res) ∧
  (pid = 992 → ProgramSem.p992 nodes args res) ∧
  (pid = 994 → ProgramSem.p994 nodes args res) ∧
  (pid = 995 → ProgramSem.p995 nodes args res) ∧
  (pid = 996 → ProgramSem.p996 nodes args res) ∧
  (pid = 997 → ProgramSem.p997 nodes args res) ∧
  (pid = 998 → ProgramSem.p998 nodes args res) ∧
  (pid = 1000 → ProgramSem.p1000 nodes args res) ∧
  (pid = 1001 → ProgramSem.p1001 nodes args res) ∧
  (pid = 1003 → ProgramSem.p1003 nodes args res) ∧
  (pid = 1016 → ProgramSem.p1016 nodes args res) ∧
  (pid = 1049 → ProgramSem.p1049 nodes args res) ∧
  (pid = 1059 → ProgramSem.p1059 nodes args res) ∧
  (pid = 1067 → ProgramSem.p1067 nodes args res) ∧
  (pid = 1068 → ProgramSem.p1068 nodes args res) ∧
  (pid = 1072 → ProgramSem.p1072 nodes args res) ∧
  (pid = 1073 → ProgramSem.p1073 nodes args res) ∧
  (pid = 1074 → ProgramSem.p1074 nodes args res) ∧
  (pid = 1075 → ProgramSem.p1075 nodes args res) ∧
  (pid = 1077 → ProgramSem.p1077 nodes args res) ∧
  (pid = 1090 → ProgramSem.p1090 nodes args res) ∧
  (pid = 1091 → ProgramSem.p1091 nodes args res) ∧
  (pid = 1094 → ProgramSem.p1094 nodes args res) ∧
  (pid = 1098 → ProgramSem.p1098 nodes args res) ∧
  (pid = 1099 → ProgramSem.p1099 nodes args res) ∧
  (pid = 1100 → ProgramSem.p1100 nodes args res) ∧
  (pid = 4294967296 → ProgramSem.p4294967296 nodes args res) ∧
  True

theorem ProgramSem.mono {nodes nodes' : List TermData} {pid : Nat} {args : List Term}
    {res : Term} (hpre : nodes <+: nodes') (h : ProgramSem nodes pid args res) :
    ProgramSem nodes' pid args res :=
  ⟨fun e => ProgramSem.p0.mono hpre (h.1 e), fun e => ProgramSem.p1.mono hpre (h.2.1 e), fun e => ProgramSem.p14.mono hpre (h.2.2.1 e), fun e => ProgramSem.p15.mono hpre (h.2.2.2.1 e), fun e => ProgramSem.p17.mono hpre (h.2.2.2.2.1 e), fun e => ProgramSem.p18.mono hpre (h.2.2.2.2.2.1 e), fun e => ProgramSem.p19.mono hpre (h.2.2.2.2.2.2.1 e), fun e => ProgramSem.p21.mono hpre (h.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p23.mono hpre (h.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p25.mono hpre (h.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p28.mono hpre (h.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p33.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p35.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p37.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p38.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p39.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p45.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p47.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p48.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p52.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p53.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p56.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p62.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p76.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p82.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p85.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p749.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p750.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p751.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p754.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p755.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p758.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p759.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p769.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p772.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p776.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p796.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p820.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p821.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p874.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p875.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p876.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p883.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p890.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p893.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p894.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p899.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p906.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p914.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p917.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p924.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p926.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p927.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p928.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p933.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p935.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p936.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p939.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p940.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p941.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p942.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p944.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p949.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p952.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p958.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p961.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p965.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p966.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p967.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p968.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p969.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p972.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p983.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p985.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p986.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p987.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p988.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p989.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p990.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p991.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p992.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p994.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p995.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p996.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p997.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p998.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1000.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1001.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1003.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1016.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1049.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1059.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1067.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1068.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1072.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1073.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1074.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1075.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1077.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1090.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1091.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1094.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1098.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1099.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1100.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p4294967296.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), trivial⟩

theorem ProgramSem.of_0 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 0 args res) : ProgramSem.p0 nodes args res :=
  h.1 rfl

theorem ProgramSem.to_0 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p0 nodes args res) : ProgramSem nodes 0 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1 args res) : ProgramSem.p1 nodes args res :=
  h.2.1 rfl

theorem ProgramSem.to_1 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1 nodes args res) : ProgramSem nodes 1 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_14 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 14 args res) : ProgramSem.p14 nodes args res :=
  h.2.2.1 rfl

theorem ProgramSem.to_14 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p14 nodes args res) : ProgramSem nodes 14 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_15 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 15 args res) : ProgramSem.p15 nodes args res :=
  h.2.2.2.1 rfl

theorem ProgramSem.to_15 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p15 nodes args res) : ProgramSem nodes 15 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_17 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 17 args res) : ProgramSem.p17 nodes args res :=
  h.2.2.2.2.1 rfl

theorem ProgramSem.to_17 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p17 nodes args res) : ProgramSem nodes 17 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_18 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 18 args res) : ProgramSem.p18 nodes args res :=
  h.2.2.2.2.2.1 rfl

theorem ProgramSem.to_18 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p18 nodes args res) : ProgramSem nodes 18 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_19 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 19 args res) : ProgramSem.p19 nodes args res :=
  h.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_19 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p19 nodes args res) : ProgramSem nodes 19 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_21 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 21 args res) : ProgramSem.p21 nodes args res :=
  h.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_21 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p21 nodes args res) : ProgramSem nodes 21 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_23 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 23 args res) : ProgramSem.p23 nodes args res :=
  h.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_23 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p23 nodes args res) : ProgramSem nodes 23 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_25 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 25 args res) : ProgramSem.p25 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_25 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p25 nodes args res) : ProgramSem nodes 25 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_28 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 28 args res) : ProgramSem.p28 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_28 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p28 nodes args res) : ProgramSem nodes 28 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_33 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 33 args res) : ProgramSem.p33 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_33 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p33 nodes args res) : ProgramSem nodes 33 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_35 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 35 args res) : ProgramSem.p35 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_35 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p35 nodes args res) : ProgramSem nodes 35 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_37 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 37 args res) : ProgramSem.p37 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_37 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p37 nodes args res) : ProgramSem nodes 37 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_38 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 38 args res) : ProgramSem.p38 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_38 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p38 nodes args res) : ProgramSem nodes 38 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_39 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 39 args res) : ProgramSem.p39 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_39 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p39 nodes args res) : ProgramSem nodes 39 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_45 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 45 args res) : ProgramSem.p45 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_45 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p45 nodes args res) : ProgramSem nodes 45 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_47 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 47 args res) : ProgramSem.p47 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_47 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p47 nodes args res) : ProgramSem nodes 47 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_48 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 48 args res) : ProgramSem.p48 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_48 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p48 nodes args res) : ProgramSem nodes 48 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_52 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 52 args res) : ProgramSem.p52 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_52 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p52 nodes args res) : ProgramSem nodes 52 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_53 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 53 args res) : ProgramSem.p53 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_53 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p53 nodes args res) : ProgramSem nodes 53 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_56 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 56 args res) : ProgramSem.p56 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_56 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p56 nodes args res) : ProgramSem nodes 56 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_62 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 62 args res) : ProgramSem.p62 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_62 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p62 nodes args res) : ProgramSem nodes 62 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_76 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 76 args res) : ProgramSem.p76 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_76 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p76 nodes args res) : ProgramSem nodes 76 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_82 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 82 args res) : ProgramSem.p82 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_82 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p82 nodes args res) : ProgramSem nodes 82 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_85 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 85 args res) : ProgramSem.p85 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_85 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p85 nodes args res) : ProgramSem nodes 85 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_749 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 749 args res) : ProgramSem.p749 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_749 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p749 nodes args res) : ProgramSem nodes 749 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_750 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 750 args res) : ProgramSem.p750 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_750 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p750 nodes args res) : ProgramSem nodes 750 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_751 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 751 args res) : ProgramSem.p751 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_751 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p751 nodes args res) : ProgramSem nodes 751 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_754 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 754 args res) : ProgramSem.p754 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_754 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p754 nodes args res) : ProgramSem nodes 754 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_755 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 755 args res) : ProgramSem.p755 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_755 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p755 nodes args res) : ProgramSem nodes 755 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_758 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 758 args res) : ProgramSem.p758 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_758 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p758 nodes args res) : ProgramSem nodes 758 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_759 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 759 args res) : ProgramSem.p759 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_759 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p759 nodes args res) : ProgramSem nodes 759 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_769 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 769 args res) : ProgramSem.p769 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_769 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p769 nodes args res) : ProgramSem nodes 769 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_772 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 772 args res) : ProgramSem.p772 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_772 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p772 nodes args res) : ProgramSem nodes 772 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_776 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 776 args res) : ProgramSem.p776 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_776 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p776 nodes args res) : ProgramSem nodes 776 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_796 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 796 args res) : ProgramSem.p796 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_796 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p796 nodes args res) : ProgramSem nodes 796 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_820 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 820 args res) : ProgramSem.p820 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_820 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p820 nodes args res) : ProgramSem nodes 820 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_821 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 821 args res) : ProgramSem.p821 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_821 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p821 nodes args res) : ProgramSem nodes 821 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_874 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 874 args res) : ProgramSem.p874 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_874 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p874 nodes args res) : ProgramSem nodes 874 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_875 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 875 args res) : ProgramSem.p875 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_875 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p875 nodes args res) : ProgramSem nodes 875 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_876 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 876 args res) : ProgramSem.p876 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_876 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p876 nodes args res) : ProgramSem nodes 876 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_883 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 883 args res) : ProgramSem.p883 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_883 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p883 nodes args res) : ProgramSem nodes 883 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_890 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 890 args res) : ProgramSem.p890 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_890 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p890 nodes args res) : ProgramSem nodes 890 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_893 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 893 args res) : ProgramSem.p893 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_893 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p893 nodes args res) : ProgramSem nodes 893 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_894 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 894 args res) : ProgramSem.p894 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_894 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p894 nodes args res) : ProgramSem nodes 894 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_899 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 899 args res) : ProgramSem.p899 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_899 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p899 nodes args res) : ProgramSem nodes 899 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_906 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 906 args res) : ProgramSem.p906 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_906 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p906 nodes args res) : ProgramSem nodes 906 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_914 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 914 args res) : ProgramSem.p914 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_914 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p914 nodes args res) : ProgramSem nodes 914 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_917 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 917 args res) : ProgramSem.p917 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_917 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p917 nodes args res) : ProgramSem nodes 917 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_924 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 924 args res) : ProgramSem.p924 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_924 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p924 nodes args res) : ProgramSem nodes 924 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_926 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 926 args res) : ProgramSem.p926 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_926 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p926 nodes args res) : ProgramSem nodes 926 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_927 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 927 args res) : ProgramSem.p927 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_927 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p927 nodes args res) : ProgramSem nodes 927 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_928 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 928 args res) : ProgramSem.p928 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_928 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p928 nodes args res) : ProgramSem nodes 928 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_933 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 933 args res) : ProgramSem.p933 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_933 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p933 nodes args res) : ProgramSem nodes 933 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_935 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 935 args res) : ProgramSem.p935 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_935 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p935 nodes args res) : ProgramSem nodes 935 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_936 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 936 args res) : ProgramSem.p936 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_936 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p936 nodes args res) : ProgramSem nodes 936 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_939 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 939 args res) : ProgramSem.p939 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_939 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p939 nodes args res) : ProgramSem nodes 939 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_940 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 940 args res) : ProgramSem.p940 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_940 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p940 nodes args res) : ProgramSem nodes 940 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_941 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 941 args res) : ProgramSem.p941 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_941 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p941 nodes args res) : ProgramSem nodes 941 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_942 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 942 args res) : ProgramSem.p942 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_942 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p942 nodes args res) : ProgramSem nodes 942 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_944 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 944 args res) : ProgramSem.p944 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_944 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p944 nodes args res) : ProgramSem nodes 944 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_949 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 949 args res) : ProgramSem.p949 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_949 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p949 nodes args res) : ProgramSem nodes 949 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_952 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 952 args res) : ProgramSem.p952 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_952 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p952 nodes args res) : ProgramSem nodes 952 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_958 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 958 args res) : ProgramSem.p958 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_958 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p958 nodes args res) : ProgramSem nodes 958 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_961 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 961 args res) : ProgramSem.p961 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_961 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p961 nodes args res) : ProgramSem nodes 961 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_965 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 965 args res) : ProgramSem.p965 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_965 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p965 nodes args res) : ProgramSem nodes 965 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_966 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 966 args res) : ProgramSem.p966 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_966 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p966 nodes args res) : ProgramSem nodes 966 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_967 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 967 args res) : ProgramSem.p967 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_967 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p967 nodes args res) : ProgramSem nodes 967 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_968 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 968 args res) : ProgramSem.p968 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_968 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p968 nodes args res) : ProgramSem nodes 968 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_969 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 969 args res) : ProgramSem.p969 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_969 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p969 nodes args res) : ProgramSem nodes 969 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_972 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 972 args res) : ProgramSem.p972 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_972 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p972 nodes args res) : ProgramSem nodes 972 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_983 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 983 args res) : ProgramSem.p983 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_983 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p983 nodes args res) : ProgramSem nodes 983 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_985 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 985 args res) : ProgramSem.p985 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_985 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p985 nodes args res) : ProgramSem nodes 985 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_986 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 986 args res) : ProgramSem.p986 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_986 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p986 nodes args res) : ProgramSem nodes 986 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_987 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 987 args res) : ProgramSem.p987 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_987 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p987 nodes args res) : ProgramSem nodes 987 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_988 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 988 args res) : ProgramSem.p988 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_988 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p988 nodes args res) : ProgramSem nodes 988 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_989 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 989 args res) : ProgramSem.p989 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_989 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p989 nodes args res) : ProgramSem nodes 989 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_990 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 990 args res) : ProgramSem.p990 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_990 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p990 nodes args res) : ProgramSem nodes 990 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_991 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 991 args res) : ProgramSem.p991 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_991 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p991 nodes args res) : ProgramSem nodes 991 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_992 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 992 args res) : ProgramSem.p992 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_992 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p992 nodes args res) : ProgramSem nodes 992 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_994 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 994 args res) : ProgramSem.p994 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_994 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p994 nodes args res) : ProgramSem nodes 994 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_995 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 995 args res) : ProgramSem.p995 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_995 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p995 nodes args res) : ProgramSem nodes 995 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_996 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 996 args res) : ProgramSem.p996 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_996 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p996 nodes args res) : ProgramSem nodes 996 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_997 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 997 args res) : ProgramSem.p997 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_997 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p997 nodes args res) : ProgramSem nodes 997 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_998 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 998 args res) : ProgramSem.p998 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_998 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p998 nodes args res) : ProgramSem nodes 998 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1000 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1000 args res) : ProgramSem.p1000 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1000 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1000 nodes args res) : ProgramSem nodes 1000 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1001 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1001 args res) : ProgramSem.p1001 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1001 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1001 nodes args res) : ProgramSem nodes 1001 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1003 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1003 args res) : ProgramSem.p1003 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1003 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1003 nodes args res) : ProgramSem nodes 1003 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1016 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1016 args res) : ProgramSem.p1016 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1016 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1016 nodes args res) : ProgramSem nodes 1016 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1049 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1049 args res) : ProgramSem.p1049 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1049 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1049 nodes args res) : ProgramSem nodes 1049 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1059 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1059 args res) : ProgramSem.p1059 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1059 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1059 nodes args res) : ProgramSem nodes 1059 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1067 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1067 args res) : ProgramSem.p1067 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1067 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1067 nodes args res) : ProgramSem nodes 1067 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1068 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1068 args res) : ProgramSem.p1068 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1068 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1068 nodes args res) : ProgramSem nodes 1068 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1072 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1072 args res) : ProgramSem.p1072 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1072 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1072 nodes args res) : ProgramSem nodes 1072 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1073 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1073 args res) : ProgramSem.p1073 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1073 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1073 nodes args res) : ProgramSem nodes 1073 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1074 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1074 args res) : ProgramSem.p1074 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1074 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1074 nodes args res) : ProgramSem nodes 1074 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1075 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1075 args res) : ProgramSem.p1075 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1075 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1075 nodes args res) : ProgramSem nodes 1075 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1077 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1077 args res) : ProgramSem.p1077 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1077 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1077 nodes args res) : ProgramSem nodes 1077 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1090 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1090 args res) : ProgramSem.p1090 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1090 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1090 nodes args res) : ProgramSem nodes 1090 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1091 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1091 args res) : ProgramSem.p1091 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1091 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1091 nodes args res) : ProgramSem nodes 1091 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1094 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1094 args res) : ProgramSem.p1094 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1094 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1094 nodes args res) : ProgramSem nodes 1094 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1098 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1098 args res) : ProgramSem.p1098 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1098 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1098 nodes args res) : ProgramSem nodes 1098 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1099 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1099 args res) : ProgramSem.p1099 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1099 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1099 nodes args res) : ProgramSem nodes 1099 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1100 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1100 args res) : ProgramSem.p1100 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1100 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1100 nodes args res) : ProgramSem nodes 1100 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_4294967296 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 4294967296 args res) : ProgramSem.p4294967296 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_4294967296 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p4294967296 nodes args res) : ProgramSem nodes 4294967296 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

end pathos_compiled_checker
