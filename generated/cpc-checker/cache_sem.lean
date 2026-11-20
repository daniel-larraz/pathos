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

/-- `$dt_updater_elim_rhs`. -/
def ProgramSem.p68 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__dt_updater_elim_rhs x0 x1 x2)

theorem ProgramSem.p68.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p68 nodes args res) :
    ProgramSem.p68 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$eo_dd_lookup`. -/
def ProgramSem.p75 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dd_lookup x0 x1)

theorem ProgramSem.p75.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p75 nodes args res) :
    ProgramSem.p75 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_dt_resolve`. -/
def ProgramSem.p81 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dt_resolve x0 x1)

theorem ProgramSem.p81.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p81 nodes args res) :
    ProgramSem.p81 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$eo_dtc_resolve`. -/
def ProgramSem.p84 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__eo_dtc_resolve x0 x1)

theorem ProgramSem.p84.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p84 nodes args res) :
    ProgramSem.p84 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$get_arg_list_rec`. -/
def ProgramSem.p879 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__get_arg_list_rec x0 x1)

theorem ProgramSem.p879.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p879 nodes args res) :
    ProgramSem.p879 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$is_absorb_rec`. -/
def ProgramSem.p889 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__is_absorb_rec x0 x1 x2)

theorem ProgramSem.p889.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p889 nodes args res) :
    ProgramSem.p889 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$is_renaming_rec`. -/
def ProgramSem.p900 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__is_renaming_rec x0 x1)

theorem ProgramSem.p900.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p900 nodes args res) :
    ProgramSem.p900 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$is_seq_const_rec`. -/
def ProgramSem.p902 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__is_seq_const_rec x0)

theorem ProgramSem.p902.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p902 nodes args res) :
    ProgramSem.p902 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$mk_arith_sum_ub_rec`. -/
def ProgramSem.p912 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_arith_sum_ub_rec x0 x1)

theorem ProgramSem.p912.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p912 nodes args res) :
    ProgramSem.p912 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_dt_inst_rec`. -/
def ProgramSem.p920 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_dt_inst_rec x0 x1 x2)

theorem ProgramSem.p920.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p920 nodes args res) :
    ProgramSem.p920 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_ho_cong`. -/
def ProgramSem.p924 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_ho_cong x0 x1 x2)

theorem ProgramSem.p924.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p924 nodes args res) :
    ProgramSem.p924 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$mk_re_concat`. -/
def ProgramSem.p929 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__mk_re_concat x0 x1)

theorem ProgramSem.p929.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p929 nodes args res) :
    ProgramSem.p929 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$mk_trans`. -/
def ProgramSem.p937 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (a2 : Term) (x0 : _) (x1 : _) (x2 : _), args = [a0, a1, a2] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧ Rep nodes a2.val x2 ∧
    Rep nodes res.val (__mk_trans x0 x1 x2)

theorem ProgramSem.p937.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p937 nodes args res) :
    ProgramSem.p937 nodes' args res := by
  obtain ⟨a0, a1, a2, x0, x1, x2, hargs, h0, h1, h2, hr⟩ := h
  exact ⟨a0, a1, a2, x0, x1, x2, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre h2, Rep.mono hpre hr⟩

/-- `$smtx_dd_has_dt`. -/
def ProgramSem.p971 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dd_has_dt x0 x1)

theorem ProgramSem.p971.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p971 nodes args res) :
    ProgramSem.p971 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dd_lookup`. -/
def ProgramSem.p972 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dd_lookup x0 x1)

theorem ProgramSem.p972.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p972 nodes args res) :
    ProgramSem.p972 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_decl_inhabited`. -/
def ProgramSem.p973 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_decl_inhabited x0 x1)

theorem ProgramSem.p973.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p973 nodes args res) :
    ProgramSem.p973 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_decl_wf_rec`. -/
def ProgramSem.p974 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_decl_wf_rec x0 x1)

theorem ProgramSem.p974.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p974 nodes args res) :
    ProgramSem.p974 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_cons_inhabited`. -/
def ProgramSem.p975 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_cons_inhabited x0 x1)

theorem ProgramSem.p975.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p975 nodes args res) :
    ProgramSem.p975 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_cons_wf_rec`. -/
def ProgramSem.p976 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_cons_wf_rec x0 x1)

theorem ProgramSem.p976.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p976 nodes args res) :
    ProgramSem.p976 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_inhabited`. -/
def ProgramSem.p977 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_inhabited x0 x1)

theorem ProgramSem.p977.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p977 nodes args res) :
    ProgramSem.p977 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_resolve`. -/
def ProgramSem.p979 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_resolve x0 x1)

theorem ProgramSem.p979.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p979 nodes args res) :
    ProgramSem.p979 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dt_wf_rec`. -/
def ProgramSem.p980 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dt_wf_rec x0 x1)

theorem ProgramSem.p980.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p980 nodes args res) :
    ProgramSem.p980 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_dtc_resolve`. -/
def ProgramSem.p982 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__smtx_dtc_resolve x0 x1)

theorem ProgramSem.p982.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p982 nodes args res) :
    ProgramSem.p982 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$smtx_inhabited_type`. -/
def ProgramSem.p983 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_inhabited_type x0)

theorem ProgramSem.p983.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p983 nodes args res) :
    ProgramSem.p983 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_type_wf`. -/
def ProgramSem.p986 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_type_wf x0)

theorem ProgramSem.p986.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p986 nodes args res) :
    ProgramSem.p986 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$smtx_type_wf_rec`. -/
def ProgramSem.p988 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (x0 : _), args = [a0] ∧ Rep nodes a0.val x0 ∧
    Rep nodes res.val (__smtx_type_wf_rec x0)

theorem ProgramSem.p988.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p988 nodes args res) :
    ProgramSem.p988 nodes' args res := by
  obtain ⟨a0, x0, hargs, h0, hr⟩ := h
  exact ⟨a0, x0, hargs, Rep.mono hpre h0, Rep.mono hpre hr⟩

/-- `$str_strip_prefix`. -/
def ProgramSem.p1073 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__str_strip_prefix x0 x1)

theorem ProgramSem.p1073.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1073 nodes args res) :
    ProgramSem.p1073 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- `$strip_even_exponent`. -/
def ProgramSem.p1077 (nodes : List TermData) (args : List Term) (res : Term) : Prop :=
  ∃ (a0 : Term) (a1 : Term) (x0 : _) (x1 : _), args = [a0, a1] ∧ Rep nodes a0.val x0 ∧ Rep nodes a1.val x1 ∧
    Rep nodes res.val (__strip_even_exponent x0 x1)

theorem ProgramSem.p1077.mono {nodes nodes' : List TermData} {args : List Term} {res : Term}
    (hpre : nodes <+: nodes') (h : ProgramSem.p1077 nodes args res) :
    ProgramSem.p1077 nodes' args res := by
  obtain ⟨a0, a1, x0, x1, hargs, h0, h1, hr⟩ := h
  exact ⟨a0, a1, x0, x1, hargs, Rep.mono hpre h0, Rep.mono hpre h1, Rep.mono hpre hr⟩

/-- What an entry of the program `pid` with the arguments `args` and the result
`res` says, in a store whose terms are `nodes`. -/
def ProgramSem (nodes : List TermData) (pid : Nat) (args : List Term) (res : Term) : Prop :=
  (pid = 68 → ProgramSem.p68 nodes args res) ∧
  (pid = 75 → ProgramSem.p75 nodes args res) ∧
  (pid = 81 → ProgramSem.p81 nodes args res) ∧
  (pid = 84 → ProgramSem.p84 nodes args res) ∧
  (pid = 879 → ProgramSem.p879 nodes args res) ∧
  (pid = 889 → ProgramSem.p889 nodes args res) ∧
  (pid = 900 → ProgramSem.p900 nodes args res) ∧
  (pid = 902 → ProgramSem.p902 nodes args res) ∧
  (pid = 912 → ProgramSem.p912 nodes args res) ∧
  (pid = 920 → ProgramSem.p920 nodes args res) ∧
  (pid = 924 → ProgramSem.p924 nodes args res) ∧
  (pid = 929 → ProgramSem.p929 nodes args res) ∧
  (pid = 937 → ProgramSem.p937 nodes args res) ∧
  (pid = 971 → ProgramSem.p971 nodes args res) ∧
  (pid = 972 → ProgramSem.p972 nodes args res) ∧
  (pid = 973 → ProgramSem.p973 nodes args res) ∧
  (pid = 974 → ProgramSem.p974 nodes args res) ∧
  (pid = 975 → ProgramSem.p975 nodes args res) ∧
  (pid = 976 → ProgramSem.p976 nodes args res) ∧
  (pid = 977 → ProgramSem.p977 nodes args res) ∧
  (pid = 979 → ProgramSem.p979 nodes args res) ∧
  (pid = 980 → ProgramSem.p980 nodes args res) ∧
  (pid = 982 → ProgramSem.p982 nodes args res) ∧
  (pid = 983 → ProgramSem.p983 nodes args res) ∧
  (pid = 986 → ProgramSem.p986 nodes args res) ∧
  (pid = 988 → ProgramSem.p988 nodes args res) ∧
  (pid = 1073 → ProgramSem.p1073 nodes args res) ∧
  (pid = 1077 → ProgramSem.p1077 nodes args res) ∧
  True

theorem ProgramSem.mono {nodes nodes' : List TermData} {pid : Nat} {args : List Term}
    {res : Term} (hpre : nodes <+: nodes') (h : ProgramSem nodes pid args res) :
    ProgramSem nodes' pid args res :=
  ⟨fun e => ProgramSem.p68.mono hpre (h.1 e), fun e => ProgramSem.p75.mono hpre (h.2.1 e), fun e => ProgramSem.p81.mono hpre (h.2.2.1 e), fun e => ProgramSem.p84.mono hpre (h.2.2.2.1 e), fun e => ProgramSem.p879.mono hpre (h.2.2.2.2.1 e), fun e => ProgramSem.p889.mono hpre (h.2.2.2.2.2.1 e), fun e => ProgramSem.p900.mono hpre (h.2.2.2.2.2.2.1 e), fun e => ProgramSem.p902.mono hpre (h.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p912.mono hpre (h.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p920.mono hpre (h.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p924.mono hpre (h.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p929.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p937.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p971.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p972.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p973.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p974.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p975.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p976.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p977.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p979.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p980.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p982.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p983.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p986.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p988.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1073.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), fun e => ProgramSem.p1077.mono hpre (h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e), trivial⟩

theorem ProgramSem.of_68 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 68 args res) : ProgramSem.p68 nodes args res :=
  h.1 rfl

theorem ProgramSem.to_68 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p68 nodes args res) : ProgramSem nodes 68 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_75 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 75 args res) : ProgramSem.p75 nodes args res :=
  h.2.1 rfl

theorem ProgramSem.to_75 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p75 nodes args res) : ProgramSem nodes 75 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_81 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 81 args res) : ProgramSem.p81 nodes args res :=
  h.2.2.1 rfl

theorem ProgramSem.to_81 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p81 nodes args res) : ProgramSem nodes 81 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_84 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 84 args res) : ProgramSem.p84 nodes args res :=
  h.2.2.2.1 rfl

theorem ProgramSem.to_84 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p84 nodes args res) : ProgramSem nodes 84 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_879 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 879 args res) : ProgramSem.p879 nodes args res :=
  h.2.2.2.2.1 rfl

theorem ProgramSem.to_879 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p879 nodes args res) : ProgramSem nodes 879 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_889 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 889 args res) : ProgramSem.p889 nodes args res :=
  h.2.2.2.2.2.1 rfl

theorem ProgramSem.to_889 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p889 nodes args res) : ProgramSem nodes 889 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_900 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 900 args res) : ProgramSem.p900 nodes args res :=
  h.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_900 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p900 nodes args res) : ProgramSem nodes 900 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_902 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 902 args res) : ProgramSem.p902 nodes args res :=
  h.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_902 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p902 nodes args res) : ProgramSem nodes 902 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_912 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 912 args res) : ProgramSem.p912 nodes args res :=
  h.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_912 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p912 nodes args res) : ProgramSem nodes 912 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_920 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 920 args res) : ProgramSem.p920 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_920 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p920 nodes args res) : ProgramSem nodes 920 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_924 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 924 args res) : ProgramSem.p924 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_924 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p924 nodes args res) : ProgramSem nodes 924 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_929 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 929 args res) : ProgramSem.p929 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_929 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p929 nodes args res) : ProgramSem nodes 929 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_937 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 937 args res) : ProgramSem.p937 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_937 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p937 nodes args res) : ProgramSem nodes 937 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_971 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 971 args res) : ProgramSem.p971 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_971 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p971 nodes args res) : ProgramSem nodes 971 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_972 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 972 args res) : ProgramSem.p972 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_972 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p972 nodes args res) : ProgramSem nodes 972 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_973 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 973 args res) : ProgramSem.p973 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_973 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p973 nodes args res) : ProgramSem nodes 973 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_974 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 974 args res) : ProgramSem.p974 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_974 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p974 nodes args res) : ProgramSem nodes 974 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_975 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 975 args res) : ProgramSem.p975 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_975 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p975 nodes args res) : ProgramSem nodes 975 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_976 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 976 args res) : ProgramSem.p976 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_976 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p976 nodes args res) : ProgramSem nodes 976 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_977 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 977 args res) : ProgramSem.p977 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_977 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p977 nodes args res) : ProgramSem nodes 977 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_979 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 979 args res) : ProgramSem.p979 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_979 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p979 nodes args res) : ProgramSem nodes 979 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_980 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 980 args res) : ProgramSem.p980 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_980 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p980 nodes args res) : ProgramSem nodes 980 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_982 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 982 args res) : ProgramSem.p982 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_982 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p982 nodes args res) : ProgramSem nodes 982 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_983 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 983 args res) : ProgramSem.p983 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_983 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p983 nodes args res) : ProgramSem nodes 983 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_986 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 986 args res) : ProgramSem.p986 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_986 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p986 nodes args res) : ProgramSem nodes 986 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_988 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 988 args res) : ProgramSem.p988 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_988 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p988 nodes args res) : ProgramSem nodes 988 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1073 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1073 args res) : ProgramSem.p1073 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1073 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1073 nodes args res) : ProgramSem nodes 1073 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

theorem ProgramSem.of_1077 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem nodes 1077 args res) : ProgramSem.p1077 nodes args res :=
  h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 rfl

theorem ProgramSem.to_1077 {nodes : List TermData} {args : List Term} {res : Term}
    (h : ProgramSem.p1077 nodes args res) : ProgramSem nodes 1077 args res := by
  unfold ProgramSem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩ <;> intro e <;> first | exact h | exact absurd e (by decide)

end pathos_compiled_checker
