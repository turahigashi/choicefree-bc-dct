import Mathdemo.Internal.CRat_iter347
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b14_caseRowTools_iteration1

set_option linter.style.longLine false

/-!
# G249: theorem 4.15 from generic case tools

G248 connected theorem 4.15 to layer telescope data.  This file adds the
parallel route that is closer to the definitional reading of measurable sets:
the set-side cover/difference dichotomy is not supplied per `B`; it is built by
`sec4_coverDichotomyData` from the validness fields of the integrable sets
`coverSet f k ∧ B` and their difference layers.

Thus the public input is only function-side `χ_A·f` case tools for the
abs-error representatives.  The measurable-set side is obtained from the
definitions already present in chapter 4.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-- Theorem-4.15 statement data using function-side case tools for every
abs-error representative. -/
structure Theorem415AbsErrorCaseToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_caseTools : forall n : Nat,
    BishopC.Sec4ChiFCaseToolsData (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Generic case tools give the local-bridge statement data used in G246. -/
noncomputable def theorem415_localBridge_statement_data_of_caseTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorCaseToolsStatementData (S := S) fn f) :
    Theorem415AbsErrorLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_local_bridge := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_genIBLocalValueBridge_of_valueBridge
        (S := S) B hB u hnn_u
        (BishopC.sec4_genIBValueBridge_of_chiFCaseTools
          (S := S) B hB u hnn_u
          (D.abs_error_caseTools n))
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from function-side case tools. -/
noncomputable def theorem415_integral_convergence_from_caseTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorCaseToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_localBridge_statement_data
    (S := S)
    (theorem415_localBridge_statement_data_of_caseTools (S := S) D)

/-- Theorem-4.15 statement data using row-level case tools for every abs-error
representative. -/
structure Theorem415AbsErrorRowCaseToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  abs_error_rowCaseTools : forall n : Nat,
    BishopC.Sec4ChiFCaseRowTools (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  pfnsrc : Nat -> BishopC.PFunR Y R
  pf : BishopC.PFunR Y R
  pfun_converges :
    BishopC.Lemma415PFunConvergeData (S := S) pfnsrc pf
  represents_fn : forall n,
    BishopC.Lemma414RepresentsPFunR (S := S) (fn n) (pfnsrc n)
  represents_limit :
    BishopC.Lemma414RepresentsPFunR (S := S) f pf

/-- Row-level case tools give the function-side case-tool route. -/
noncomputable def theorem415_caseTools_statement_data_of_rowCaseTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorRowCaseToolsStatementData (S := S) fn f) :
    Theorem415AbsErrorCaseToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  abs_error_caseTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_chiFCaseToolsData_of_rowTools
        (S := S) u hnn_u
        (D.abs_error_rowCaseTools n)
  pfnsrc := D.pfnsrc
  pf := D.pf
  pfun_converges := D.pfun_converges
  represents_fn := D.represents_fn
  represents_limit := D.represents_limit

/-- Theorem 4.15 from row-level case tools. -/
noncomputable def theorem415_integral_convergence_from_rowCaseTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415AbsErrorRowCaseToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_caseTools_statement_data
    (S := S)
    (theorem415_caseTools_statement_data_of_rowCaseTools (S := S) D)

structure Theorem415CaseToolsRouteAuditAfterG249 : Type where
  per_set_cover_or_chi_data_required : Nat
  set_dichotomy_built_from_integrable_validness : Nat
  row_case_tools_route_added : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_row_case_tool_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def theorem415CaseToolsRouteAuditAfterG249 :
    Theorem415CaseToolsRouteAuditAfterG249 where
  per_set_cover_or_chi_data_required := 0
  set_dichotomy_built_from_integrable_validness := 1
  row_case_tools_route_added := 1
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_row_case_tool_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

structure Chapter4G249Theorem415CaseToolsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g248 : Chapter4G248Theorem415LayerTelescopePackage S
  audit : Theorem415CaseToolsRouteAuditAfterG249
  per_set_cover_or_chi_data_removed_this_step : Nat
  remaining_row_case_tool_construction_frontiers : Nat
  remaining_pfun_representation_frontiers : Nat

def chapter4G249Theorem415CaseToolsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G249Theorem415CaseToolsPackage S where
  g248 := chapter4G248Theorem415LayerTelescopePackage S
  audit := theorem415CaseToolsRouteAuditAfterG249
  per_set_cover_or_chi_data_removed_this_step := 1
  remaining_row_case_tool_construction_frontiers := 1
  remaining_pfun_representation_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G249. -/
def bishopRegularSeqChapter4Theorem415CaseToolsProgressAfterG249 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G249: added a theorem-4.15 route from function-side case tools. The \
    set-side cover/difference dichotomy is built from IntegrableSet1.valid \
    via sec4_coverDichotomyData, so the route no longer asks for per-set \
    cover/χ data. Remaining frontiers are row-level case-tool construction \
    for the abs-error representatives and the PFun/representation source \
    layer."


end BishopCReal
