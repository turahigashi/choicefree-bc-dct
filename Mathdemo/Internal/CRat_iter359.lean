import Mathdemo.Internal.CRat_iter358
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b10_stepAbs_iteration1
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b13_dichotomyData_iteration1

set_option linter.style.longLine false

/-!
# G260: source-level theorem 4.15 down to the one-step finite-cover assembly

G259 replayed the lower `I_B` route on the source-level theorem-4.15 surface,
but its last public route also displayed the older standard-row provider
components.  This file records the cleaner constructive route:

* the public theorem-4.15 surface remains `fn -> f` convergence in measure;
* `I_B` value identification is still discharged through the local bridge;
* the local bridge is produced from the one-step finite-cover abs assembly
  `Sec4CoverChiFStepAbs`;
* the `B`-dependent data-valued cover dichotomy is constructed internally by
  `sec4_coverDichotomyData`, so it is not an external input;
* from source-level function-side `Sec4ChiFCaseToolsData`, the one-step
  finite-cover assembly is obtained by `sec4_coverChiFStepAbs_of_dataCases`.

The remaining frontier is therefore the function-side `χ_A · f` case-tool
package for each absolute-error representative.  No Prop-to-Type witness
extraction or external selector is added here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing theorem 4.15 from one-step cover abs data -/

structure Theorem415SourceFacingStepAbsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_stepAbs : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4CoverChiFStepAbs (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingLocalBridge_statement_data_of_stepAbs
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStepAbsStatementData (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_local_bridge := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_genIBLocalValueBridge_of_valueBridge
        (S := S) B hB u hnn_u
        (BishopC.sec4_genIBValueBridge_of_stepAbs
          (S := S) B hB u hnn_u
          (D.abs_error_stepAbs n B hB))

noncomputable def theorem415_integral_convergence_from_sourceFacingStepAbs_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStepAbsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalBridge_statement_data
    (S := S)
    (theorem415_sourceFacingLocalBridge_statement_data_of_stepAbs
      (S := S) D)

/-! ## 2. Function-side case tools construct the one-step cover assembly -/

noncomputable def theorem415_sourceFacingStepAbs_statement_data_of_caseTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCaseToolsStatementData (S := S) fn f) :
    Theorem415SourceFacingStepAbsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_stepAbs := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_coverChiFStepAbs_of_dataCases
        (S := S) B hB u hnn_u
        (D.abs_error_caseTools n)
        (BishopC.sec4_coverDichotomyData (S := S) B hB u)

noncomputable def theorem415_integral_convergence_from_sourceFacingCaseTools_via_stepAbs_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCaseToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingStepAbs_statement_data
    (S := S)
    (theorem415_sourceFacingStepAbs_statement_data_of_caseTools
      (S := S) D)

/-! ## 3. Source-facing route through final tools -/

structure Theorem415SourceFacingFinalToolsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_finalTools : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4Prop42FinalTools (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingFinalTools_statement_data_of_stepAbs
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStepAbsStatementData (S := S) fn f) :
    Theorem415SourceFacingFinalToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_finalTools := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_prop42FinalTools_of_stepAbs
        (S := S) B hB u hnn_u
        (D.abs_error_stepAbs n B hB)

noncomputable def theorem415_sourceFacingLocalBridge_statement_data_of_finalTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingFinalToolsStatementData (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_local_bridge := by
    intro n B hB
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_genIBLocalValueBridge_of_valueBridge
        (S := S) B hB u hnn_u
        (BishopC.sec4_genIBValueBridge_of_finalTools
          (S := S) B hB u hnn_u
          (D.abs_error_finalTools n B hB))

noncomputable def theorem415_integral_convergence_from_sourceFacingFinalTools_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingFinalToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalBridge_statement_data
    (S := S)
    (theorem415_sourceFacingLocalBridge_statement_data_of_finalTools
      (S := S) D)

/-! ## 4. Audit and package -/

structure Theorem415SourceFacingStepAbsRouteAuditAfterG260 : Type where
  source_facing_convergence_in_measure_used : Nat
  local_full_set_bridge_public_input_required : Nat
  canonical_cover_chi_data_public_input_required : Nat
  telescope_or_layer_telescope_public_input_required : Nat
  b_specific_cover_dichotomy_public_input_required : Nat
  b_specific_step_abs_public_input_required_after_case_tools_route : Nat
  function_side_chi_f_case_tools_required : Nat
  data_valued_cover_dichotomy_constructed_from_validness : Nat
  old_global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  row_to_flat_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_function_side_chi_f_case_tool_frontiers : Nat

def theorem415SourceFacingStepAbsRouteAuditAfterG260 :
    Theorem415SourceFacingStepAbsRouteAuditAfterG260 where
  source_facing_convergence_in_measure_used := 1
  local_full_set_bridge_public_input_required := 0
  canonical_cover_chi_data_public_input_required := 0
  telescope_or_layer_telescope_public_input_required := 0
  b_specific_cover_dichotomy_public_input_required := 0
  b_specific_step_abs_public_input_required_after_case_tools_route := 0
  function_side_chi_f_case_tools_required := 1
  data_valued_cover_dichotomy_constructed_from_validness := 1
  old_global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  row_to_flat_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_function_side_chi_f_case_tool_frontiers := 1

structure Chapter4G260Theorem415SourceFacingStepAbsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g259 : Chapter4G259Theorem415SourceFacingNoRowToFlatPackage S
  audit : Theorem415SourceFacingStepAbsRouteAuditAfterG260
  data_valued_cover_dichotomy_constructed_this_step : Nat
  source_route_lowered_to_one_step_cover_abs_this_step : Nat
  remaining_function_side_chi_f_case_tool_frontiers : Nat

def chapter4G260Theorem415SourceFacingStepAbsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G260Theorem415SourceFacingStepAbsPackage S where
  g259 := chapter4G259Theorem415SourceFacingNoRowToFlatPackage S
  audit := theorem415SourceFacingStepAbsRouteAuditAfterG260
  data_valued_cover_dichotomy_constructed_this_step := 1
  source_route_lowered_to_one_step_cover_abs_this_step := 1
  remaining_function_side_chi_f_case_tool_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G260. -/
def bishopRegularSeqChapter4Theorem415SourceFacingStepAbsProgressAfterG260 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G260: source-level theorem 4.15 is lowered to the one-step finite-cover \
    abs assembly.  The B-dependent data-valued cover dichotomy is constructed \
    internally from integrable-set validness; no external selector, PFun layer, \
    row-to-flat input, or previous global characteristic-domain witness is added. \
    Remaining countdown: 1 function-side chi-f case-tool frontier."


end BishopCReal
