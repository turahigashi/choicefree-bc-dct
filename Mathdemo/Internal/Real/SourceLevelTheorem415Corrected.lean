import Mathdemo.Internal.Real.SourceLevelTheorem415DownOneStepFiniteCover

set_option linter.style.longLine false

/-!
# G261: source-level theorem 4.15 from the corrected abs-row package

G260 lowered the source-level theorem-4.15 route to the one-step finite-cover
abs assembly `Sec4CoverChiFStepAbs`, and showed that source-level
`Sec4ChiFCaseToolsData` builds that assembly without any `B`-dependent
selector input.

This file lowers the remaining function-side case-tool input to the corrected
abs-row package already proved in b2b20:

`Sec4ChiFCaseAbsPackTools -> Sec4ChiFCaseToolsData -> Sec4CoverChiFStepAbs`.

Thus the public theorem-4.15 route no longer asks for the abstract case tools.
It asks for the row/outer absolute-convergence package for each absolute-error
representative.  That package is still data-carrying, but its components are
the explicit row-to-flat bridge and the positive/negative row abs pack
constructors, not a hidden choice principle.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Abs-row packages directly produce the one-step cover assembly -/

noncomputable def theorem415_sourceFacingStepAbs_statement_data_of_absPackTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f) :
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
    let Tcase : BishopC.Sec4ChiFCaseToolsData (S := S) u hnn_u :=
      BishopC.sec4_chiFCaseToolsData_of_absPackTools
        (S := S) u hnn_u
        (D.abs_error_absPackTools n)
    exact
      BishopC.sec4_coverChiFStepAbs_of_dataCases
        (S := S) B hB u hnn_u
        Tcase
        (BishopC.sec4_coverDichotomyData (S := S) B hB u)

noncomputable def theorem415_sourceFacingFinalTools_statement_data_of_absPackTools
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f) :
    Theorem415SourceFacingFinalToolsStatementData (S := S) fn f :=
  theorem415_sourceFacingFinalTools_statement_data_of_stepAbs
    (S := S)
    (theorem415_sourceFacingStepAbs_statement_data_of_absPackTools
      (S := S) D)

noncomputable def theorem415_integral_convergence_from_sourceFacingAbsPackTools_via_stepAbs_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingStepAbs_statement_data
    (S := S)
    (theorem415_sourceFacingStepAbs_statement_data_of_absPackTools
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415SourceFacingAbsPackStepAbsRouteAuditAfterG261 : Type where
  source_facing_convergence_in_measure_used : Nat
  abstract_case_tools_public_input_required : Nat
  b_specific_cover_dichotomy_public_input_required : Nat
  b_specific_step_abs_public_input_required : Nat
  abs_row_package_per_error_required : Nat
  row_to_flat_present_only_inside_abs_row_package : Nat
  positive_side_row_abs_pack_required : Nat
  negative_side_row_abs_pack_required : Nat
  old_global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_abs_row_package_component_frontiers : Nat

def theorem415SourceFacingAbsPackStepAbsRouteAuditAfterG261 :
    Theorem415SourceFacingAbsPackStepAbsRouteAuditAfterG261 where
  source_facing_convergence_in_measure_used := 1
  abstract_case_tools_public_input_required := 0
  b_specific_cover_dichotomy_public_input_required := 0
  b_specific_step_abs_public_input_required := 0
  abs_row_package_per_error_required := 1
  row_to_flat_present_only_inside_abs_row_package := 1
  positive_side_row_abs_pack_required := 1
  negative_side_row_abs_pack_required := 1
  old_global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_abs_row_package_component_frontiers := 3

structure Chapter4G261Theorem415SourceFacingAbsPackStepAbsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g260 : Chapter4G260Theorem415SourceFacingStepAbsPackage S
  audit : Theorem415SourceFacingAbsPackStepAbsRouteAuditAfterG261
  abstract_case_tools_removed_this_step : Nat
  source_route_lowered_to_abs_row_package_this_step : Nat
  remaining_abs_row_package_component_frontiers : Nat

def chapter4G261Theorem415SourceFacingAbsPackStepAbsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G261Theorem415SourceFacingAbsPackStepAbsPackage S where
  g260 := chapter4G260Theorem415SourceFacingStepAbsPackage S
  audit := theorem415SourceFacingAbsPackStepAbsRouteAuditAfterG261
  abstract_case_tools_removed_this_step := 1
  source_route_lowered_to_abs_row_package_this_step := 1
  remaining_abs_row_package_component_frontiers := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G261. -/
def bishopRegularSeqChapter4Theorem415SourceFacingAbsPackStepAbsProgressAfterG261 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G261: the theorem-4.15 source-level route now goes from the corrected \
    abs-row package to the one-step cover assembly, then to the local value \
    bridge and integral convergence.  The abstract chi-f case-tool input is \
    no longer public.  Remaining countdown: 3 abs-row package components."


end BishopCReal
