import Mathdemo.Internal.CRat_iter360

set_option linter.style.longLine false

/-!
# G262: remove row-to-flat from the public theorem-4.15 frontier

G261 lowered theorem 4.15 to the corrected abs-row package
`Sec4ChiFCaseAbsPackTools`.  That package contains four components: the generic
row-to-flat bridge, the positive-side row extraction, the positive-side row
pack construction, and the negative-side row pack construction.

The generic row-to-flat bridge is already implemented as
`sec4_rowToFlat_source`.  This file uses it to build the abs-row package, so
the source-level theorem-4.15 route no longer exposes row-to-flat as an input.
The remaining public frontier is exactly the three function-side row package
components.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing data with row-to-flat already closed -/

structure Theorem415SourceFacingAbsPackNoRowToFlatStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_fabs_of_rows_s1 : forall n : Nat,
    BishopC.Sec4FAbsOfLambdaAbsRowsOnS1 (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_pack_on_s1_of_fabs : forall n : Nat,
    BishopC.Sec4LambdaRowsAbsPackOnS1OfFAbs (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_pack_on_s2 : forall n : Nat,
    BishopC.Sec4LambdaRowsAbsPackOnS2 (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingAbsPackTools_statement_data_of_noRowToFlat
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackNoRowToFlatStatementData (S := S) fn f) :
    Theorem415SourceFacingAbsPackToolsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_absPackTools := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.Sec4ChiFCaseAbsPackTools.mk
        (S := S) (f := u) (hnn := hnn_u)
        (BishopC.sec4_rowToFlat_source (S := S))
        (D.abs_error_fabs_of_rows_s1 n)
        (D.abs_error_pack_on_s1_of_fabs n)
        (D.abs_error_pack_on_s2 n)

noncomputable def theorem415_sourceFacingStepAbs_statement_data_of_noRowToFlat
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackNoRowToFlatStatementData (S := S) fn f) :
    Theorem415SourceFacingStepAbsStatementData (S := S) fn f :=
  theorem415_sourceFacingStepAbs_statement_data_of_absPackTools
    (S := S)
    (theorem415_sourceFacingAbsPackTools_statement_data_of_noRowToFlat
      (S := S) D)

noncomputable def theorem415_integral_convergence_from_sourceFacingAbsPackNoRowToFlat_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingAbsPackNoRowToFlatStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingAbsPackTools_via_stepAbs_statement_data
    (S := S)
    (theorem415_sourceFacingAbsPackTools_statement_data_of_noRowToFlat
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415SourceFacingNoRowToFlatAbsPackRouteAuditAfterG262 : Type where
  source_facing_convergence_in_measure_used : Nat
  row_to_flat_public_input_required : Nat
  row_to_flat_closed_by_sec4_rowToFlat_source : Nat
  positive_side_row_abs_extraction_required : Nat
  positive_side_row_abs_pack_required : Nat
  negative_side_row_abs_pack_required : Nat
  abstract_case_tools_public_input_required : Nat
  b_specific_step_abs_public_input_required : Nat
  old_global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_row_package_component_frontiers : Nat

def theorem415SourceFacingNoRowToFlatAbsPackRouteAuditAfterG262 :
    Theorem415SourceFacingNoRowToFlatAbsPackRouteAuditAfterG262 where
  source_facing_convergence_in_measure_used := 1
  row_to_flat_public_input_required := 0
  row_to_flat_closed_by_sec4_rowToFlat_source := 1
  positive_side_row_abs_extraction_required := 1
  positive_side_row_abs_pack_required := 1
  negative_side_row_abs_pack_required := 1
  abstract_case_tools_public_input_required := 0
  b_specific_step_abs_public_input_required := 0
  old_global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_row_package_component_frontiers := 3

structure Chapter4G262Theorem415SourceFacingNoRowToFlatAbsPackPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g261 : Chapter4G261Theorem415SourceFacingAbsPackStepAbsPackage S
  audit : Theorem415SourceFacingNoRowToFlatAbsPackRouteAuditAfterG262
  row_to_flat_public_frontier_removed_this_step : Nat
  remaining_row_package_component_frontiers : Nat

def chapter4G262Theorem415SourceFacingNoRowToFlatAbsPackPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G262Theorem415SourceFacingNoRowToFlatAbsPackPackage S where
  g261 := chapter4G261Theorem415SourceFacingAbsPackStepAbsPackage S
  audit := theorem415SourceFacingNoRowToFlatAbsPackRouteAuditAfterG262
  row_to_flat_public_frontier_removed_this_step := 1
  remaining_row_package_component_frontiers := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G262. -/
def bishopRegularSeqChapter4Theorem415SourceFacingNoRowToFlatAbsPackProgressAfterG262 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G262: row-to-flat is no longer a public theorem-4.15 frontier; it is \
    filled by sec4_rowToFlat_source.  The source-level route now needs only \
    the three function-side row-package components for each abs-error term. \
    Remaining countdown: 3 row-package components."


end BishopCReal
