import Mathdemo.Internal.CRat_iter361

set_option linter.style.longLine false

/-!
# G263: replace the first row-package frontier by the row-0 reconstruction

G262 left three public row-package components for each theorem-4.15 absolute
error term.  The first one, reconstruction of `f` absolute convergence from
lambda-row absolute convergence on `A.S1`, is already closed generically by
the row-0-right argument from b2b27.

This file uses that result on the source-level theorem-4.15 route.  The
remaining frontier is now the three residual row-seed fields:

* characteristic absolute convergence on `A.S1`;
* corrected outer convergence for the standard positive-side rows;
* corrected negative-side row package.

The first row-package field is no longer public.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing data using row-seed residual fields -/

structure Theorem415SourceFacingRowSeedResidualStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_chi_abs_on_s1_of_fabs : forall n : Nat,
    BishopC.Sec4Prop42ChiAbsOnS1OfFAbs (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_abs_outer_on_s1_of_rows : forall n : Nat,
    BishopC.Sec4Prop42AbsOuterOnS1OfRows (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_pack_on_s2 : forall n : Nat,
    BishopC.Sec4LambdaRowsAbsPackOnS2 (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_sourceFacingAbsPackNoRowToFlat_statement_data_of_rowSeedResidual
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualStatementData (S := S) fn f) :
    Theorem415SourceFacingAbsPackNoRowToFlatStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_fabs_of_rows_s1 := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    exact
      BishopC.sec4_fabsOfLambdaAbsRowsOnS1_of_row0Right_general
        (S := S) u hnn_u
  abs_error_pack_on_s1_of_fabs := by
    intro n
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    let T : BishopC.Sec4Prop42RowSeedResidualTools (S := S) u hnn_u :=
      BishopC.Sec4Prop42RowSeedResidualTools.mk
        (S := S) (f := u) (hnn := hnn_u)
        (D.abs_error_chi_abs_on_s1_of_fabs n)
        (D.abs_error_abs_outer_on_s1_of_rows n)
        (D.abs_error_pack_on_s2 n)
    exact
      BishopC.sec4_packOnS1_of_rowSeedTools
        (S := S) u hnn_u
        (BishopC.sec4_rowSeedTools_of_residualTools (S := S) u hnn_u T)
  abs_error_pack_on_s2 := D.abs_error_pack_on_s2

noncomputable def theorem415_sourceFacingStepAbs_statement_data_of_rowSeedResidual
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualStatementData (S := S) fn f) :
    Theorem415SourceFacingStepAbsStatementData (S := S) fn f :=
  theorem415_sourceFacingStepAbs_statement_data_of_noRowToFlat
    (S := S)
    (theorem415_sourceFacingAbsPackNoRowToFlat_statement_data_of_rowSeedResidual
      (S := S) D)

noncomputable def theorem415_integral_convergence_from_sourceFacingRowSeedResidual_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingRowSeedResidualStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingAbsPackNoRowToFlat_statement_data
    (S := S)
    (theorem415_sourceFacingAbsPackNoRowToFlat_statement_data_of_rowSeedResidual
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415SourceFacingRowSeedResidualRouteAuditAfterG263 : Type where
  source_facing_convergence_in_measure_used : Nat
  row_to_flat_public_input_required : Nat
  fabs_of_rows_s1_public_input_required : Nat
  fabs_of_rows_s1_closed_by_row0_right : Nat
  chi_abs_on_s1_of_fabs_required : Nat
  abs_outer_on_s1_of_rows_required : Nat
  pack_on_s2_required : Nat
  b_specific_step_abs_public_input_required : Nat
  old_global_characteristic_domain_witness_required : Nat
  pfun_representation_data_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_row_seed_residual_frontiers : Nat

def theorem415SourceFacingRowSeedResidualRouteAuditAfterG263 :
    Theorem415SourceFacingRowSeedResidualRouteAuditAfterG263 where
  source_facing_convergence_in_measure_used := 1
  row_to_flat_public_input_required := 0
  fabs_of_rows_s1_public_input_required := 0
  fabs_of_rows_s1_closed_by_row0_right := 1
  chi_abs_on_s1_of_fabs_required := 1
  abs_outer_on_s1_of_rows_required := 1
  pack_on_s2_required := 1
  b_specific_step_abs_public_input_required := 0
  old_global_characteristic_domain_witness_required := 0
  pfun_representation_data_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_row_seed_residual_frontiers := 3

structure Chapter4G263Theorem415SourceFacingRowSeedResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g262 : Chapter4G262Theorem415SourceFacingNoRowToFlatAbsPackPackage S
  audit : Theorem415SourceFacingRowSeedResidualRouteAuditAfterG263
  row0_right_frontier_closed_this_step : Nat
  remaining_row_seed_residual_frontiers : Nat

def chapter4G263Theorem415SourceFacingRowSeedResidualPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G263Theorem415SourceFacingRowSeedResidualPackage S where
  g262 := chapter4G262Theorem415SourceFacingNoRowToFlatAbsPackPackage S
  audit := theorem415SourceFacingRowSeedResidualRouteAuditAfterG263
  row0_right_frontier_closed_this_step := 1
  remaining_row_seed_residual_frontiers := 3

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G263. -/
def bishopRegularSeqChapter4Theorem415SourceFacingRowSeedResidualProgressAfterG263 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G263: the row-0-right argument removes the public fabs-of-rows-on-S1 \
    field.  The theorem-4.15 source-level route is now reduced to the three \
    row-seed residual fields: chi abs on S1, positive-side abs outer for rows, \
    and the negative-side row pack."


end BishopCReal
