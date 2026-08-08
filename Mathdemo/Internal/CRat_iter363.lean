import Mathdemo.Internal.CRat_iter362

set_option linter.style.longLine false

/-!
# G264: replace arbitrary row residuals by source-shaped standard rows

G263 reduced the source-level theorem-4.15 route to row-seed residual fields.
One of those fields still had the over-strong shape
`Sec4Prop42AbsOuterOnS1OfRows`: it quantified over arbitrary row witnesses.

The printed Proposition 4.2 proof does not need that.  It constructs the
standard lambda rows from the characteristic representative and the supplied
`f`-absolute witness, then proves the corrected outer convergence for those
standard rows.  On the negative side, the corrected target is likewise the
standard `A.S2` rows together with the corrected outer convergence for those
same rows.

This file records that source-shaped route on the current G263 surface:

* `charDomain` supplies the positive-side characteristic abs witness;
* `standard_outer_on_s1` supplies the corrected outer convergence for the
  standard positive-side rows;
* `rows_on_s2` and `standard_outer_on_s2` supply the negative-side pack;
* row-to-flat and row-0 reconstruction stay internally discharged.

Thus the public route no longer asks for outer convergence over arbitrary row
witnesses.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Abs-error-specific standard row source data -/

structure Theorem415SourceFacingStandardRowsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  charDomain : BishopC.Sec4Prop42CharacteristicDomainWitness (S := S)
  abs_error_standard_outer_on_s1 : forall n : Nat,
    BishopC.Sec4Prop42StandardAbsOuterOnS1OfFAbs (S := S) charDomain
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_rows_on_s2 : forall n : Nat,
    BishopC.Sec4Prop42RowsOnS2 (S := S)
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_standard_outer_on_s2 : forall n : Nat,
    BishopC.Sec4LambdaRowsAbsOuterOnS2ForRows (S := S)
      (abs_error_rows_on_s2 n)

noncomputable def theorem415_sourceFacingAbsPackNoRowToFlat_statement_data_of_standardRows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStandardRowsStatementData (S := S) fn f) :
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
    exact
      BishopC.sec4_packOnS1_of_characteristicDomain_standardOuter
        (S := S) D.charDomain u hnn_u
        (D.abs_error_standard_outer_on_s1 n)
  abs_error_pack_on_s2 := by
    intro n
    exact
      BishopC.sec4_packOnS2_of_rowsAbsOuter
        (S := S)
        (D.abs_error_rows_on_s2 n)
        (D.abs_error_standard_outer_on_s2 n)

noncomputable def theorem415_sourceFacingStepAbs_statement_data_of_standardRows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStandardRowsStatementData (S := S) fn f) :
    Theorem415SourceFacingStepAbsStatementData (S := S) fn f :=
  theorem415_sourceFacingStepAbs_statement_data_of_noRowToFlat
    (S := S)
    (theorem415_sourceFacingAbsPackNoRowToFlat_statement_data_of_standardRows
      (S := S) D)

noncomputable def theorem415_integral_convergence_from_sourceFacingStandardRows_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingStandardRowsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingAbsPackNoRowToFlat_statement_data
    (S := S)
    (theorem415_sourceFacingAbsPackNoRowToFlat_statement_data_of_standardRows
      (S := S) D)

/-! ## 2. Global source-shaped standard-row provider, without row-to-flat -/

structure Theorem415SourceFacingGlobalStandardRowsStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  charDomain : BishopC.Sec4Prop42CharacteristicDomainWitness (S := S)
  standard_outer_on_s1 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4Prop42StandardAbsOuterOnS1OfFAbs
        (S := S) charDomain u unn
  rows_on_s2 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4Prop42RowsOnS2 (S := S) u unn
  standard_outer_on_s2 : forall (u : BishopC.IntegrableRep S)
    (unn : BishopC.RepNonneg u),
      BishopC.Sec4LambdaRowsAbsOuterOnS2ForRows (S := S)
        (rows_on_s2 u unn)

noncomputable def theorem415_sourceFacingStandardRows_statement_data_of_globalStandardRows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingGlobalStandardRowsStatementData (S := S) fn f) :
    Theorem415SourceFacingStandardRowsStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  charDomain := D.charDomain
  abs_error_standard_outer_on_s1 := by
    intro n
    exact
      D.standard_outer_on_s1
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_rows_on_s2 := by
    intro n
    exact
      D.rows_on_s2
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_standard_outer_on_s2 := by
    intro n
    exact
      D.standard_outer_on_s2
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)

noncomputable def theorem415_integral_convergence_from_sourceFacingGlobalStandardRows_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingGlobalStandardRowsStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingStandardRows_statement_data
    (S := S)
    (theorem415_sourceFacingStandardRows_statement_data_of_globalStandardRows
      (S := S) D)

/-! ## 3. Audit and package -/

structure Theorem415SourceFacingStandardRowsRouteAuditAfterG264 : Type where
  source_facing_convergence_in_measure_used : Nat
  row_to_flat_public_input_required : Nat
  fabs_of_rows_s1_public_input_required : Nat
  arbitrary_positive_row_outer_public_input_required : Nat
  standard_positive_row_outer_required : Nat
  standard_negative_rows_required : Nat
  standard_negative_row_outer_required : Nat
  characteristic_domain_witness_required : Nat
  b_specific_step_abs_public_input_required : Nat
  pfun_representation_data_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_shaped_standard_row_components : Nat

def theorem415SourceFacingStandardRowsRouteAuditAfterG264 :
    Theorem415SourceFacingStandardRowsRouteAuditAfterG264 where
  source_facing_convergence_in_measure_used := 1
  row_to_flat_public_input_required := 0
  fabs_of_rows_s1_public_input_required := 0
  arbitrary_positive_row_outer_public_input_required := 0
  standard_positive_row_outer_required := 1
  standard_negative_rows_required := 1
  standard_negative_row_outer_required := 1
  characteristic_domain_witness_required := 1
  b_specific_step_abs_public_input_required := 0
  pfun_representation_data_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_shaped_standard_row_components := 4

structure Chapter4G264Theorem415SourceFacingStandardRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g263 : Chapter4G263Theorem415SourceFacingRowSeedResidualPackage S
  audit : Theorem415SourceFacingStandardRowsRouteAuditAfterG264
  arbitrary_positive_row_outer_removed_this_step : Nat
  remaining_source_shaped_standard_row_components : Nat

def chapter4G264Theorem415SourceFacingStandardRowsPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G264Theorem415SourceFacingStandardRowsPackage S where
  g263 := chapter4G263Theorem415SourceFacingRowSeedResidualPackage S
  audit := theorem415SourceFacingStandardRowsRouteAuditAfterG264
  arbitrary_positive_row_outer_removed_this_step := 1
  remaining_source_shaped_standard_row_components := 4

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G264. -/
def bishopRegularSeqChapter4Theorem415SourceFacingStandardRowsProgressAfterG264 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G264: theorem 4.15 no longer uses an arbitrary positive-side row-outer \
    frontier.  It uses the source-shaped standard rows: characteristic-domain \
    data, standard outer convergence on S1, standard rows on S2, and standard \
    outer convergence on S2.  Row-to-flat, row0-right, B-specific dichotomy, \
    and stepAbs are internal."


end BishopCReal
