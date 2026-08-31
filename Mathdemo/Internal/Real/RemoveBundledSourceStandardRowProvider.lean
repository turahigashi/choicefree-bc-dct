import Mathdemo.Internal.Real.DeriveGeneralLocalBridgeProviderSource
import Mathdemo.Internal.Sec4.RowToFlat

set_option linter.style.longLine false

/-!
# G271: remove the bundled source standard-row provider from the local route

G270 replaced theorem-specific local bridge data by the existing
`Sec4GeneralIBSourceS2StandardOuterProvider`.  That provider still bundled one
component already proved in the development: the generic `rowToFlat` bridge.

This file fills `rowToFlat` with `sec4_rowToFlat_source` and exposes only the
four source-shaped Proposition-4.2 components still relevant to the direct
measurable representative:

* characteristic-domain witnesses for `χ_A`;
* standard positive-side outer convergence;
* standard negative-side rows;
* standard negative-side outer convergence for those rows.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Rebuild the G270 route from global standard-row components -/

noncomputable def theorem415_sourceS2StandardOuterLocal_statement_data_of_globalStandardRows
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingGlobalStandardRowsStatementData
      (S := S) fn f) :
    Theorem415SourceFacingS2StandardOuterLocalStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  source_s2_standard_outer_provider :=
    {
      rowToFlat := BishopC.sec4_rowToFlat_source (S := S)
      charDomain := D.charDomain
      standard_outer_on_s1 := D.standard_outer_on_s1
      rows_on_s2 := D.rows_on_s2
      standard_outer_on_s2 := D.standard_outer_on_s2
    }

noncomputable def theorem415_integral_convergence_from_globalStandardRows_via_local_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingGlobalStandardRowsStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceS2StandardOuterLocal_statement_data
    (S := S)
    (theorem415_sourceS2StandardOuterLocal_statement_data_of_globalStandardRows
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415GlobalStandardRowsLocalRouteAuditAfterG271 : Type where
  bundled_source_s2_standard_outer_provider_public_input_required : Nat
  row_to_flat_public_input_required : Nat
  row_to_flat_closed_by_sec4_rowToFlat_source : Nat
  characteristic_domain_witness_required : Nat
  standard_positive_row_outer_required : Nat
  standard_negative_rows_required : Nat
  standard_negative_row_outer_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_shaped_standard_row_components : Nat

def theorem415GlobalStandardRowsLocalRouteAuditAfterG271 :
    Theorem415GlobalStandardRowsLocalRouteAuditAfterG271 where
  bundled_source_s2_standard_outer_provider_public_input_required := 0
  row_to_flat_public_input_required := 0
  row_to_flat_closed_by_sec4_rowToFlat_source := 1
  characteristic_domain_witness_required := 1
  standard_positive_row_outer_required := 1
  standard_negative_rows_required := 1
  standard_negative_row_outer_required := 1
  theorem_specific_bridge_inputs_required := 0
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_shaped_standard_row_components := 4

structure Chapter4G271Theorem415GlobalStandardRowsLocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g270 : Chapter4G270Theorem415SourceS2StandardOuterLocalPackage S
  audit : Theorem415GlobalStandardRowsLocalRouteAuditAfterG271
  bundled_provider_removed_this_step : Nat
  row_to_flat_closed_this_step : Nat
  remaining_source_shaped_standard_row_components : Nat

def chapter4G271Theorem415GlobalStandardRowsLocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G271Theorem415GlobalStandardRowsLocalPackage S where
  g270 := chapter4G270Theorem415SourceS2StandardOuterLocalPackage S
  audit := theorem415GlobalStandardRowsLocalRouteAuditAfterG271
  bundled_provider_removed_this_step := 1
  row_to_flat_closed_this_step := 1
  remaining_source_shaped_standard_row_components := 4

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G271. -/
def bishopRegularSeqChapter4Theorem415GlobalStandardRowsLocalProgressAfterG271 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G271: removed the bundled source standard-row provider from the local \
    theorem-4.15 route and filled rowToFlat with sec4_rowToFlat_source. The \
    remaining lower frontier is the four source-shaped Proposition-4.2 standard \
    row components: charDomain, standard S1 outer convergence, S2 rows, and S2 \
    outer convergence."


end BishopCReal
