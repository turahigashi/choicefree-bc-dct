import Mathdemo.Internal.Real.ReduceTheorem415LocalBridges
import Mathdemo.Internal.Sec4.S2StandardOuterProvider

set_option linter.style.longLine false

/-!
# G270: derive the general local bridge provider from the source standard-row provider

G269 exposed one remaining theorem-4.15 frontier: a general local value bridge
for the direct measurable representative `I_B(u)`.

The older chapter-4 development already has a source-shaped standard-row
provider for the same direct representative.  This file connects the two
interfaces:

`Sec4GeneralIBSourceS2StandardOuterProvider`
  -> `Sec4GenIBValueBridge`
  -> `Sec4GenIBLocalValueBridge`
  -> `Sec4GeneralLocalValueBridgeProvider`.

Thus theorem 4.15 no longer asks for a theorem-specific local bridge package,
nor even for the G269 local-provider wrapper.  Its remaining input is the
existing section-4 standard-row provider.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Standard-row provider implies the general local bridge provider -/

noncomputable def sec4GeneralLocalValueBridgeProvider_of_sourceS2StandardOuterProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : BishopC.Sec4GeneralIBSourceS2StandardOuterProvider (S := S)) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_sourceS2StandardOuterProvider
        (S := S) P B hB u hu)

structure Theorem415SourceFacingS2StandardOuterLocalStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  source_s2_standard_outer_provider :
    BishopC.Sec4GeneralIBSourceS2StandardOuterProvider (S := S)

noncomputable def theorem415_generalProvider_statement_data_of_sourceS2StandardOuterProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingS2StandardOuterLocalStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_sourceS2StandardOuterProvider
      (S := S) D.source_s2_standard_outer_provider

noncomputable def theorem415_integral_convergence_from_sourceS2StandardOuterLocal_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingS2StandardOuterLocalStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_sourceS2StandardOuterProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415SourceS2StandardOuterLocalRouteAuditAfterG270 : Type where
  general_local_bridge_provider_public_input_required : Nat
  source_s2_standard_outer_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  row_seed_tools_public_input_required : Nat
  global_value_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_source_standard_row_frontiers : Nat

def theorem415SourceS2StandardOuterLocalRouteAuditAfterG270 :
    Theorem415SourceS2StandardOuterLocalRouteAuditAfterG270 where
  general_local_bridge_provider_public_input_required := 0
  source_s2_standard_outer_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  row_seed_tools_public_input_required := 0
  global_value_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_source_standard_row_frontiers := 1

structure Chapter4G270Theorem415SourceS2StandardOuterLocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g269 : Chapter4G269Theorem415GeneralLocalBridgeProviderPackage S
  audit : Theorem415SourceS2StandardOuterLocalRouteAuditAfterG270
  local_provider_replaced_by_source_standard_provider_this_step : Nat
  remaining_source_standard_row_frontiers : Nat

def chapter4G270Theorem415SourceS2StandardOuterLocalPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G270Theorem415SourceS2StandardOuterLocalPackage S where
  g269 := chapter4G269Theorem415GeneralLocalBridgeProviderPackage S
  audit := theorem415SourceS2StandardOuterLocalRouteAuditAfterG270
  local_provider_replaced_by_source_standard_provider_this_step := 1
  remaining_source_standard_row_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G270. -/
def bishopRegularSeqChapter4Theorem415SourceS2StandardOuterLocalProgressAfterG270 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G270: derived the G269 general local bridge provider from the existing \
    section-4 source-shaped standard-row provider. The theorem-4.15 route now \
    has no theorem-specific bridge, complement, or local-majorant-split inputs. \
    Remaining countdown is still 1, now concentrated in proving the standard-row \
    provider fields from the carried Proposition-4.2/measurable-set \
    representatives."


end BishopCReal
