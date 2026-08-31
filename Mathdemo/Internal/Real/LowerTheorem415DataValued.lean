import Mathdemo.Internal.Real.LowerTheorem415OneStep
import Mathdemo.Internal.Sec4.DataCases

set_option linter.style.longLine false

/-!
# G276: lower theorem 4.15 to data-valued cases

G275 connected theorem 4.15 to the one-step finite-cover assembly
`Sec4CoverChiFStepAbs`.  The b2b12 development proves that this one-step
assembly follows from two data-carrying inputs:

* generic case tools for `chi_A * f`;
* data-valued (`PSum`) S1/S2 dichotomies for the current cover and the
  difference layer.

This file exposes that b2b12 route on the theorem-4.15 surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Data-valued cases imply the G269 local provider -/

structure Sec4GeneralDataCasesProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  chiF_case_tools : forall
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4ChiFCaseToolsData (S := S) u hu
  cover_dichotomy : forall
    (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B)
    (u : BishopC.IntegrableRep S),
      BishopC.Sec4CoverDichotomyData (S := S) B hB u

noncomputable def sec4GeneralLocalValueBridgeProvider_of_dataCasesProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralDataCasesProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_dataCases
        (S := S) B hB u hu
        (P.chiF_case_tools u hu)
        (P.cover_dichotomy B hB u))

structure Theorem415SourceFacingDataCasesProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  data_cases_provider : Sec4GeneralDataCasesProvider S

noncomputable def theorem415_generalProvider_statement_data_of_dataCasesProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingDataCasesProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_dataCasesProvider
      (S := S) D.data_cases_provider

noncomputable def theorem415_integral_convergence_from_dataCasesProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingDataCasesProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_dataCasesProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415DataCasesProviderRouteAuditAfterG276 : Type where
  cover_chiF_step_abs_provider_required : Nat
  prop42_final_tools_provider_required : Nat
  chiF_internal_tools_provider_required : Nat
  layer_telescope_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  general_local_bridge_provider_public_input_required : Nat
  data_cases_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_chiF_case_tool_fields : Nat
  remaining_cover_dichotomy_fields : Nat
  remaining_data_case_frontiers : Nat

def theorem415DataCasesProviderRouteAuditAfterG276 :
    Theorem415DataCasesProviderRouteAuditAfterG276 where
  cover_chiF_step_abs_provider_required := 0
  prop42_final_tools_provider_required := 0
  chiF_internal_tools_provider_required := 0
  layer_telescope_provider_required := 0
  global_characteristic_domain_witness_required := 0
  general_local_bridge_provider_public_input_required := 0
  data_cases_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_chiF_case_tool_fields := 3
  remaining_cover_dichotomy_fields := 2
  remaining_data_case_frontiers := 1

structure Chapter4G276Theorem415DataCasesProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g275 : Chapter4G275Theorem415CoverChiFStepAbsProviderPackage S
  audit : Theorem415DataCasesProviderRouteAuditAfterG276
  step_abs_provider_replaced_this_step : Nat
  remaining_data_case_frontiers : Nat

def chapter4G276Theorem415DataCasesProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G276Theorem415DataCasesProviderPackage S where
  g275 := chapter4G275Theorem415CoverChiFStepAbsProviderPackage S
  audit := theorem415DataCasesProviderRouteAuditAfterG276
  step_abs_provider_replaced_this_step := 1
  remaining_data_case_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G276. -/
def bishopRegularSeqChapter4Theorem415DataCasesProgressAfterG276 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G276: lowered theorem 4.15 from one-step cover assembly to data-valued \
    cases. The remaining frontier is to build the generic chi-f case tools and \
    the cover/difference PSum dichotomies from the carried definitions; no \
    Prop-to-Type selector or external choice was introduced."


end BishopCReal
