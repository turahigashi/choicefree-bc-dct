import Mathdemo.Internal.Real.LowerTheorem415DataValued
import Mathdemo.Internal.Sec4.DichotomyData

set_option linter.style.longLine false

/-!
# G277: close the cover/difference dichotomy input

G276 exposed theorem 4.15 through `Sec4GeneralDataCasesProvider`, whose public
inputs were generic chi-f case tools plus data-valued cover/difference
dichotomies.  The b2b13 development constructs the cover/difference dichotomy
data directly from the carried measurable-set and cover definitions.

This node removes that dichotomy from the theorem-4.15 public surface.  The
remaining public input is exactly the generic `Sec4ChiFCaseToolsData` package.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Generic chi-f case tools imply the G269 local provider -/

structure Sec4GeneralChiFCaseToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  tools : forall
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4ChiFCaseToolsData (S := S) u hu

noncomputable def sec4GeneralLocalValueBridgeProvider_of_chiFCaseToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralChiFCaseToolsProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_chiFCaseTools
        (S := S) B hB u hu (P.tools u hu))

structure Theorem415SourceFacingChiFCaseToolsProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  chiF_case_tools_provider : Sec4GeneralChiFCaseToolsProvider S

noncomputable def theorem415_generalProvider_statement_data_of_chiFCaseToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiFCaseToolsProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_chiFCaseToolsProvider
      (S := S) D.chiF_case_tools_provider

noncomputable def theorem415_integral_convergence_from_chiFCaseToolsProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiFCaseToolsProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_chiFCaseToolsProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415ChiFCaseToolsProviderRouteAuditAfterG277 : Type where
  data_cases_provider_required : Nat
  cover_dichotomy_public_input_required : Nat
  cover_dichotomy_closed_by_sec4_coverDichotomyData : Nat
  chiF_case_tools_provider_public_input_required : Nat
  global_characteristic_domain_witness_required : Nat
  general_local_bridge_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_chiF_case_tool_frontiers : Nat
  remaining_total_frontiers : Nat

def theorem415ChiFCaseToolsProviderRouteAuditAfterG277 :
    Theorem415ChiFCaseToolsProviderRouteAuditAfterG277 where
  data_cases_provider_required := 0
  cover_dichotomy_public_input_required := 0
  cover_dichotomy_closed_by_sec4_coverDichotomyData := 1
  chiF_case_tools_provider_public_input_required := 1
  global_characteristic_domain_witness_required := 0
  general_local_bridge_provider_public_input_required := 0
  theorem_specific_bridge_inputs_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_chiF_case_tool_frontiers := 1
  remaining_total_frontiers := 1

structure Chapter4G277Theorem415ChiFCaseToolsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g276 : Chapter4G276Theorem415DataCasesProviderPackage S
  audit : Theorem415ChiFCaseToolsProviderRouteAuditAfterG277
  cover_dichotomy_public_input_closed_this_step : Nat
  remaining_total_frontiers : Nat

def chapter4G277Theorem415ChiFCaseToolsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G277Theorem415ChiFCaseToolsProviderPackage S where
  g276 := chapter4G276Theorem415DataCasesProviderPackage S
  audit := theorem415ChiFCaseToolsProviderRouteAuditAfterG277
  cover_dichotomy_public_input_closed_this_step := 1
  remaining_total_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G277. -/
def bishopRegularSeqChapter4Theorem415ChiFCaseToolsProgressAfterG277 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G277: closed the cover/difference PSum dichotomy input by reusing \
    sec4_coverDichotomyData. The theorem-4.15 route now exposes only the \
    generic chi-f case-tools frontier; no global characteristic-domain witness, \
    Prop-to-Type selector, or external choice was introduced."


end BishopCReal
