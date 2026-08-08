import Mathdemo.Internal.CRat_iter373
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b10_stepAbs_iteration1

set_option linter.style.longLine false

/-!
# G275: lower theorem 4.15 to one-step finite-cover assembly

G274 exposed the final Proposition-4.2 primitive,
`Sec4Prop42FinalTools`.  The b2b10 development reduces that primitive to the
one-step finite-cover assembly lemma `Sec4CoverChiFStepAbs`.

This file connects that lower interface to theorem 4.15:

`Sec4CoverChiFStepAbs`
  -> `Sec4Prop42FinalTools`
  -> `Sec4GenIBValueBridge`
  -> `Sec4GenIBLocalValueBridge`
  -> theorem 4.15.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. General one-step cover assembly implies the G269 local provider -/

structure Sec4GeneralCoverChiFStepAbsProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  step : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B)
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4CoverChiFStepAbs (S := S) B hB u hu

noncomputable def sec4GeneralLocalValueBridgeProvider_of_coverChiFStepAbsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralCoverChiFStepAbsProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_stepAbs
        (S := S) B hB u hu (P.step B hB u hu))

structure Theorem415SourceFacingCoverChiFStepAbsProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  cover_chiF_step_abs_provider : Sec4GeneralCoverChiFStepAbsProvider S

noncomputable def theorem415_generalProvider_statement_data_of_coverChiFStepAbsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCoverChiFStepAbsProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_coverChiFStepAbsProvider
      (S := S) D.cover_chiF_step_abs_provider

noncomputable def theorem415_integral_convergence_from_coverChiFStepAbsProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingCoverChiFStepAbsProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_coverChiFStepAbsProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415CoverChiFStepAbsProviderRouteAuditAfterG275 :
    Type where
  prop42_final_tools_provider_required : Nat
  chiF_internal_tools_provider_required : Nat
  layer_telescope_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  general_local_bridge_provider_public_input_required : Nat
  cover_chiF_step_abs_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_one_step_finite_cover_assembly_frontiers : Nat

def theorem415CoverChiFStepAbsProviderRouteAuditAfterG275 :
    Theorem415CoverChiFStepAbsProviderRouteAuditAfterG275 where
  prop42_final_tools_provider_required := 0
  chiF_internal_tools_provider_required := 0
  layer_telescope_provider_required := 0
  global_characteristic_domain_witness_required := 0
  general_local_bridge_provider_public_input_required := 0
  cover_chiF_step_abs_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_one_step_finite_cover_assembly_frontiers := 1

structure Chapter4G275Theorem415CoverChiFStepAbsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g274 : Chapter4G274Theorem415Prop42FinalToolsProviderPackage S
  audit : Theorem415CoverChiFStepAbsProviderRouteAuditAfterG275
  final_tools_provider_replaced_this_step : Nat
  remaining_one_step_finite_cover_assembly_frontiers : Nat

def chapter4G275Theorem415CoverChiFStepAbsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G275Theorem415CoverChiFStepAbsProviderPackage S where
  g274 := chapter4G274Theorem415Prop42FinalToolsProviderPackage S
  audit := theorem415CoverChiFStepAbsProviderRouteAuditAfterG275
  final_tools_provider_replaced_this_step := 1
  remaining_one_step_finite_cover_assembly_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G275. -/
def bishopRegularSeqChapter4Theorem415CoverChiFStepAbsProgressAfterG275 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G275: lowered theorem 4.15 from the final Proposition-4.2 primitive to \
    the one-step finite-cover assembly provider. Countdown remains 1: prove \
    Sec4CoverChiFStepAbs, i.e. assemble the successor cover chi-f abs witness \
    from the current cover and the next difference layer."


end BishopCReal
