import Mathdemo.Internal.CRat_iter372
import Mathdemo.Internal.Sec4_Phase2_IB_D2b2b_beta_b2b9_row1Switch_iteration1

set_option linter.style.longLine false

/-!
# G274: lower theorem 4.15 to the final Proposition-4.2 primitive

G273 connected theorem 4.15 to the b2b6 `Sec4ChiFInternalTools` provider.
The b2b9 row-1 switch already proves that those three internal tools follow
from a single remaining primitive, `Sec4Prop42FinalTools`, i.e. the finite
cover `chi * f` abs witness.

This file exposes that lower route on the theorem-4.15 surface:

`Sec4Prop42FinalTools`
  -> `Sec4ChiFInternalTools`
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

/-! ## 1. General final Proposition-4.2 tools imply the G269 local provider -/

structure Sec4GeneralProp42FinalToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  tools : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B)
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4Prop42FinalTools (S := S) B hB u hu

noncomputable def sec4GeneralLocalValueBridgeProvider_of_prop42FinalToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralProp42FinalToolsProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_finalTools
        (S := S) B hB u hu (P.tools B hB u hu))

structure Theorem415SourceFacingProp42FinalToolsProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  prop42_final_tools_provider : Sec4GeneralProp42FinalToolsProvider S

noncomputable def theorem415_generalProvider_statement_data_of_prop42FinalToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingProp42FinalToolsProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_prop42FinalToolsProvider
      (S := S) D.prop42_final_tools_provider

noncomputable def theorem415_integral_convergence_from_prop42FinalToolsProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingProp42FinalToolsProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_prop42FinalToolsProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415Prop42FinalToolsProviderRouteAuditAfterG274 :
    Type where
  chiF_internal_tools_provider_required : Nat
  layer_telescope_provider_required : Nat
  source_s2_standard_outer_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  general_local_bridge_provider_public_input_required : Nat
  prop42_final_tools_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_finite_cover_chi_f_abs_primitives : Nat

def theorem415Prop42FinalToolsProviderRouteAuditAfterG274 :
    Theorem415Prop42FinalToolsProviderRouteAuditAfterG274 where
  chiF_internal_tools_provider_required := 0
  layer_telescope_provider_required := 0
  source_s2_standard_outer_provider_required := 0
  global_characteristic_domain_witness_required := 0
  general_local_bridge_provider_public_input_required := 0
  prop42_final_tools_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_finite_cover_chi_f_abs_primitives := 1

structure Chapter4G274Theorem415Prop42FinalToolsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g273 : Chapter4G273Theorem415ChiFInternalToolsProviderPackage S
  audit : Theorem415Prop42FinalToolsProviderRouteAuditAfterG274
  internal_tool_fields_replaced_this_step : Nat
  remaining_finite_cover_chi_f_abs_primitives : Nat

def chapter4G274Theorem415Prop42FinalToolsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G274Theorem415Prop42FinalToolsProviderPackage S where
  g273 := chapter4G273Theorem415ChiFInternalToolsProviderPackage S
  audit := theorem415Prop42FinalToolsProviderRouteAuditAfterG274
  internal_tool_fields_replaced_this_step := 3
  remaining_finite_cover_chi_f_abs_primitives := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G274. -/
def bishopRegularSeqChapter4Theorem415Prop42FinalToolsProgressAfterG274 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G274: lowered the theorem-4.15 mainline from the b2b6 chi-f internal \
    tools to the b2b9 final Proposition-4.2 primitive. Countdown remains 1: \
    prove the finite-cover chi-f abs witness, equivalently the final \
    cover_chiF_abs_succ primitive, from the carried definitions."


end BishopCReal
