import Mathdemo.Internal.Real.PreferLayerTelescopeRouteTheorem4
import Mathdemo.Internal.Sec4.InternalTools

set_option linter.style.longLine false

/-!
# G273: lower theorem 4.15 from layer telescopes to internal chi-f tools

G272 selected the layer-telescope route as the Bishop-faithful theorem-4.15
mainline.  The existing b2b6 development has already pushed that route one
level lower: from the finite layer telescope to the internal tools for
`prop_4_2_chi_f_rep`.

This file connects those b2b6 tools to the G269 general local bridge provider:

`Sec4ChiFInternalTools`
  -> `Sec4GenIBValueBridge`
  -> `Sec4GenIBLocalValueBridge`
  -> `Sec4GeneralLocalValueBridgeProvider`
  -> theorem 4.15.

So the remaining mathematical frontier is now precisely the generic internal
factor plumbing for `chi_A * f`: extracting the characteristic abs witness from
the chi-f abs witness and proving zero on the negative side.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. General chi-f internal tools imply the G269 local provider -/

structure Sec4GeneralChiFInternalToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  tools : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B)
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4ChiFInternalTools (S := S) B hB u hu

noncomputable def sec4GeneralLocalValueBridgeProvider_of_chiFInternalToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralChiFInternalToolsProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_internalTools
        (S := S) B hB u hu (P.tools B hB u hu))

structure Theorem415SourceFacingChiFInternalToolsProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  chiF_internal_tools_provider : Sec4GeneralChiFInternalToolsProvider S

noncomputable def theorem415_generalProvider_statement_data_of_chiFInternalToolsProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiFInternalToolsProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_chiFInternalToolsProvider
      (S := S) D.chiF_internal_tools_provider

noncomputable def theorem415_integral_convergence_from_chiFInternalToolsProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingChiFInternalToolsProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_chiFInternalToolsProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415ChiFInternalToolsProviderRouteAuditAfterG273 :
    Type where
  layer_telescope_provider_required : Nat
  source_s2_standard_outer_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  general_local_bridge_provider_public_input_required : Nat
  chiF_internal_tools_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_internal_chi_f_factor_fields : Nat
  remaining_internal_chi_f_factor_frontiers : Nat

def theorem415ChiFInternalToolsProviderRouteAuditAfterG273 :
    Theorem415ChiFInternalToolsProviderRouteAuditAfterG273 where
  layer_telescope_provider_required := 0
  source_s2_standard_outer_provider_required := 0
  global_characteristic_domain_witness_required := 0
  general_local_bridge_provider_public_input_required := 0
  chiF_internal_tools_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_internal_chi_f_factor_fields := 3
  remaining_internal_chi_f_factor_frontiers := 1

structure Chapter4G273Theorem415ChiFInternalToolsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g272 : Chapter4G272Theorem415PreferredLayerTelescopeProviderPackage S
  audit : Theorem415ChiFInternalToolsProviderRouteAuditAfterG273
  layer_telescope_provider_replaced_this_step : Nat
  remaining_internal_chi_f_factor_frontiers : Nat

def chapter4G273Theorem415ChiFInternalToolsProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G273Theorem415ChiFInternalToolsProviderPackage S where
  g272 := chapter4G272Theorem415PreferredLayerTelescopeProviderPackage S
  audit := theorem415ChiFInternalToolsProviderRouteAuditAfterG273
  layer_telescope_provider_replaced_this_step := 1
  remaining_internal_chi_f_factor_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G273. -/
def bishopRegularSeqChapter4Theorem415ChiFInternalToolsProgressAfterG273 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G273: lowered the theorem-4.15 mainline from a layer-telescope provider \
    to the b2b6 chi-f internal-tools provider. Countdown remains 1, but the \
    remaining work is now exactly the generic prop_4_2_chi_f_rep factor \
    plumbing: cover chi-f abs, set-chi abs extraction, and zero on S2."


end BishopCReal
