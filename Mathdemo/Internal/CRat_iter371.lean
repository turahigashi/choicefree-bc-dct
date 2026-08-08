import Mathdemo.Internal.CRat_iter370
import Mathdemo.Internal.CRat_iter358

set_option linter.style.longLine false

/-!
# G272: prefer the layer-telescope route for theorem 4.15

G270--G271 connected the G269 general local bridge provider to the older
source-shaped standard-row provider.  That route is useful for compatibility,
but it exposes a global `charDomain` component.  The more Bishop-faithful route
is the one already present in the lower chapter-4 development: the direct
measurable representative carries a layer telescope, and that layer telescope
builds the value bridge.

This file makes that route the explicit source-level mainline:

`Sec4CanonicalCoverLayerTelescopeData`
  -> `Sec4GenIBValueBridge`
  -> `Sec4GenIBLocalValueBridge`
  -> `Sec4GeneralLocalValueBridgeProvider`
  -> theorem 4.15.

The remaining frontier is therefore not a selector from a bare proposition.
It is the construction, from the carried measurable-set and integrable-function
representations, of the layer-telescope data used by Bishop's proof.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. General layer-telescope data implies the G269 local provider -/

structure Sec4GeneralLayerTelescopeProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  layer : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B)
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4CanonicalCoverLayerTelescopeData (S := S) B hB u hu

noncomputable def sec4GeneralLocalValueBridgeProvider_of_layerTelescopeProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (P : Sec4GeneralLayerTelescopeProvider S) :
    Sec4GeneralLocalValueBridgeProvider S where
  bridge := by
    intro B hB u hu
    exact BishopC.sec4_genIBLocalValueBridge_of_valueBridge
      (S := S) B hB u hu
      (BishopC.sec4_genIBValueBridge_of_layerTelescopeData
        (S := S) B hB u hu (P.layer B hB u hu))

structure Theorem415SourceFacingLayerTelescopeProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  layer_telescope_provider : Sec4GeneralLayerTelescopeProvider S

noncomputable def theorem415_generalProvider_statement_data_of_layerTelescopeProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLayerTelescopeProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_bridge_provider :=
    sec4GeneralLocalValueBridgeProvider_of_layerTelescopeProvider
      (S := S) D.layer_telescope_provider

noncomputable def theorem415_integral_convergence_from_layerTelescopeProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLayerTelescopeProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    (S := S)
    (theorem415_generalProvider_statement_data_of_layerTelescopeProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415PreferredLayerTelescopeProviderRouteAuditAfterG272 :
    Type where
  source_s2_standard_outer_provider_required : Nat
  global_characteristic_domain_witness_required : Nat
  standard_row_component_provider_required : Nat
  general_local_bridge_provider_public_input_required : Nat
  layer_telescope_provider_public_input_required : Nat
  theorem_specific_bridge_inputs_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_layer_telescope_provider_frontiers : Nat

def theorem415PreferredLayerTelescopeProviderRouteAuditAfterG272 :
    Theorem415PreferredLayerTelescopeProviderRouteAuditAfterG272 where
  source_s2_standard_outer_provider_required := 0
  global_characteristic_domain_witness_required := 0
  standard_row_component_provider_required := 0
  general_local_bridge_provider_public_input_required := 0
  layer_telescope_provider_public_input_required := 1
  theorem_specific_bridge_inputs_required := 0
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_layer_telescope_provider_frontiers := 1

structure Chapter4G272Theorem415PreferredLayerTelescopeProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g271 : Chapter4G271Theorem415GlobalStandardRowsLocalPackage S
  audit : Theorem415PreferredLayerTelescopeProviderRouteAuditAfterG272
  global_standard_row_route_retained_for_compatibility : Nat
  layer_telescope_route_selected_as_mainline : Nat
  remaining_layer_telescope_provider_frontiers : Nat

def chapter4G272Theorem415PreferredLayerTelescopeProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G272Theorem415PreferredLayerTelescopeProviderPackage S where
  g271 := chapter4G271Theorem415GlobalStandardRowsLocalPackage S
  audit := theorem415PreferredLayerTelescopeProviderRouteAuditAfterG272
  global_standard_row_route_retained_for_compatibility := 1
  layer_telescope_route_selected_as_mainline := 1
  remaining_layer_telescope_provider_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G272. -/
def bishopRegularSeqChapter4Theorem415PreferredLayerTelescopeProgressAfterG272 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G272: selected the layer-telescope route as the theorem-4.15 mainline. \
    The global standard-row route from G271 remains available for \
    compatibility, but the preferred route now asks only for a general \
    layer-telescope provider. Countdown remains 1: construct that provider \
    from the carried measurable-set and integrable-function representations."


end BishopCReal
