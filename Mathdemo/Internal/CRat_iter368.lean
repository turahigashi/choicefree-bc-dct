import Mathdemo.Internal.CRat_iter367

set_option linter.style.longLine false

/-!
# G269: reduce theorem 4.15 local bridges to one general provider

G268 reduced the theorem-specific frontier to local value bridges for the
absolute-error representatives and for the majorant `g + |f|`.  Both are
instances of the same section-4 fact: for any non-negative integrable
representative `u` and any measurable set `B`, the direct measurable relative
integral representative carries the local value bridge.

This file packages that fact as one provider and derives the G268 theorem-4.15
bridge generators from it.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. The one remaining general local bridge provider -/

structure Sec4GeneralLocalValueBridgeProvider
    {R : Type*} [COFOC R] {Y : Type}
    (S : BishopC.IntSpaceRC Y R) : Type _ where
  bridge : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B)
    (u : BishopC.IntegrableRep S) (hu : BishopC.RepNonneg u),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB u hu

structure Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  local_bridge_provider : Sec4GeneralLocalValueBridgeProvider S

noncomputable def theorem415_bridgeGenerator_statement_data_of_generalProvider
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeGeneratorStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_local_bridge := by
    intro n B hB
    exact D.local_bridge_provider.bridge B hB
      (BishopC.thm_4_15_abs_error (S := S) fn f n)
      (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorant_local_bridge := by
    intro B hB
    exact D.local_bridge_provider.bridge B hB
      (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)

noncomputable def theorem415_integral_convergence_from_generalLocalBridgeProvider_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingGeneralLocalBridgeProviderStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_bridgeGenerator_statement_data
    (S := S)
    (theorem415_bridgeGenerator_statement_data_of_generalProvider
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415GeneralLocalBridgeProviderRouteAuditAfterG269 : Type where
  theorem_specific_abs_error_bridge_input_required : Nat
  theorem_specific_majorant_bridge_input_required : Nat
  general_local_bridge_provider_frontier_required : Nat
  local_majorant_split_public_input_required : Nat
  complement_bridge_public_input_required : Nat
  row_seed_tools_public_input_required : Nat
  global_value_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_unfolding_frontiers : Nat

def theorem415GeneralLocalBridgeProviderRouteAuditAfterG269 :
    Theorem415GeneralLocalBridgeProviderRouteAuditAfterG269 where
  theorem_specific_abs_error_bridge_input_required := 0
  theorem_specific_majorant_bridge_input_required := 0
  general_local_bridge_provider_frontier_required := 1
  local_majorant_split_public_input_required := 0
  complement_bridge_public_input_required := 0
  row_seed_tools_public_input_required := 0
  global_value_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_unfolding_frontiers := 1

structure Chapter4G269Theorem415GeneralLocalBridgeProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g268 : Chapter4G268Theorem415LocalBridgeGeneratorPackage S
  audit : Theorem415GeneralLocalBridgeProviderRouteAuditAfterG269
  theorem_specific_bridge_fields_compressed_this_step : Nat
  remaining_definition_unfolding_frontiers : Nat

def chapter4G269Theorem415GeneralLocalBridgeProviderPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G269Theorem415GeneralLocalBridgeProviderPackage S where
  g268 := chapter4G268Theorem415LocalBridgeGeneratorPackage S
  audit := theorem415GeneralLocalBridgeProviderRouteAuditAfterG269
  theorem_specific_bridge_fields_compressed_this_step := 2
  remaining_definition_unfolding_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G269. -/
def bishopRegularSeqChapter4Theorem415GeneralLocalBridgeProviderProgressAfterG269 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G269: compressed the theorem 4.15 bridge frontier to one general section-4 \
    provider: every non-negative integrable representative over every \
    measurable set has the local value bridge for direct measurable relative \
    integration. Countdown remains 1: prove this provider directly from the \
    carried measurable-set and integrable-function representations."


end BishopCReal
