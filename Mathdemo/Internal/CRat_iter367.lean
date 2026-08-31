import Mathdemo.Internal.CRat_iter366

set_option linter.style.longLine false

/-!
# G268: build the local majorant split from local bridge generators

G267 removed the separate complement bridge.  The remaining public frontier was
the full local majorant split package.  This file opens that package one layer:
the set selection, epsilon budget, delta, and majorant smallness estimates are
now constructed from the existing source lemmas.  What remains is the genuinely
local definitional frontier: producing the local value bridges for the direct
measurable relative integral from the carried representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Small local atoms -/

theorem repNonneg_sub_self_from_definition
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (r : BishopC.IntegrableRep S) :
    BishopC.RepNonneg (r.sub r) := by
  intro x hsubDom habs hx
  let hleftDom : r.MemAt x := BishopC.add_dom_left hsubDom
  let hrightNegDom : r.neg.MemAt x := BishopC.add_dom_right hsubDom
  let hrightDom : r.MemAt x := BishopC.neg_dom hrightNegDom
  have hleft_abs :
      RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hleftDom n)) := by
    simpa only [hleftDom, BishopC.IntegrableRep.sub] using
      (BishopC.add_absSeriesSum_left
        (r := r) (r' := r.neg) (x := x) hsubDom habs)
  have hright_neg_abs :
      RSeq.SeriesSum
        (fun n => COF.abs (r.neg.valueAt x hrightNegDom n)) := by
    simpa only [hrightNegDom, BishopC.IntegrableRep.sub] using
      (BishopC.add_absSeriesSum_right
        (r := r) (r' := r.neg) (x := x) hsubDom habs)
  have hright_abs :
      RSeq.SeriesSum (fun n => COF.abs (r.valueAt x hrightDom n)) := by
    simpa only [hrightDom] using
      BishopC.neg_absSeriesSum hrightNegDom hright_neg_abs
  let hleft_sum : RSeq.SeriesSum (fun n => r.valueAt x hleftDom n) :=
    BishopC.seriesSum_of_abs hleft_abs
  let hright_sum : RSeq.SeriesSum (fun n => r.valueAt x hrightDom n) :=
    BishopC.seriesSum_of_abs hright_abs
  let hsub_sum :
      RSeq.SeriesSum (fun n => (r.sub r).valueAt x hsubDom n) := by
    simpa only [BishopC.IntegrableRep.sub] using
      (BishopC.add_seriesSum_value hleftDom hrightNegDom hleft_sum
        (BishopC.neg_seriesSum_value hrightDom hright_sum))
  have hx_eq : hx.sum = hsub_sum.sum :=
    BishopC.seriesSum_unique hx hsub_sum
  have hsame : hleft_sum.sum = hright_sum.sum :=
    BishopC.seriesSum_unique hleft_sum hright_sum
  rw [hx_eq]
  change BishopC.Nonneg (hleft_sum.sum + -hright_sum.sum)
  rw [hsame]
  convert BishopC.nonneg_zero (R := R) using 1
  ring

theorem genRelIntegral_from_measurable_le_relIntegral_same_of_localBridge
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
    (u : BishopC.IntegrableRep S) (hnn_u : BishopC.RepNonneg u)
    (Vu : BishopC.Sec4GenIBLocalValueBridge (S := S) C
      (BishopC.isMeasurableSet_of_integrable (S := S) hC) u hnn_u) :
    BishopC.Le
      (BishopC.genRelIntegral_from_measurable C
        (BishopC.isMeasurableSet_of_integrable (S := S) hC) u hnn_u)
      (BishopC.relIntegral C hC u hnn_u) :=
  BishopC.genRelIntegral_from_measurable_le_relIntegral_of_localBridge
    (S := S) C hC u u hnn_u hnn_u Vu
    (repNonneg_sub_self_from_definition (S := S) u)

theorem genRelIntegral_neg_le_complementIntegral_same_of_localBridge
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C)
    (u : BishopC.IntegrableRep S) (hnn_u : BishopC.RepNonneg u)
    (Vu : BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
      (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u) :
    BishopC.Le
      (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC) u hnn_u)
      ((u.sub (BishopC.prop_4_2_chi_f_rep C hC u hnn_u)).integral) :=
  BishopC.genRelIntegral_neg_le_complementIntegral_of_localBridge
    (S := S) C hC u u hnn_u hnn_u Vu
    (repNonneg_sub_self_from_definition (S := S) u)

/-! ## 2. Source data with local bridge generators -/

structure Theorem415SourceFacingLocalBridgeGeneratorStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_local_bridge : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorant_local_bridge : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB
        (g.add f.absVal)
        (theorem415_g_add_absf_majorant_nonneg
          (S := S) f g domination.g_nonneg)

noncomputable def theorem415_sourceFacingLocalBridge_statement_data_of_bridgeGenerator
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeGeneratorStatementData
      (S := S) fn f) :
    Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_local_bridge := D.abs_error_local_bridge

noncomputable def theorem415_localMajorantBridgeSplit_of_bridgeGenerator
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeGeneratorStatementData
      (S := S) fn f)
    (eps : R) (heps : COF.lt 0 eps) :
    Theorem415LocalMajorantBridgeSplitData (S := S) fn f
      (D.g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f D.g D.domination.g_nonneg)
      eps :=
  let majorant : BishopC.IntegrableRep S := D.g.add f.absVal
  let majorant_nonneg : BishopC.RepNonneg majorant :=
    theorem415_g_add_absf_majorant_nonneg
      (S := S) f D.g D.domination.g_nonneg
  let Dlocal : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f :=
    theorem415_sourceFacingLocalBridge_statement_data_of_bridgeGenerator
      (S := S) D
  let M : BishopC.Lemma415MajorantRelChoiceSourceData
      (S := S) fn f majorant majorant_nonneg eps :=
    theorem415_sourceFacingLocalBridge_majorant_rel_choice
      (S := S) Dlocal eps heps
  let H := BishopC.relIntegral_abs_continuous_delta
    (S := S) majorant majorant_nonneg M.epsAB M.epsAB_pos
  {
    A := M.A
    hA := M.hA
    N := M.N
    N_ge_one := M.N_ge_one
    delta := H.1
    delta_pos := H.2.1
    epsAB := M.epsAB
    epsNeg := M.epsNeg
    pieces_sum_lt := M.pieces_sum_lt
    dominatesError := M.dominatesError
    abs_error_local_bridge := D.abs_error_local_bridge
    majorant_local_bridge := D.majorant_local_bridge
    majorantABSmall := by
      intro B hB hmu
      let hABint : BishopC.IntegrableSet1 S (BishopC.BSet.and M.A B) :=
        hB M.A M.hA
      have hrel_small : COF.lt
          (BishopC.relIntegral (BishopC.BSet.and M.A B) hABint
            majorant majorant_nonneg)
          M.epsAB :=
        H.2.2 (BishopC.BSet.and M.A B) hABint hmu
      have hgen_le_rel : BishopC.Le
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and M.A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) hABint)
            majorant majorant_nonneg)
          (BishopC.relIntegral (BishopC.BSet.and M.A B) hABint
            majorant majorant_nonneg) :=
        genRelIntegral_from_measurable_le_relIntegral_same_of_localBridge
          (S := S) (BishopC.BSet.and M.A B) hABint
          majorant majorant_nonneg
          (D.majorant_local_bridge (BishopC.BSet.and M.A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) hABint))
      exact BishopC.lt_of_le_of_lt hgen_le_rel hrel_small
    majorantNegSmall := by
      have hgen_le_comp : BishopC.Le
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg M.A)
            (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA)
            majorant majorant_nonneg)
          ((majorant.sub
            (BishopC.prop_4_2_chi_f_rep M.A M.hA
              majorant majorant_nonneg)).integral) :=
        genRelIntegral_neg_le_complementIntegral_same_of_localBridge
          (S := S) M.A M.hA majorant majorant_nonneg
          (D.majorant_local_bridge (BishopC.BSet.neg M.A)
            (BishopC.isMeasurableSet_neg_of_integrable (S := S) M.hA))
      exact BishopC.lt_of_le_of_lt hgen_le_comp M.majorantNegSmall
  }

noncomputable def theorem415_bridgeSplitNoComplement_statement_data_of_bridgeGenerator
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeGeneratorStatementData
      (S := S) fn f) :
    Theorem415SourceFacingBridgeSplitNoComplementStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  local_majorant_split := by
    intro eps heps
    exact theorem415_localMajorantBridgeSplit_of_bridgeGenerator
      (S := S) D eps heps

noncomputable def theorem415_integral_convergence_from_bridgeGenerator_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeGeneratorStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingBridgeSplitNoComplement_statement_data
    (S := S)
    (theorem415_bridgeSplitNoComplement_statement_data_of_bridgeGenerator
      (S := S) D)

/-! ## 3. Audit and package -/

structure Theorem415LocalBridgeGeneratorRouteAuditAfterG268 : Type where
  source_facing_convergence_in_measure_used : Nat
  full_local_majorant_split_public_input_required : Nat
  local_bridge_generator_package_public_input_required : Nat
  epsilon_budget_and_cover_set_constructed_from_source : Nat
  absolute_continuity_delta_constructed_from_integrable_majorant : Nat
  complement_bridge_public_input_required : Nat
  row_seed_tools_public_input_required : Nat
  global_value_bridge_public_input_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_unfolding_frontiers : Nat

def theorem415LocalBridgeGeneratorRouteAuditAfterG268 :
    Theorem415LocalBridgeGeneratorRouteAuditAfterG268 where
  source_facing_convergence_in_measure_used := 1
  full_local_majorant_split_public_input_required := 0
  local_bridge_generator_package_public_input_required := 1
  epsilon_budget_and_cover_set_constructed_from_source := 1
  absolute_continuity_delta_constructed_from_integrable_majorant := 1
  complement_bridge_public_input_required := 0
  row_seed_tools_public_input_required := 0
  global_value_bridge_public_input_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_unfolding_frontiers := 1

structure Chapter4G268Theorem415LocalBridgeGeneratorPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g267 : Chapter4G267Theorem415BridgeSplitNoComplementPackage S
  audit : Theorem415LocalBridgeGeneratorRouteAuditAfterG268
  local_majorant_split_opened_to_bridge_generators_this_step : Nat
  remaining_definition_unfolding_frontiers : Nat

def chapter4G268Theorem415LocalBridgeGeneratorPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G268Theorem415LocalBridgeGeneratorPackage S where
  g267 := chapter4G267Theorem415BridgeSplitNoComplementPackage S
  audit := theorem415LocalBridgeGeneratorRouteAuditAfterG268
  local_majorant_split_opened_to_bridge_generators_this_step := 1
  remaining_definition_unfolding_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G268. -/
def bishopRegularSeqChapter4Theorem415LocalBridgeGeneratorProgressAfterG268 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G268: opened the last theorem 4.15 local-majorant-split package. The \
    cover set, epsilon budget, delta from absolute continuity, AB-smallness, \
    and complement-smallness are now constructed from source lemmas and local \
    bridges. Countdown remains 1, but the remaining frontier is narrower: \
    derive the abs-error and majorant local value bridges from the \
    measurable/integrable-set representative definitions."


end BishopCReal
