import Mathdemo.Internal.Real.BuildLocalSplitDataBridgeBacked

set_option linter.style.longLine false

/-!
# G267: remove the separate complement-bridge input

G266 still displayed two theorem-4.15 local frontiers:

* complement bridges for `I_{-C}`;
* bridge-backed local majorant split data.

But the second package already contains local bridges for the absolute-error
representatives for every measurable set.  Instantiating it once at the fixed
positive radius `halfPow 0` is enough to recover the complement bridges needed
by lemma 4.14.  This file therefore removes the complement bridge as an
independent public input.

The remaining top-level frontier is now a single one: construct the
bridge-backed local majorant split package from the measurable/integrable-set
definitions and the source majorant estimates.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing data with no separate complement input -/

structure Theorem415SourceFacingBridgeSplitNoComplementStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  local_majorant_split : forall (eps : R), COF.lt 0 eps ->
    Theorem415LocalMajorantBridgeSplitData (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f g domination.g_nonneg)
      eps

noncomputable def theorem415_absErrorComplementBridge_of_bridgeSplitNoComplement
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingBridgeSplitNoComplementStatementData
      (S := S) fn f) :
    forall (n : Nat) (C : BishopC.BSet Y) (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n) :=
  fun n C hC =>
    let eps0 : R := COF.halfPow (R := R) 0
    let heps0 : COF.lt 0 eps0 := BishopC.halfPow_pos (R := R) 0
    let Split := D.local_majorant_split eps0 heps0
    Split.abs_error_local_bridge n
      (BishopC.BSet.neg C)
      (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)

noncomputable def theorem415_sourceFacingLocalMajorantBridgeSplit_statement_data_of_noComplement
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingBridgeSplitNoComplementStatementData
      (S := S) fn f) :
    Theorem415SourceFacingLocalMajorantBridgeSplitStatementData
      (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_complement_bridge :=
    theorem415_absErrorComplementBridge_of_bridgeSplitNoComplement (S := S) D
  local_majorant_split := D.local_majorant_split

noncomputable def theorem415_integral_convergence_from_sourceFacingBridgeSplitNoComplement_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingBridgeSplitNoComplementStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalMajorantBridgeSplit_statement_data
    (S := S)
    (theorem415_sourceFacingLocalMajorantBridgeSplit_statement_data_of_noComplement
      (S := S) D)

/-! ## 2. Audit and package -/

structure Theorem415BridgeSplitNoComplementRouteAuditAfterG267 : Type where
  source_facing_convergence_in_measure_used : Nat
  separate_complement_bridge_public_input_required : Nat
  complement_bridge_recovered_from_split_data : Nat
  bridge_backed_local_majorant_split_public_input_required : Nat
  row_seed_tools_public_input_required : Nat
  global_value_bridge_public_input_required : Nat
  global_characteristic_domain_witness_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_top_level_definition_unfolding_frontiers : Nat

def theorem415BridgeSplitNoComplementRouteAuditAfterG267 :
    Theorem415BridgeSplitNoComplementRouteAuditAfterG267 where
  source_facing_convergence_in_measure_used := 1
  separate_complement_bridge_public_input_required := 0
  complement_bridge_recovered_from_split_data := 1
  bridge_backed_local_majorant_split_public_input_required := 1
  row_seed_tools_public_input_required := 0
  global_value_bridge_public_input_required := 0
  global_characteristic_domain_witness_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_top_level_definition_unfolding_frontiers := 1

structure Chapter4G267Theorem415BridgeSplitNoComplementPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g266 : Chapter4G266Theorem415LocalMajorantBridgeSplitPackage S
  audit : Theorem415BridgeSplitNoComplementRouteAuditAfterG267
  separate_complement_bridge_removed_this_step : Nat
  remaining_top_level_definition_unfolding_frontiers : Nat

def chapter4G267Theorem415BridgeSplitNoComplementPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G267Theorem415BridgeSplitNoComplementPackage S where
  g266 := chapter4G266Theorem415LocalMajorantBridgeSplitPackage S
  audit := theorem415BridgeSplitNoComplementRouteAuditAfterG267
  separate_complement_bridge_removed_this_step := 1
  remaining_top_level_definition_unfolding_frontiers := 1

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G267. -/
def bishopRegularSeqChapter4Theorem415BridgeSplitNoComplementProgressAfterG267 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G267: removed the separate theorem 4.15 complement-bridge input. A fixed \
    positive radius halfPow 0 instantiates the bridge-backed local split data, \
    and its abs-error local bridge field supplies the needed I_{-C} bridges. \
    Top-level countdown is now 1: derive the bridge-backed local majorant \
    split package itself from the measurable/integrable-set definitions and \
    source majorant estimates."


end BishopCReal
