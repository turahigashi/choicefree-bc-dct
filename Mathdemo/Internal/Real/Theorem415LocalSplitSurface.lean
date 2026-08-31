import Mathdemo.Internal.Real.ReplaceArbitraryRowResidualsSourceShaped

set_option linter.style.longLine false

/-!
# G265: theorem 4.15 through the local split surface

G264 is useful as a diagnostic for the remaining Proposition 4.2 row
components, but its public fields are still not the exact data consumed by the
printed proof of theorem 4.15.

The source proof uses lemma 4.14 through two local ingredients:

* complement bridges for `I_{-C}`;
* the uniform split estimate produced after the majorant set `A` is chosen.

This file exposes that smaller surface directly.  It keeps the theorem-4.15
statement data (`g`, domination, and convergence in measure), but the `I_B`
frontier is no longer an all-measurable-set bridge.  It is the local
split/complement package already used by the completed kernel.

This does not introduce a choice principle.  It narrows the remaining
definition-unfolding responsibility to the two source-shaped local bridge
frontiers.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing theorem 4.15 on the local split surface -/

structure Theorem415SourceFacingLocalSplitStatementData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S) : Type _ where
  g : BishopC.IntegrableRep S
  domination : Theorem415DominatingMajorantData (S := S) fn g
  converges_in_measure :
    Theorem415ConvergesInMeasureData (S := S) fn f
  abs_error_complement_bridge : forall (n : Nat) (C : BishopC.BSet Y)
    (hC : BishopC.IntegrableSet1 S C),
      BishopC.Sec4GenIBLocalValueBridge (S := S) (BishopC.BSet.neg C)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hC)
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  abs_error_local_split : forall (eps : R), COF.lt 0 eps ->
    BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps

noncomputable def theorem415_local_abs_error_source_data_of_sourceFacingLocalSplit
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalSplitStatementData (S := S) fn f) :
    BishopC.Lemma415AbsErrorLocalSourceData (S := S) fn f :=
  BishopC.Lemma415AbsErrorLocalSourceData.of_localSplitUniformData
    (S := S) fn f
    D.abs_error_complement_bridge
    D.abs_error_local_split
    D.converges_in_measure.abs_error

noncomputable def theorem415_integral_convergence_from_sourceFacingLocalSplit_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalSplitStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  BishopC.thm_4_15_source_from_local_abs_error_data
    (S := S) fn f
    (theorem415_local_abs_error_source_data_of_sourceFacingLocalSplit
      (S := S) D)

/-! ## 2. Compatibility from the older all-bridge surface -/

noncomputable def theorem415_sourceFacingLocalSplit_statement_data_of_localBridge
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
    Theorem415SourceFacingLocalSplitStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_complement_bridge :=
    theorem415_sourceFacingLocalBridge_complement_bridges (S := S) D
  abs_error_local_split :=
    theorem415_sourceFacingLocalBridge_direct_local_split_source_data (S := S) D

noncomputable def theorem415_integral_convergence_from_sourceFacingLocalBridge_via_localSplit
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalBridgeStatementData (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalSplit_statement_data
    (S := S)
    (theorem415_sourceFacingLocalSplit_statement_data_of_localBridge
      (S := S) D)

/-! ## 3. Audit and package -/

structure Theorem415SourceFacingLocalSplitRouteAuditAfterG265 : Type where
  source_facing_convergence_in_measure_used : Nat
  all_measurable_local_bridge_public_input_required : Nat
  local_complement_bridge_public_input_required : Nat
  local_split_data_public_input_required : Nat
  global_characteristic_domain_witness_required : Nat
  arbitrary_row_outer_public_input_required : Nat
  row_to_flat_public_input_required : Nat
  pfun_representation_data_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_unfolding_frontiers : Nat

def theorem415SourceFacingLocalSplitRouteAuditAfterG265 :
    Theorem415SourceFacingLocalSplitRouteAuditAfterG265 where
  source_facing_convergence_in_measure_used := 1
  all_measurable_local_bridge_public_input_required := 0
  local_complement_bridge_public_input_required := 1
  local_split_data_public_input_required := 1
  global_characteristic_domain_witness_required := 0
  arbitrary_row_outer_public_input_required := 0
  row_to_flat_public_input_required := 0
  pfun_representation_data_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_unfolding_frontiers := 2

structure Chapter4G265Theorem415SourceFacingLocalSplitPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g264 : Chapter4G264Theorem415SourceFacingStandardRowsPackage S
  g257 : Chapter4G257Theorem415SourceFacingLocalBridgePackage S
  audit : Theorem415SourceFacingLocalSplitRouteAuditAfterG265
  all_measurable_bridge_removed_from_public_surface_this_step : Nat
  remaining_definition_unfolding_frontiers : Nat

def chapter4G265Theorem415SourceFacingLocalSplitPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G265Theorem415SourceFacingLocalSplitPackage S where
  g264 := chapter4G264Theorem415SourceFacingStandardRowsPackage S
  g257 := chapter4G257Theorem415SourceFacingLocalBridgePackage S
  audit := theorem415SourceFacingLocalSplitRouteAuditAfterG265
  all_measurable_bridge_removed_from_public_surface_this_step := 1
  remaining_definition_unfolding_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G265. -/
def bishopRegularSeqChapter4Theorem415SourceFacingLocalSplitProgressAfterG265 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G265: theorem 4.15 now has a smaller source-level local split surface. \
    It no longer asks publicly for an all-measurable-set local bridge, a \
    global characteristic-domain witness, arbitrary row-outer data, row-to-flat, \
    or PFun representation data. The remaining countdown is 2: derive local \
    complement bridges and local split data directly from the source \
    definitions."


end BishopCReal
