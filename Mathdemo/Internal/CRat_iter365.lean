import Mathdemo.Internal.CRat_iter364

set_option linter.style.longLine false

/-!
# G266: build local split data from bridge-backed majorant estimates

G265 exposed theorem 4.15 at the exact local split/complement surface consumed
by lemma 4.14.  This file opens the `local split` field one layer further.

The source proof of theorem 4.15 proves the split estimate by comparing
`|f_n - f|` with a non-negative majorant and then estimating the two pieces
over `A ∧ B` and `-A`.  The construction below formalizes that step using
local full-set bridges directly, rather than going back through the older
row-seed/global-bridge interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Bridge-backed local majorant split data -/

structure Theorem415LocalMajorantBridgeSplitData
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    (fn : Nat -> BishopC.IntegrableRep S)
    (f : BishopC.IntegrableRep S)
    (majorant : BishopC.IntegrableRep S)
    (majorant_nonneg : BishopC.RepNonneg majorant)
    (eps : R) : Type _ where
  A : BishopC.BSet Y
  hA : BishopC.IntegrableSet1 S A
  N : Nat
  N_ge_one : 1 <= N
  delta : R
  delta_pos : COF.lt 0 delta
  epsAB : R
  epsNeg : R
  pieces_sum_lt : COF.lt (epsAB + epsNeg) eps
  dominatesError : forall n : Nat,
    BishopC.RepNonneg
      (majorant.sub (BishopC.thm_4_15_abs_error (S := S) fn f n))
  abs_error_local_bridge : forall (n : Nat) (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB
        (BishopC.thm_4_15_abs_error (S := S) fn f n)
        (BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n)
  majorant_local_bridge : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      BishopC.Sec4GenIBLocalValueBridge (S := S) B hB
        majorant majorant_nonneg
  majorantABSmall : forall (B : BishopC.BSet Y)
    (hB : BishopC.IsMeasurableSet (S := S) B),
      COF.lt (BishopC.measure1 S (hB A hA)) delta ->
        COF.lt
          (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and A B)
            (BishopC.isMeasurableSet_of_integrable (S := S) (hB A hA))
            majorant majorant_nonneg)
          epsAB
  majorantNegSmall :
    COF.lt
      (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg A)
        (BishopC.isMeasurableSet_neg_of_integrable (S := S) hA)
        majorant majorant_nonneg)
      epsNeg

noncomputable def theorem415_localSplit_of_localMajorantBridgeSplit
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    {majorant : BishopC.IntegrableRep S}
    {majorant_nonneg : BishopC.RepNonneg majorant}
    {eps : R}
    (D : Theorem415LocalMajorantBridgeSplitData
      (S := S) fn f majorant majorant_nonneg eps) :
    BishopC.Lemma415SplitUniformLocalSourceData (S := S) fn f eps where
  A := D.A
  hA := D.hA
  N := D.N
  N_ge_one := D.N_ge_one
  delta := D.delta
  delta_pos := D.delta_pos
  epsAB := D.epsAB
  epsNeg := D.epsNeg
  pieces_sum_lt := D.pieces_sum_lt
  pieceBounds := by
    intro n _hn B hB hmu
    let u : BishopC.IntegrableRep S :=
      BishopC.thm_4_15_abs_error (S := S) fn f n
    let hnn_u : BishopC.RepNonneg u :=
      BishopC.thm_4_15_abs_error_nonneg (S := S) fn f n
    let VB : BishopC.Sec4GenIBLocalValueBridge (S := S) B hB u hnn_u :=
      D.abs_error_local_bridge n B hB
    let hAB : BishopC.IsMeasurableSet (S := S) (BishopC.BSet.and D.A B) :=
      BishopC.isMeasurableSet_of_integrable (S := S) (hB D.A D.hA)
    let hNegA : BishopC.IsMeasurableSet (S := S) (BishopC.BSet.neg D.A) :=
      BishopC.isMeasurableSet_neg_of_integrable (S := S) D.hA
    let VAB : BishopC.Sec4GenIBLocalValueBridge
        (S := S) (BishopC.BSet.and D.A B) hAB u hnn_u :=
      D.abs_error_local_bridge n (BishopC.BSet.and D.A B) hAB
    let VnegA : BishopC.Sec4GenIBLocalValueBridge
        (S := S) (BishopC.BSet.neg D.A) hNegA u hnn_u :=
      D.abs_error_local_bridge n (BishopC.BSet.neg D.A) hNegA
    let VABmajorant : BishopC.Sec4GenIBLocalValueBridge
        (S := S) (BishopC.BSet.and D.A B) hAB
        majorant majorant_nonneg :=
      D.majorant_local_bridge (BishopC.BSet.and D.A B) hAB
    let VnegAmajorant : BishopC.Sec4GenIBLocalValueBridge
        (S := S) (BishopC.BSet.neg D.A) hNegA
        majorant majorant_nonneg :=
      D.majorant_local_bridge (BishopC.BSet.neg D.A) hNegA
    have hAB_le : BishopC.Le
        (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and D.A B)
          hAB u hnn_u)
        (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and D.A B)
          hAB majorant majorant_nonneg) :=
      BishopC.genRelIntegral_from_measurable_mono_integrand_of_localBridges
        (S := S)
        (BishopC.BSet.and D.A B) hAB
        u majorant hnn_u majorant_nonneg
        VAB VABmajorant (D.dominatesError n)
    have hNeg_le : BishopC.Le
        (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg D.A)
          hNegA u hnn_u)
        (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg D.A)
          hNegA majorant majorant_nonneg) :=
      BishopC.genRelIntegral_from_measurable_mono_integrand_of_localBridges
        (S := S)
        (BishopC.BSet.neg D.A) hNegA
        u majorant hnn_u majorant_nonneg
        VnegA VnegAmajorant (D.dominatesError n)
    have hAB_lt : COF.lt
        (BishopC.genRelIntegral_from_measurable (BishopC.BSet.and D.A B)
          hAB u hnn_u)
        D.epsAB :=
      BishopC.lt_of_le_of_lt hAB_le (D.majorantABSmall B hB hmu)
    have hNeg_lt : COF.lt
        (BishopC.genRelIntegral_from_measurable (BishopC.BSet.neg D.A)
          hNegA u hnn_u)
        D.epsNeg :=
      BishopC.lt_of_le_of_lt hNeg_le D.majorantNegSmall
    exact ⟨VB, VAB, VnegA, hAB_lt, hNeg_lt⟩

/-! ## 2. Theorem 4.15 wrapper using bridge-backed majorant split data -/

structure Theorem415SourceFacingLocalMajorantBridgeSplitStatementData
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
  local_majorant_split : forall (eps : R), COF.lt 0 eps ->
    Theorem415LocalMajorantBridgeSplitData (S := S) fn f (g.add f.absVal)
      (theorem415_g_add_absf_majorant_nonneg
        (S := S) f g domination.g_nonneg)
      eps

noncomputable def theorem415_sourceFacingLocalSplit_statement_data_of_localMajorantBridgeSplit
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalMajorantBridgeSplitStatementData
      (S := S) fn f) :
    Theorem415SourceFacingLocalSplitStatementData (S := S) fn f where
  g := D.g
  domination := D.domination
  converges_in_measure := D.converges_in_measure
  abs_error_complement_bridge := D.abs_error_complement_bridge
  abs_error_local_split := by
    intro eps heps
    exact
      theorem415_localSplit_of_localMajorantBridgeSplit
        (S := S) (D.local_majorant_split eps heps)

noncomputable def theorem415_integral_convergence_from_sourceFacingLocalMajorantBridgeSplit_statement_data
    {R : Type*} [COFOC R] {Y : Type}
    {S : BishopC.IntSpaceRC Y R}
    {fn : Nat -> BishopC.IntegrableRep S}
    {f : BishopC.IntegrableRep S}
    (D : Theorem415SourceFacingLocalMajorantBridgeSplitStatementData
      (S := S) fn f) :
    RSeq.TendstoHalf (fun n => (fn n).integral) f.integral :=
  theorem415_integral_convergence_from_sourceFacingLocalSplit_statement_data
    (S := S)
    (theorem415_sourceFacingLocalSplit_statement_data_of_localMajorantBridgeSplit
      (S := S) D)

/-! ## 3. Audit and package -/

structure Theorem415LocalMajorantBridgeSplitRouteAuditAfterG266 : Type where
  source_facing_convergence_in_measure_used : Nat
  opaque_local_split_public_input_required : Nat
  local_majorant_bridge_split_data_required : Nat
  local_complement_bridge_public_input_required : Nat
  row_seed_tools_public_input_required_for_split : Nat
  global_value_bridge_public_input_required_for_split : Nat
  global_characteristic_domain_witness_required : Nat
  prop_to_type_witness_extraction_used : Nat
  external_choice_principle_added : Nat
  remaining_definition_unfolding_frontiers : Nat

def theorem415LocalMajorantBridgeSplitRouteAuditAfterG266 :
    Theorem415LocalMajorantBridgeSplitRouteAuditAfterG266 where
  source_facing_convergence_in_measure_used := 1
  opaque_local_split_public_input_required := 0
  local_majorant_bridge_split_data_required := 1
  local_complement_bridge_public_input_required := 1
  row_seed_tools_public_input_required_for_split := 0
  global_value_bridge_public_input_required_for_split := 0
  global_characteristic_domain_witness_required := 0
  prop_to_type_witness_extraction_used := 0
  external_choice_principle_added := 0
  remaining_definition_unfolding_frontiers := 2

structure Chapter4G266Theorem415LocalMajorantBridgeSplitPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 10 where
  g265 : Chapter4G265Theorem415SourceFacingLocalSplitPackage S
  audit : Theorem415LocalMajorantBridgeSplitRouteAuditAfterG266
  local_split_opened_to_majorant_bridge_estimates_this_step : Nat
  remaining_definition_unfolding_frontiers : Nat

def chapter4G266Theorem415LocalMajorantBridgeSplitPackage
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    Chapter4G266Theorem415LocalMajorantBridgeSplitPackage S where
  g265 := chapter4G265Theorem415SourceFacingLocalSplitPackage S
  audit := theorem415LocalMajorantBridgeSplitRouteAuditAfterG266
  local_split_opened_to_majorant_bridge_estimates_this_step := 1
  remaining_definition_unfolding_frontiers := 2

end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route

/-- Progress after G266. -/
def bishopRegularSeqChapter4Theorem415LocalMajorantBridgeSplitProgressAfterG266 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 100
  ch1_on_bishop_real_percent := 100
  ch2_on_bishop_real_percent := 100
  ch3_on_bishop_real_percent := 100
  ch4_on_bishop_real_percent := 99
  total_final_goal_percent := 99
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G266: opened the theorem 4.15 local split field into the source majorant \
    estimate: local bridges for |f_n-f| and the majorant, plus the two small \
    piece estimates, construct the local split. RowSeedTools and global value \
    bridges are no longer public inputs for this conversion. Countdown remains \
    2: derive the local bridge-backed split data and complement bridges from \
    the measurable/integrable-set definitions."


end BishopCReal
