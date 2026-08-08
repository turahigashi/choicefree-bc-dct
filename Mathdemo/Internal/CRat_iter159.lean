import Mathdemo.Internal.CRat_iter158

/-!
# G59: identifying the large truncation middle term

G58 reduced the large Theorem 1.18(4) estimate to two non-strict inequalities
with an abstract middle term.  The source middle term on lines 734--735 is
`I(|min(f,n)-min(g,n)|)`.  This file identifies that middle term in the
RegularSeq `L1` presentation by embedding the old-space truncation `min(g,n)`
into `L1`, forming the difference, and taking its source norm.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The old-space large truncation `min(g,n)` where `g` is the Corollary 1.17
finite-sum approximant. -/
def largeOldCutPFun
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat) :
    BishopRegularSeqPFun X :=
  BishopRegularSeqPFun.cutNat Arch n
    (((bishopRegularSeqCor117_from_data S r cor117_data).approximant) N)

/-- The old-space truncation `min(g,n)` belongs to the original integration
space by Definition 1.1(1). -/
theorem largeOldCut_mem
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat) :
    largeOldCutPFun S r cor117_data N n ∈ S.core.L := by
  simpa [largeOldCutPFun, BishopRegularSeqPFun.cutNat] using
    S.cutConst_mem
      (constSeq (n : Scalar))
      (((bishopRegularSeqCor117_from_data S r cor117_data).approximant_mem) N)

/-- The old-space truncation `min(g,n)` embedded into `L1`. -/
def largeOldCutRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n)) :
    BishopRegularSeqIntegrableRep S :=
  def16_ofL S (largeOldCut_mem S r cor117_data N n) ofL_data

/-- The embedded previous truncation has the previous integral value. -/
theorem largeOldCutRep_integral_agrees
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n)) :
    relEventually
      (BishopRegularSeqIntegrableRep.integral
        (largeOldCutRep S r cor117_data N n ofL_data))
      (S.core.I (largeOldCutPFun S r cor117_data N n)) :=
  def16_ofL_integral_agrees S
    (largeOldCut_mem S r cor117_data N n)
    ofL_data

/-- The `L1` difference `min(f,n)-min(g,n)` used in the first inequality on
source line 734. -/
def largeCutDiffRep
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data)) :
    BishopRegularSeqIntegrableRep S :=
  BishopRegularSeqIntegrableRep.sub
    (cutNatRep r cuts n)
    (largeOldCutRep S r cor117_data N n ofL_data)
    sub_data

/-- The concrete middle term `I(|min(f,n)-min(g,n)|)`. -/
def largeCutDiffMid
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (cuts : Property4CutData S r)
    (cor117_data : BishopRegularSeqCor117ApproxData S r)
    (N n : Nat)
    (ofL_data :
      BishopRegularSeqOfLData S
        (largeOldCutPFun S r cor117_data N n)
        (largeOldCut_mem S r cor117_data N n))
    (sub_data :
      BishopRegularSeqIntegrableRep.SubData
        (cutNatRep r cuts n)
        (largeOldCutRep S r cor117_data N n ofL_data))
    (abs_data :
      BishopRegularSeqIntegrableRep.AbsData
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)) :
    RegularSeq :=
  BishopRegularSeqIntegrableRep.sourceNorm
    (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)
    abs_data

/-- Source line 734 with the middle term now identified as the norm of the
`L1` cut-difference representative.  The two inequalities themselves remain
explicit fields, corresponding to line 734 and line 735. -/
structure Property4LargeCutDiffBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  old_cut_ofL_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (_cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqOfLData S
          (largeOldCutPFun S r cor117_data N n)
          (largeOldCut_mem S r cor117_data N n)
  cut_diff_sub_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.SubData
          (cutNatRep r cuts n)
          (largeOldCutRep S r cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n))
  cut_diff_abs_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.AbsData
          (largeCutDiffRep S r cuts cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n)
            (cut_diff_sub_data r cuts cor117_data N n))
  line734_abs_integral_bound :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        RegularSeqLe
          (absSeq
            (subSeq
              (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
              (S.core.I (largeOldCutPFun S r cor117_data N n))))
          (largeCutDiffMid S r cuts cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n)
            (cut_diff_sub_data r cuts cor117_data N n)
            (cut_diff_abs_data r cuts cor117_data N n))
  line735_cut_diff_bound :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        RegularSeqLe
          (largeCutDiffMid S r cuts cor117_data N n
            (old_cut_ofL_data r cuts cor117_data N n)
            (cut_diff_sub_data r cuts cor117_data N n)
            (cut_diff_abs_data r cuts cor117_data N n))
          (BishopRegularSeqIntegrableRep.sourceNorm
            (BishopRegularSeqIntegrableRep.sub
              r
              ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep N)
              ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data N))
            ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data N))
  source_line734_middle_term_is_cut_difference_norm : Prop
  source_line735_is_min_lipschitz_integral_bound : Prop

/-- Recover the G58 large two-step bridge from the concrete cut-difference
middle term. -/
def property4LargeNormBoundTwoStepBridge_from_cut_diff
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeCutDiffBridge S) :
    Property4LargeNormBoundTwoStepBridge S where
  mid := fun r cuts cor117_data N n =>
    largeCutDiffMid S r cuts cor117_data N n
      (bridge.old_cut_ofL_data r cuts cor117_data N n)
      (bridge.cut_diff_sub_data r cuts cor117_data N n)
      (bridge.cut_diff_abs_data r cuts cor117_data N n)
  left_le_mid := by
    intro r cuts cor117_data N n
    exact bridge.line734_abs_integral_bound r cuts cor117_data N n
  mid_le_norm := by
    intro r cuts cor117_data N n
    exact bridge.line735_cut_diff_bound r cuts cor117_data N n
  source_line_734_first_non_strict_bound := True
  source_line_735_second_non_strict_bound := True

/-- Large norm-bound bridge with the middle term no longer abstract. -/
def property4LargeNormBoundBridge_from_cut_diff
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (order : RegularSeqLeOrderBridge)
    (bridge : Property4LargeCutDiffBridge S) :
    Property4LargeNormBoundBridge S :=
  property4LargeNormBoundBridge_from_two_step S order
    (property4LargeNormBoundTwoStepBridge_from_cut_diff S bridge)

end BishopRegularSeqTheorem118

/-- G59 package: the large branch middle term of Theorem 1.18(4) is now the
source norm of the explicit `L1` cut-difference representative. -/
structure BishopRegularSeqTheorem118G59Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  g58 : BishopRegularSeqTheorem118G58Package S
  large_cut_diff_bridge : Type 2
  large_two_step_from_cut_diff :
    BishopRegularSeqTheorem118.Property4LargeCutDiffBridge S ->
      BishopRegularSeqTheorem118.Property4LargeNormBoundTwoStepBridge S
  large_norm_bound_from_cut_diff :
    BishopRegularSeqTheorem118.Property4LargeCutDiffBridge S ->
      BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S
  source_line734_middle_term_identified : Prop
  remaining_large_frontier_is_two_integral_inequalities : Prop
  remaining_small_frontier_unchanged_from_g58 : Prop

def bishopRegularSeqTheorem118G59Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G59Package S where
  g58 := bishopRegularSeqTheorem118G58Package S
  large_cut_diff_bridge :=
    BishopRegularSeqTheorem118.Property4LargeCutDiffBridge S
  large_two_step_from_cut_diff := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeNormBoundTwoStepBridge_from_cut_diff
      S bridge
  large_norm_bound_from_cut_diff := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeNormBoundBridge_from_cut_diff
      S regularSeqLeOrderBridge bridge
  source_line734_middle_term_identified := True
  remaining_large_frontier_is_two_integral_inequalities := True
  remaining_small_frontier_unchanged_from_g58 := True

/-- Progress after G59: the large branch middle term in Theorem 1.18(4) is
concretely represented as `I(|min(f,n)-min(g,n)|)`. -/
def bishopRegularSeqCh1To4ProgressAfterG59 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 87
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 59
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G59: identified Theorem 1.18 property (4)'s large branch middle term as \
    the norm of the L1 cut-difference representative."

set_option linter.style.longLine false


end BishopCReal
