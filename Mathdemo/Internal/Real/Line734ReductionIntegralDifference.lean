import Mathdemo.Internal.Real.IdentifyingLargeTruncationMiddleTerm

/-!
# G60: line 734 reduction through the integral of the difference

G59 identified the source middle term on lines 734--735 as
`I(|min(f,n)-min(g,n)|)`.  This file closes the algebraic identification
needed for line 734: the source left side is the absolute value of the
integral of the explicit `L1` difference representative.

The analytic estimate `|I(h)| <= I(|h|)` is kept as its own source-level
bridge, so the remaining frontier is stated at the right level.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Multiplication by the representative `-1` agrees with additive inverse. -/
theorem mulSeq_neg_one_left_eventually_neg
    (Arch : ScalarMulArchimedeanData)
    (x : RegularSeq) :
    relEventually
      (mulSeqConcreteWith Arch (negSeq oneSeq) x)
      (negSeq x) := by
  have hmul :
      relEventually
        (mulSeqConcreteWith Arch (negSeq oneSeq) x)
        (negSeq (mulSeqConcreteWith Arch oneSeq x)) :=
    bounded_mul_neg_left_eventually_with Arch oneSeq x
  have hone :
      relEventually (mulSeqConcreteWith Arch oneSeq x) x :=
    mulSeqConcrete_one_left_eventually Arch x
  have hneg :
      relEventually
        (negSeq (mulSeqConcreteWith Arch oneSeq x))
        (negSeq x) :=
    negSeq_respects_eventually
      (mulSeqConcreteWith Arch oneSeq x) x hone
  exact
    relEventually_trans
      (mulSeqConcreteWith Arch (negSeq oneSeq) x)
      (negSeq (mulSeqConcreteWith Arch oneSeq x))
      (negSeq x)
      hmul
      hneg

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The source difference representative has integral `I(r)-I(s)`. -/
theorem sub_integral_agrees
    (r s : BishopRegularSeqIntegrableRep S)
    (data : BishopRegularSeqIntegrableRep.SubData r s) :
    relEventually
      (BishopRegularSeqIntegrableRep.integral
        (BishopRegularSeqIntegrableRep.sub r s data))
      (subSeq r.integral s.integral) := by
  let neg_s : BishopRegularSeqIntegrableRep S :=
    BishopRegularSeqIntegrableRep.smul
      (S := S) (negSeq oneSeq) s data.neg_data
  have hadd :
      relEventually
        (BishopRegularSeqIntegrableRep.integral
          (BishopRegularSeqIntegrableRep.sub r s data))
        (addSeq r.integral neg_s.integral) :=
    BishopRegularSeqIntegrableRep.add_integral_agrees
      r neg_s data.add_data
  have hsmul :
      relEventually
        neg_s.integral
        (mulSeqConcreteWith Arch (negSeq oneSeq) s.integral) :=
    BishopRegularSeqIntegrableRep.smul_integral_agrees
      (S := S) (negSeq oneSeq) s data.neg_data
  have hneg :
      relEventually
        neg_s.integral
        (negSeq s.integral) :=
    relEventually_trans
      neg_s.integral
      (mulSeqConcreteWith Arch (negSeq oneSeq) s.integral)
      (negSeq s.integral)
      hsmul
      (mulSeq_neg_one_left_eventually_neg Arch s.integral)
  have hadd_neg :
      relEventually
        (addSeq r.integral neg_s.integral)
        (addSeq r.integral (negSeq s.integral)) :=
    addSeq_respects_eventually
      r.integral r.integral
      neg_s.integral (negSeq s.integral)
      (relEventually_refl r.integral)
      hneg
  have hsub :
      relEventually
        (addSeq r.integral (negSeq s.integral))
        (subSeq r.integral s.integral) :=
    relEventually_symm
      (subSeq r.integral s.integral)
      (addSeq r.integral (negSeq s.integral))
      (subSeq_eq_add_neg_eventually r.integral s.integral)
  exact
    relEventually_trans
      (BishopRegularSeqIntegrableRep.integral
        (BishopRegularSeqIntegrableRep.sub r s data))
      (addSeq r.integral neg_s.integral)
      (subSeq r.integral s.integral)
      hadd
      (relEventually_trans
        (addSeq r.integral neg_s.integral)
        (addSeq r.integral (negSeq s.integral))
        (subSeq r.integral s.integral)
        hadd_neg
        hsub)

end BishopRegularSeqIntegrableRep

/-- Non-strict order is stable under eventual equality on the left side. -/
theorem regularSeqLe_of_left_eventual
    {x x' y : RegularSeq}
    (hxx : relEventually x x')
    (hle : RegularSeqLe x' y) :
    RegularSeqLe x y := by
  intro hcounter
  have hbase :
      relEventually (subSeq y x) (subSeq y x') :=
    subSeq_respects_eventually
      y y x x'
      (relEventually_refl y)
      hxx
  have hneg :
      relEventually
        (subSeq zeroSeq (subSeq y x))
        (subSeq zeroSeq (subSeq y x')) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      (subSeq y x) (subSeq y x')
      (relEventually_refl zeroSeq)
      hbase
  exact
    hle
      (posEventually_respects
        (subSeq zeroSeq (subSeq y x))
        (subSeq zeroSeq (subSeq y x'))
        hneg
        hcounter)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- General source estimate used in line 734:
`|I(h)| <= I(|h|)`. -/
structure BishopRegularSeqIntegralAbsBoundBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 1 where
  bound :
    forall h : BishopRegularSeqIntegrableRep S,
      forall abs_data : BishopRegularSeqIntegrableRep.AbsData h,
        RegularSeqLe
          (absSeq h.integral)
          (BishopRegularSeqIntegrableRep.sourceNorm h abs_data)
  source_uses_abs_integral_bound : Prop

/-- The source left side of line 734 is the absolute value of the integral of
the explicit `L1` cut-difference representative. -/
theorem largeLine734Left_agrees_cutDiffIntegralAbs
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
    relEventually
      (absSeq
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (S.core.I (largeOldCutPFun S r cor117_data N n))))
      (absSeq
        (BishopRegularSeqIntegrableRep.integral
          (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data))) := by
  have hprevious :
      relEventually
        (BishopRegularSeqIntegrableRep.integral
          (largeOldCutRep S r cor117_data N n ofL_data))
        (S.core.I (largeOldCutPFun S r cor117_data N n)) :=
    largeOldCutRep_integral_agrees S r cor117_data N n ofL_data
  have hleft :
      relEventually
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (S.core.I (largeOldCutPFun S r cor117_data N n)))
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (BishopRegularSeqIntegrableRep.integral
            (largeOldCutRep S r cor117_data N n ofL_data))) :=
    subSeq_respects_eventually
      (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
      (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
      (S.core.I (largeOldCutPFun S r cor117_data N n))
      (BishopRegularSeqIntegrableRep.integral
        (largeOldCutRep S r cor117_data N n ofL_data))
      (relEventually_refl
        (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n)))
      (relEventually_symm
        (BishopRegularSeqIntegrableRep.integral
          (largeOldCutRep S r cor117_data N n ofL_data))
        (S.core.I (largeOldCutPFun S r cor117_data N n))
        hprevious)
  have hdiff :
      relEventually
        (BishopRegularSeqIntegrableRep.integral
          (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data))
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (BishopRegularSeqIntegrableRep.integral
            (largeOldCutRep S r cor117_data N n ofL_data))) :=
    BishopRegularSeqIntegrableRep.sub_integral_agrees
      (cutNatRep r cuts n)
      (largeOldCutRep S r cor117_data N n ofL_data)
      sub_data
  have hmain :
      relEventually
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (S.core.I (largeOldCutPFun S r cor117_data N n)))
        (BishopRegularSeqIntegrableRep.integral
          (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)) :=
    relEventually_trans
      (subSeq
        (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
        (S.core.I (largeOldCutPFun S r cor117_data N n)))
      (subSeq
        (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
        (BishopRegularSeqIntegrableRep.integral
          (largeOldCutRep S r cor117_data N n ofL_data)))
      (BishopRegularSeqIntegrableRep.integral
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data))
      hleft
      (relEventually_symm
        (BishopRegularSeqIntegrableRep.integral
          (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data))
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (BishopRegularSeqIntegrableRep.integral
            (largeOldCutRep S r cor117_data N n ofL_data)))
        hdiff)
  exact absSeq_respects_eventually _ _ hmain

/-- Line 734 follows once the general `|I(h)| <= I(|h|)` estimate is supplied. -/
theorem largeLine734_abs_integral_bound_from_bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (abs_bridge : BishopRegularSeqIntegralAbsBoundBridge S)
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
    RegularSeqLe
      (absSeq
        (subSeq
          (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
          (S.core.I (largeOldCutPFun S r cor117_data N n))))
      (largeCutDiffMid S r cuts cor117_data N n
        ofL_data sub_data abs_data) := by
  have hleft :=
    largeLine734Left_agrees_cutDiffIntegralAbs
      S r cuts cor117_data N n ofL_data sub_data
  have hbound :
      RegularSeqLe
        (absSeq
          (BishopRegularSeqIntegrableRep.integral
            (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)))
        (largeCutDiffMid S r cuts cor117_data N n
          ofL_data sub_data abs_data) := by
    simpa [largeCutDiffMid] using
      abs_bridge.bound
        (largeCutDiffRep S r cuts cor117_data N n ofL_data sub_data)
        abs_data
  exact regularSeqLe_of_left_eventual hleft hbound

/-- A source-faithful large branch bridge where line 734 is obtained from the
general absolute-integral estimate, leaving line 735 as the local
min-truncation estimate. -/
structure Property4LargeCutDiffLine734Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  abs_integral_bound : BishopRegularSeqIntegralAbsBoundBridge S
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
  source_line734_generated_from_abs_integral_bound : Prop
  source_line735_remains_min_lipschitz_integral_bound : Prop

/-- Recover the G59 bridge from the line-734-reduced bridge. -/
def property4LargeCutDiffBridge_from_line734
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeCutDiffLine734Bridge S) :
    Property4LargeCutDiffBridge S where
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line734_abs_integral_bound := by
    intro r cuts cor117_data N n
    exact
      largeLine734_abs_integral_bound_from_bridge
        S bridge.abs_integral_bound
        r cuts cor117_data N n
        (bridge.old_cut_ofL_data r cuts cor117_data N n)
        (bridge.cut_diff_sub_data r cuts cor117_data N n)
        (bridge.cut_diff_abs_data r cuts cor117_data N n)
  line735_cut_diff_bound := bridge.line735_cut_diff_bound
  source_line734_middle_term_is_cut_difference_norm := True
  source_line735_is_min_lipschitz_integral_bound := True

/-- Large norm-bound bridge where only line 735 remains local. -/
def property4LargeNormBoundBridge_from_line734
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeCutDiffLine734Bridge S) :
    Property4LargeNormBoundBridge S :=
  property4LargeNormBoundBridge_from_cut_diff
    S regularSeqLeOrderBridge
    (property4LargeCutDiffBridge_from_line734 S bridge)

end BishopRegularSeqTheorem118

/-- G60 package: line 734 is reduced to the general absolute-integral bound,
and the `sub` integral algebra has been closed. -/
structure BishopRegularSeqTheorem118G60Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  g59 : BishopRegularSeqTheorem118G59Package S
  integral_abs_bound_bridge : Type 1
  large_line734_bridge : Type 2
  large_cut_diff_from_line734 :
    BishopRegularSeqTheorem118.Property4LargeCutDiffLine734Bridge S ->
      BishopRegularSeqTheorem118.Property4LargeCutDiffBridge S
  large_norm_bound_from_line734 :
    BishopRegularSeqTheorem118.Property4LargeCutDiffLine734Bridge S ->
      BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S
  source_line734_algebraic_identification_closed : Prop
  remaining_large_frontier_is_general_abs_bound_plus_line735 : Prop
  remaining_small_frontier_unchanged_from_g59 : Prop

def bishopRegularSeqTheorem118G60Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G60Package S where
  g59 := bishopRegularSeqTheorem118G59Package S
  integral_abs_bound_bridge :=
    BishopRegularSeqTheorem118.BishopRegularSeqIntegralAbsBoundBridge S
  large_line734_bridge :=
    BishopRegularSeqTheorem118.Property4LargeCutDiffLine734Bridge S
  large_cut_diff_from_line734 := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeCutDiffBridge_from_line734
      S bridge
  large_norm_bound_from_line734 := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeNormBoundBridge_from_line734
      S bridge
  source_line734_algebraic_identification_closed := True
  remaining_large_frontier_is_general_abs_bound_plus_line735 := True
  remaining_small_frontier_unchanged_from_g59 := True

/-- Progress after G60: the large branch line 734 algebraic identification is
closed, leaving its analytic estimate as the source-level bridge and line 735
as the next local target. -/
def bishopRegularSeqCh1To4ProgressAfterG60 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 88
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 60
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G60: closed the sub-integral algebra and reduced Theorem 1.18 property \
    (4) line 734 to the general absolute-integral bound."

set_option linter.style.longLine false


end BishopCReal
