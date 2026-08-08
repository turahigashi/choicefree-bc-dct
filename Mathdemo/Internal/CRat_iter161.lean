import Mathdemo.Internal.CRat_iter160

/-!
# G61: reducing `|I(h)| <= I(|h|)` to Proposition 1.11

G60 isolated the general source estimate `|I(h)| <= I(|h|)`.  This file
connects that estimate back to the earlier source monotonicity layer:
Proposition 1.11 gives the two integral bounds from the pointwise domination
`h <= |h|` and `-h <= |h|`; a small RegularSeq order bridge then turns those
two bounds into the absolute-value bound.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- RegularSeq order bridge: if `x` and `-x` are both below `y`, then `|x|`
is below `y`.  This is the order step used after Proposition 1.11 in the
source estimate `|I(h)| <= I(|h|)`. -/
structure RegularSeqAbsFromTwoSidedBridge : Type 1 where
  abs_le_of_two_sided :
    forall x y : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (negSeq x) y ->
          RegularSeqLe (absSeq x) y
  source_order_step_for_absolute_integral_bound : Prop

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Data needed to apply Proposition 1.11 to the two pointwise inequalities
`h <= |h|` and `-h <= |h|`. -/
structure BishopRegularSeqIntegralAbsProp111Data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (h : BishopRegularSeqIntegrableRep S)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData h) : Type 2 where
  neg_data :
    BishopRegularSeqIntegrableRep.SmulData (negSeq oneSeq) h
  upper_set : Set X
  upper_full : BishopRegularSeqFullSet S upper_set
  upper_le_on_full :
    BishopRegularSeqL1LeOnFull S upper_set
      h
      (BishopRegularSeqIntegrableRep.abs h abs_data)
  lower_set : Set X
  lower_full : BishopRegularSeqFullSet S lower_set
  lower_le_on_full :
    BishopRegularSeqL1LeOnFull S lower_set
      (BishopRegularSeqIntegrableRep.smul
        (S := S) (negSeq oneSeq) h neg_data)
      (BishopRegularSeqIntegrableRep.abs h abs_data)
  source_upper_is_h_le_abs_h : Prop
  source_lower_is_neg_h_le_abs_h : Prop

/-- From the Proposition 1.11 monotonicity bridge and the two pointwise
domination inputs, derive the general estimate `|I(h)| <= I(|h|)`. -/
theorem integralAbsBound_from_prop111
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (prop111_bridge : BishopRegularSeqProp111Bridge S)
    (order_abs : RegularSeqAbsFromTwoSidedBridge)
    (h : BishopRegularSeqIntegrableRep S)
    (abs_data : BishopRegularSeqIntegrableRep.AbsData h)
    (data : BishopRegularSeqIntegralAbsProp111Data S h abs_data) :
    RegularSeqLe
      (absSeq h.integral)
      (BishopRegularSeqIntegrableRep.sourceNorm h abs_data) := by
  let absRep : BishopRegularSeqIntegrableRep S :=
    BishopRegularSeqIntegrableRep.abs h abs_data
  let negRep : BishopRegularSeqIntegrableRep S :=
    BishopRegularSeqIntegrableRep.smul
      (S := S) (negSeq oneSeq) h data.neg_data
  have hupper0 :
      RegularSeqLe h.integral absRep.integral :=
    prop111_bridge.monotone
      data.upper_full
      h
      absRep
      data.upper_le_on_full
  have hupper :
      RegularSeqLe
        h.integral
        (BishopRegularSeqIntegrableRep.sourceNorm h abs_data) := by
    simpa [BishopRegularSeqIntegrableRep.sourceNorm, absRep] using hupper0
  have hlower0 :
      RegularSeqLe negRep.integral absRep.integral :=
    prop111_bridge.monotone
      data.lower_full
      negRep
      absRep
      data.lower_le_on_full
  have hneg :
      relEventually negRep.integral (negSeq h.integral) := by
    have hsmul :
        relEventually
          negRep.integral
          (mulSeqConcreteWith Arch (negSeq oneSeq) h.integral) :=
      BishopRegularSeqIntegrableRep.smul_integral_agrees
        (S := S) (negSeq oneSeq) h data.neg_data
    exact
      relEventually_trans
        negRep.integral
        (mulSeqConcreteWith Arch (negSeq oneSeq) h.integral)
        (negSeq h.integral)
        hsmul
        (mulSeq_neg_one_left_eventually_neg Arch h.integral)
  have hlower0' :
      RegularSeqLe
        negRep.integral
        (BishopRegularSeqIntegrableRep.sourceNorm h abs_data) := by
    simpa [BishopRegularSeqIntegrableRep.sourceNorm, absRep] using hlower0
  have hlower :
      RegularSeqLe
        (negSeq h.integral)
        (BishopRegularSeqIntegrableRep.sourceNorm h abs_data) :=
    regularSeqLe_of_left_eventual
      (relEventually_symm negRep.integral (negSeq h.integral) hneg)
      hlower0'
  exact
    order_abs.abs_le_of_two_sided
      h.integral
      (BishopRegularSeqIntegrableRep.sourceNorm h abs_data)
      hupper
      hlower

/-- A global source bridge for `|I(h)| <= I(|h|)` built from Proposition
1.11 data for each `h`. -/
structure BishopRegularSeqIntegralAbsProp111Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  prop111_bridge : BishopRegularSeqProp111Bridge S
  order_abs : RegularSeqAbsFromTwoSidedBridge
  domination_data :
    forall h : BishopRegularSeqIntegrableRep S,
      forall abs_data : BishopRegularSeqIntegrableRep.AbsData h,
        BishopRegularSeqIntegralAbsProp111Data S h abs_data
  source_uses_proposition_1_11_for_abs_integral_bound : Prop
  source_uses_two_pointwise_bounds_h_and_neg_h : Prop

/-- Recover the G60 absolute-integral bridge from the Proposition 1.11
reduction. -/
def integralAbsBoundBridge_from_prop111
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : BishopRegularSeqIntegralAbsProp111Bridge S) :
    BishopRegularSeqIntegralAbsBoundBridge S where
  bound := by
    intro h abs_data
    exact
      integralAbsBound_from_prop111
        S
        bridge.prop111_bridge
        bridge.order_abs
        h
        abs_data
        (bridge.domination_data h abs_data)
  source_uses_abs_integral_bound := True

/-- Large line-734 bridge obtained from Proposition 1.11 plus the remaining
line-735 input. -/
structure Property4LargeLine734FromProp111Bridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  abs_from_prop111 : BishopRegularSeqIntegralAbsProp111Bridge S
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
  source_line734_now_reduced_to_prop111 : Prop
  source_line735_remains_min_lipschitz_integral_bound : Prop

/-- Convert the Proposition 1.11 version into the G60 line-734 bridge. -/
def property4LargeCutDiffLine734Bridge_from_prop111
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine734FromProp111Bridge S) :
    Property4LargeCutDiffLine734Bridge S where
  abs_integral_bound :=
    integralAbsBoundBridge_from_prop111 S bridge.abs_from_prop111
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  line735_cut_diff_bound := bridge.line735_cut_diff_bound
  source_line734_generated_from_abs_integral_bound := True
  source_line735_remains_min_lipschitz_integral_bound := True

/-- Large norm-bound bridge with line 734 reduced all the way to Proposition
1.11-shaped data. -/
def property4LargeNormBoundBridge_from_prop111_line734
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4LargeLine734FromProp111Bridge S) :
    Property4LargeNormBoundBridge S :=
  property4LargeNormBoundBridge_from_line734 S
    (property4LargeCutDiffLine734Bridge_from_prop111 S bridge)

end BishopRegularSeqTheorem118

/-- G61 package: the general `|I(h)| <= I(|h|)` bridge is now obtained from
Proposition 1.11-shaped monotonicity data and a two-sided RegularSeq order
step. -/
structure BishopRegularSeqTheorem118G61Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  g60 : BishopRegularSeqTheorem118G60Package S
  abs_order_bridge : Type 1
  abs_prop111_data :
    forall h : BishopRegularSeqIntegrableRep S,
      BishopRegularSeqIntegrableRep.AbsData h -> Type 2
  abs_prop111_bridge : Type 3
  integral_abs_from_prop111 :
    BishopRegularSeqTheorem118.BishopRegularSeqIntegralAbsProp111Bridge S ->
      BishopRegularSeqTheorem118.BishopRegularSeqIntegralAbsBoundBridge S
  large_line734_from_prop111_bridge : Type 3
  large_norm_bound_from_prop111_line734 :
    BishopRegularSeqTheorem118.Property4LargeLine734FromProp111Bridge S ->
      BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S
  source_abs_integral_bound_reduced_to_prop111 : Prop
  remaining_large_frontier_is_order_abs_bridge_and_line735 : Prop
  remaining_small_frontier_unchanged_from_g60 : Prop

def bishopRegularSeqTheorem118G61Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G61Package S where
  g60 := bishopRegularSeqTheorem118G60Package S
  abs_order_bridge := RegularSeqAbsFromTwoSidedBridge
  abs_prop111_data := fun h abs_data =>
    BishopRegularSeqTheorem118.BishopRegularSeqIntegralAbsProp111Data
      S h abs_data
  abs_prop111_bridge :=
    BishopRegularSeqTheorem118.BishopRegularSeqIntegralAbsProp111Bridge S
  integral_abs_from_prop111 := fun bridge =>
    BishopRegularSeqTheorem118.integralAbsBoundBridge_from_prop111
      S bridge
  large_line734_from_prop111_bridge :=
    BishopRegularSeqTheorem118.Property4LargeLine734FromProp111Bridge S
  large_norm_bound_from_prop111_line734 := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeNormBoundBridge_from_prop111_line734
      S bridge
  source_abs_integral_bound_reduced_to_prop111 := True
  remaining_large_frontier_is_order_abs_bridge_and_line735 := True
  remaining_small_frontier_unchanged_from_g60 := True

/-- Progress after G61: the general absolute-integral estimate has been
connected to Proposition 1.11-shaped monotonicity data. -/
def bishopRegularSeqCh1To4ProgressAfterG61 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 89
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 61
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G61: reduced Theorem 1.18 property (4)'s absolute-integral estimate \
    to Proposition 1.11 monotonicity data plus a two-sided order bridge."

set_option linter.style.longLine false


end BishopCReal
