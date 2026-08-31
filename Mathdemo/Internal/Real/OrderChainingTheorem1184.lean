import Mathdemo.Internal.Real.ClosingStrictUpperTransferBridge

/-!
# G58: order chaining for Theorem 1.18(4) norm bounds

G57 closed the strict upper-transfer bridge.  The next source estimates,
lines 734--735 and 743--747, also require chaining non-strict bounds.  This
file closes the needed `RegularSeqLe` transitivity step from the existing
cotransitive strict order, then uses it to factor the remaining large and small
norm-bound targets into two displayed non-strict inequalities.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- A counterexample to `x <= y`, in the internal `RegularSeqLe` spelling, gives
the reverse strict comparison `y < x`. -/
theorem regularSeqLtProp_reverse_of_le_counterexample
    {x y : RegularSeq}
    (h : regularSeqLtProp (subSeq y x) zeroSeq) :
    regularSeqLtProp y x := by
  have h1 :
      relEventually
        (subSeq zeroSeq (subSeq y x))
        (negSeq (subSeq y x)) :=
    subSeq_zero_left_eventually (subSeq y x)
  have h2 :
      relEventually
        (negSeq (subSeq y x))
        (subSeq x y) :=
    relEventually_symm
      (subSeq x y)
      (negSeq (subSeq y x))
      (subSeq_comm_neg_eventually x y)
  exact
    posEventually_respects
      (subSeq zeroSeq (subSeq y x))
      (subSeq x y)
      (relEventually_trans
        (subSeq zeroSeq (subSeq y x))
        (negSeq (subSeq y x))
        (subSeq x y)
        h1 h2)
      h

/-- Prop-valued version of the G57 contradiction: `y < x` contradicts
`x <= y`. -/
theorem regularSeqLe_not_lt_reverse_prop
    {x y : RegularSeq}
    (hxy : RegularSeqLe x y)
    (hyx : regularSeqLtProp y x) :
    False := by
  have htarget :
      PosEventually (subSeq zeroSeq (subSeq y x)) := by
    have h1 :
        relEventually (subSeq x y) (negSeq (subSeq y x)) :=
      subSeq_comm_neg_eventually x y
    have h2 :
        relEventually (negSeq (subSeq y x)) (subSeq zeroSeq (subSeq y x)) :=
      relEventually_symm
        (subSeq zeroSeq (subSeq y x))
        (negSeq (subSeq y x))
        (subSeq_zero_left_eventually (subSeq y x))
    exact
      posEventually_respects
        (subSeq x y)
        (subSeq zeroSeq (subSeq y x))
        (relEventually_trans
          (subSeq x y)
          (negSeq (subSeq y x))
          (subSeq zeroSeq (subSeq y x))
          h1 h2)
        hyx
  exact hxy htarget

/-- Non-strict order transitivity for the RegularSeq order surface. -/
theorem regularSeqLe_trans
    {x y z : RegularSeq}
    (hxy : RegularSeqLe x y)
    (hyz : RegularSeqLe y z) :
    RegularSeqLe x z := by
  intro hcounter
  have hzx : regularSeqLtProp z x :=
    regularSeqLtProp_reverse_of_le_counterexample hcounter
  rcases regularSeqLtProp_cotrans z x y hzx with hzy | hyx
  · exact regularSeqLe_not_lt_reverse_prop hyz hzy
  · exact regularSeqLe_not_lt_reverse_prop hxy hyx

/-- Closed non-strict order chaining used by the displayed estimate chains in
Theorem 1.18(4). -/
structure RegularSeqLeOrderBridge : Type 1 where
  le_trans :
    forall {x y z : RegularSeq},
      RegularSeqLe x y -> RegularSeqLe y z -> RegularSeqLe x z
  source_order_chaining_for_displayed_estimates : Prop

def regularSeqLeOrderBridge : RegularSeqLeOrderBridge where
  le_trans := by
    intro x y z hxy hyz
    exact regularSeqLe_trans hxy hyz
  source_order_chaining_for_displayed_estimates := True

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- Two-step non-strict bound behind source lines 734--735.  The middle term is
the source's intermediate absolute integral, left abstract here so the next
increment can identify it with the exact `min`-difference representation. -/
structure Property4LargeNormBoundTwoStepBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  mid :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (_cuts : Property4CutData S r),
      forall _cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (_N _n : Nat), RegularSeq
  left_le_mid :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        RegularSeqLe
          (absSeq
            (subSeq
              (BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
              (S.core.I
                (BishopRegularSeqPFun.cutNat Arch n
                  (((bishopRegularSeqCor117_from_data S r cor117_data).approximant)
                    N)))))
          (mid r cuts cor117_data N n)
  mid_le_norm :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_data : BishopRegularSeqCor117ApproxData S r,
      forall (N n : Nat),
        RegularSeqLe
          (mid r cuts cor117_data N n)
          (BishopRegularSeqIntegrableRep.sourceNorm
            (BishopRegularSeqIntegrableRep.sub
              r
              ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep N)
              ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data N))
            ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data N))
  source_line_734_first_non_strict_bound : Prop
  source_line_735_second_non_strict_bound : Prop

/-- Build the large norm-bound bridge by chaining its two source inequalities. -/
def property4LargeNormBoundBridge_from_two_step
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (order : RegularSeqLeOrderBridge)
    (two_step : Property4LargeNormBoundTwoStepBridge S) :
    Property4LargeNormBoundBridge S where
  bound := by
    intro r cuts cor117_data N n
    exact
      order.le_trans
        (two_step.left_le_mid r cuts cor117_data N n)
        (two_step.mid_le_norm r cuts cor117_data N n)
  source_lines_734_to_735 := True

/-- Two-step non-strict bound behind source lines 743--747.  The middle term
keeps the source's local small-truncation comparison explicit. -/
structure Property4SmallNormBoundTwoStepBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 2 where
  mid :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall _cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (_N _n : Nat), RegularSeq
  left_le_mid :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        RegularSeqLe
          (BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
          (mid r cuts cor117_abs_data N n)
  mid_le_old_plus_norm :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        RegularSeqLe
          (mid r cuts cor117_abs_data N n)
          (addSeq
            (S.core.I
              (BishopRegularSeqPFun.cutSmall Arch n
                (((bishopRegularSeqCor117_from_data S
                  (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                  cor117_abs_data).approximant) N)))
            (BishopRegularSeqIntegrableRep.sourceNorm
              (BishopRegularSeqIntegrableRep.sub
                (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                ((bishopRegularSeqCor117_from_data S
                    (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                    cor117_abs_data).approximant_rep N)
                ((bishopRegularSeqCor117_from_data S
                    (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                    cor117_abs_data).tail_sub_data N))
              ((bishopRegularSeqCor117_from_data S
                  (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
                  cor117_abs_data).tail_abs_data N)))
  source_lines_743_to_745_first_non_strict_bound : Prop
  source_lines_745_to_747_second_non_strict_bound : Prop

/-- Build the small norm-bound bridge by chaining its two source inequalities. -/
def property4SmallNormBoundBridge_from_two_step
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (order : RegularSeqLeOrderBridge)
    (two_step : Property4SmallNormBoundTwoStepBridge S) :
    Property4SmallNormBoundBridge S where
  bound := by
    intro r cuts cor117_abs_data N n
    exact
      order.le_trans
        (two_step.left_le_mid r cuts cor117_abs_data N n)
        (two_step.mid_le_old_plus_norm r cuts cor117_abs_data N n)
  source_lines_743_to_747 := True

/-- Property (4) norm-bound inputs reduced to two-step source inequalities, with
non-strict order chaining now closed. -/
structure Property4ReductionDataFromTwoStepNormBounds
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 2 where
  order : RegularSeqLeOrderBridge
  large_two_step : Property4LargeNormBoundTwoStepBridge S
  small_two_step : Property4SmallNormBoundTwoStepBridge S
  base_data :
    Property4ReductionDataFromNormBounds S r
  base_large_norm_bound_is_generated :
    base_data.large_norm_bound =
      property4LargeNormBoundBridge_from_two_step S order large_two_step
  base_small_norm_bound_is_generated :
    base_data.small_norm_bound =
      property4SmallNormBoundBridge_from_two_step S order small_two_step

/-- Forget the two-step factories and recover the G56 norm-bound data. -/
def property4NormBoundData_from_two_step
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromTwoStepNormBounds S r) :
    Property4ReductionDataFromNormBounds S r :=
  data.base_data

/-- Theorem 1.18 property (4), assembled through the G58 two-step norm-bound
factorization. -/
def property4_from_two_step_norm_bound_data
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data : Property4ReductionDataFromTwoStepNormBounds S r) :
    Property4Conclusion S r :=
  property4_from_norm_bound_data S r
    (property4NormBoundData_from_two_step S r data)

end BishopRegularSeqTheorem118

/-- G58 package: non-strict order chaining is closed, and the remaining
Theorem 1.18(4) norm bounds are factored into the two source inequality steps. -/
structure BishopRegularSeqTheorem118G58Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 3 where
  g57 : BishopRegularSeqTheorem118G57Package S
  le_order_bridge : RegularSeqLeOrderBridge
  large_two_step : Type 2
  small_two_step : Type 2
  large_norm_bound_from_two_step :
    BishopRegularSeqTheorem118.Property4LargeNormBoundTwoStepBridge S ->
      BishopRegularSeqTheorem118.Property4LargeNormBoundBridge S
  small_norm_bound_from_two_step :
    BishopRegularSeqTheorem118.Property4SmallNormBoundTwoStepBridge S ->
      BishopRegularSeqTheorem118.Property4SmallNormBoundBridge S
  source_order_chaining_closed_by_cotransitivity : Prop
  remaining_work_is_source_two_step_inequality_data : Prop

def bishopRegularSeqTheorem118G58Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G58Package S where
  g57 := bishopRegularSeqTheorem118G57Package S
  le_order_bridge := regularSeqLeOrderBridge
  large_two_step :=
    BishopRegularSeqTheorem118.Property4LargeNormBoundTwoStepBridge S
  small_two_step :=
    BishopRegularSeqTheorem118.Property4SmallNormBoundTwoStepBridge S
  large_norm_bound_from_two_step := fun bridge =>
    BishopRegularSeqTheorem118.property4LargeNormBoundBridge_from_two_step
      S regularSeqLeOrderBridge bridge
  small_norm_bound_from_two_step := fun bridge =>
    BishopRegularSeqTheorem118.property4SmallNormBoundBridge_from_two_step
      S regularSeqLeOrderBridge bridge
  source_order_chaining_closed_by_cotransitivity := True
  remaining_work_is_source_two_step_inequality_data := True

/-- Progress after G58: order chaining for Theorem 1.18(4)'s displayed
non-strict estimate chains is closed. -/
def bishopRegularSeqCh1To4ProgressAfterG58 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 62
  ch1_on_bishop_real_percent := 86
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 58
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G58: closed RegularSeqLe transitivity and factored Theorem 1.18 property \
    (4)'s norm bounds into two-step source inequality bridges."

set_option linter.style.longLine false


end BishopCReal
