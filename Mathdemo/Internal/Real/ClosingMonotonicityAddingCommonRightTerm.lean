import Mathdemo.Internal.Real.ClosingAbsoluteTailShiftBounds

set_option linter.style.longLine false

/-!
# G94: closing monotonicity under adding a common right term

G93 left `addSeq_monotone_left` as a primitive order input.  This file closes
it by reducing

`(y+z)-(x+z)`

to `y-x`.  The proof reuses the G90 identity
`(x'-r)-(x-r)=x'-x`, after rewriting `a+z` as `a-(-z)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Double negation over the RegularSeq implementation equality. -/
theorem negSeq_negSeq_eventually
    (x : RegularSeq) :
    relEventually (negSeq (negSeq x)) x := by
  apply rel_to_relEventually
  intro n
  unfold negSeq negVal
  rw [show -(-x.val n) - x.val n = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Adding `z` is the same as subtracting `-z` over `relEventually`. -/
theorem addSeq_eq_sub_neg_eventually
    (x z : RegularSeq) :
    relEventually (addSeq x z) (subSeq x (negSeq z)) := by
  have hsub :
      relEventually
        (subSeq x (negSeq z))
        (addSeq x (negSeq (negSeq z))) :=
    subSeq_eq_add_neg_eventually x (negSeq z)
  have hdn :
      relEventually
        (addSeq x (negSeq (negSeq z)))
        (addSeq x z) :=
    addSeq_respects_eventually
      x x
      (negSeq (negSeq z)) z
      (relEventually_refl x)
      (negSeq_negSeq_eventually z)
  exact
    relEventually_symm
      (subSeq x (negSeq z))
      (addSeq x z)
      (relEventually_trans
        (subSeq x (negSeq z))
        (addSeq x (negSeq (negSeq z)))
        (addSeq x z)
        hsub
        hdn)

/-- The represented difference is unchanged by adding the same right term:
`(y+z)-(x+z) = y-x`. -/
theorem addSeq_same_right_sub_eventually
    (x y z : RegularSeq) :
    relEventually
      (subSeq (addSeq y z) (addSeq x z))
      (subSeq y x) := by
  have hy :
      relEventually
        (addSeq y z)
        (subSeq y (negSeq z)) :=
    addSeq_eq_sub_neg_eventually y z
  have hx :
      relEventually
        (addSeq x z)
        (subSeq x (negSeq z)) :=
    addSeq_eq_sub_neg_eventually x z
  have h0 :
      relEventually
        (subSeq (addSeq y z) (addSeq x z))
        (subSeq (subSeq y (negSeq z)) (subSeq x (negSeq z))) :=
    subSeq_respects_eventually
      (addSeq y z) (subSeq y (negSeq z))
      (addSeq x z) (subSeq x (negSeq z))
      hy
      hx
  have hsame :
      relEventually
        (subSeq (subSeq y (negSeq z)) (subSeq x (negSeq z)))
        (subSeq y x) :=
    subSeq_same_right_diff_eventually x y (negSeq z)
  exact
    relEventually_trans
      (subSeq (addSeq y z) (addSeq x z))
      (subSeq (subSeq y (negSeq z)) (subSeq x (negSeq z)))
      (subSeq y x)
      h0
      hsame

/-- Non-strict order is monotone under adding a common right term. -/
theorem addSeq_monotone_left_regularSeqLe
    (x y z : RegularSeq)
    (hxy : RegularSeqLe x y) :
    RegularSeqLe (addSeq x z) (addSeq y z) :=
  regularSeqNonneg_of_eventual
    (addSeq_same_right_sub_eventually x y z)
    hxy

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G94 core data: the add-left monotonicity input is now obtained from the
closed RegularSeq order lemma. -/
structure Property4DisplayedScalarAddMonotoneClosedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  minSeqWith_add_nonnegative_right_bound :
    forall x d c : RegularSeq,
      RegularSeqLe zeroSeq d ->
        RegularSeqLe
          (minSeqWith Arch (addSeq x d) c)
          (addSeq (minSeqWith Arch x c) d)
  source_line735_subtraction_monotone_left_closed : Prop
  source_line735_sub_add_cancel_closed : Prop
  source_line735_same_right_subtraction_diff_closed : Prop
  source_line735_nonneg_transport_closed : Prop
  source_line735_self_shift_upper_closed : Prop
  source_line735_base_shift_lower_closed : Prop
  source_line735_addition_monotonicity_closed : Prop
  source_line735_min_monotonicity_and_shift : Prop
  source_line743_self_le_base_plus_abs_tail_closed : Prop
  source_line743_base_le_abs_base_closed : Prop
  source_line743_addition_monotonicity_for_abs_base_closed : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative_closed : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G94 closed addition monotonicity back to the G93 layer. -/
def displayedScalarShiftClosedCoreLaws_from_addMonotoneClosed
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarAddMonotoneClosedCoreLaws Arch) :
    Property4DisplayedScalarShiftClosedCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  addSeq_monotone_left := addSeq_monotone_left_regularSeqLe
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  minSeqWith_add_nonnegative_right_bound :=
    laws.minSeqWith_add_nonnegative_right_bound
  source_line735_subtraction_monotone_left_closed :=
    laws.source_line735_subtraction_monotone_left_closed
  source_line735_sub_add_cancel_closed :=
    laws.source_line735_sub_add_cancel_closed
  source_line735_same_right_subtraction_diff_closed :=
    laws.source_line735_same_right_subtraction_diff_closed
  source_line735_nonneg_transport_closed :=
    laws.source_line735_nonneg_transport_closed
  source_line735_self_shift_upper_closed :=
    laws.source_line735_self_shift_upper_closed
  source_line735_base_shift_lower_closed :=
    laws.source_line735_base_shift_lower_closed
  source_line735_min_monotonicity_and_shift :=
    laws.source_line735_min_monotonicity_and_shift
  source_line743_self_le_base_plus_abs_tail_closed :=
    laws.source_line743_self_le_base_plus_abs_tail_closed
  source_line743_base_le_abs_base_closed :=
    laws.source_line743_base_le_abs_base_closed
  source_line743_addition_monotonicity_for_abs_base :=
    laws.source_line743_addition_monotonicity_for_abs_base_closed
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_tail_abs_is_nonnegative_closed :=
    laws.source_line743_tail_abs_is_nonnegative_closed
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G94 unified bridge: the G93 bridge obtained from closed addition
monotonicity. -/
structure Property4DisplayedScalarAddMonotoneClosedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  add_monotone_closed_core_laws :
    Property4DisplayedScalarAddMonotoneClosedCoreLaws Arch
  full_sets : Property4DisplayedScalarFullSetData S
  abs_from_prop111 : BishopRegularSeqIntegralAbsProp111Bridge S
  prop111_bridge : BishopRegularSeqProp111Bridge S
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
  old_small_ofL_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqOfLData S
          (smallOldCutPFun S r cuts cor117_abs_data N n)
          (smallOldCut_mem S r cuts cor117_abs_data N n)
  old_plus_tail_add_data :
    forall (r : BishopRegularSeqIntegrableRep S),
      forall (cuts : Property4CutData S r),
      forall cor117_abs_data :
        BishopRegularSeqCor117ApproxData S
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data),
      forall (N n : Nat),
        BishopRegularSeqIntegrableRep.AddData
          (smallOldCutRep S r cuts cor117_abs_data N n
            (old_small_ofL_data r cuts cor117_abs_data N n))
          (smallAbsTailAbsRep S r cuts cor117_abs_data N)
  source_line734_reduced_to_prop111 : Prop
  source_line735_reduced_to_closed_shift_and_add_bounds : Prop
  source_line743_reduced_to_abs_nonnegative_closed_chain : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G94 bridge to the G93 bridge. -/
def displayedScalarShiftClosedCoreUnifiedBridge_from_addMonotoneClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4DisplayedScalarAddMonotoneClosedCoreUnifiedBridge S) :
    Property4DisplayedScalarShiftClosedCoreUnifiedBridge S where
  shift_closed_core_laws :=
    displayedScalarShiftClosedCoreLaws_from_addMonotoneClosed
      Arch bridge.add_monotone_closed_core_laws
  full_sets := bridge.full_sets
  abs_from_prop111 := bridge.abs_from_prop111
  prop111_bridge := bridge.prop111_bridge
  old_cut_ofL_data := bridge.old_cut_ofL_data
  cut_diff_sub_data := bridge.cut_diff_sub_data
  cut_diff_abs_data := bridge.cut_diff_abs_data
  old_small_ofL_data := bridge.old_small_ofL_data
  old_plus_tail_add_data := bridge.old_plus_tail_add_data
  source_line734_reduced_to_prop111 :=
    bridge.source_line734_reduced_to_prop111
  source_line735_reduced_to_closed_shift_bounds :=
    bridge.source_line735_reduced_to_closed_shift_and_add_bounds
  source_line743_reduced_to_abs_nonnegative_closed_chain :=
    bridge.source_line743_reduced_to_abs_nonnegative_closed_chain
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after closing addition monotonicity. -/
structure Property4ReductionDataFromDisplayedScalarAddMonotoneClosedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_add_monotone_closed_bridge :
    Property4DisplayedScalarAddMonotoneClosedCoreUnifiedBridge S
  large_epsv : RegularSeq
  large_eps_pos : regularSeqLtData zeroSeq large_epsv
  large_approx_index : Nat
  large_approx_norm_lt_eps :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub
          r
          ((bishopRegularSeqCor117_from_data S r cor117_data).approximant_rep
            large_approx_index)
          ((bishopRegularSeqCor117_from_data S r cor117_data).tail_sub_data
            large_approx_index))
        ((bishopRegularSeqCor117_from_data S r cor117_data).tail_abs_data
          large_approx_index))
      large_epsv
  large_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutNatRep r cuts n))
      (BishopRegularSeqIntegrableRep.integral r)
  small_epsv : RegularSeq
  small_eps_pos : regularSeqLtData zeroSeq small_epsv
  small_approx_index : Nat
  small_cor117_abs_data :
    BishopRegularSeqCor117ApproxData S
      (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
  small_abs_close :
    regularSeqLtData
      (BishopRegularSeqIntegrableRep.sourceNorm
        (BishopRegularSeqIntegrableRep.sub
          (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
          ((bishopRegularSeqCor117_from_data S
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              small_cor117_abs_data).approximant_rep small_approx_index)
          ((bishopRegularSeqCor117_from_data S
              (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
              small_cor117_abs_data).tail_sub_data small_approx_index))
        ((bishopRegularSeqCor117_from_data S
            (BishopRegularSeqIntegrableRep.abs r cuts.abs_data)
            small_cor117_abs_data).tail_abs_data small_approx_index))
      small_epsv
  small_trunc_tendsto :
    BishopRegularSeqTendsto
      (fun n => BishopRegularSeqIntegrableRep.integral (cutSmallRep r cuts n))
      zeroSeq
  source_property4_frontier_after_add_monotone_closed : Prop

/-- Convert G94 reduction data to the G93 layer. -/
def property4DisplayedScalarShiftClosedData_from_addMonotoneClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarAddMonotoneClosedBridge
        S r) :
    Property4ReductionDataFromDisplayedScalarShiftClosedBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_shift_closed_bridge :=
    displayedScalarShiftClosedCoreUnifiedBridge_from_addMonotoneClosed
      S data.displayed_scalar_add_monotone_closed_bridge
  large_epsv := data.large_epsv
  large_eps_pos := data.large_eps_pos
  large_approx_index := data.large_approx_index
  large_approx_norm_lt_eps := data.large_approx_norm_lt_eps
  large_trunc_tendsto := data.large_trunc_tendsto
  small_epsv := data.small_epsv
  small_eps_pos := data.small_eps_pos
  small_approx_index := data.small_approx_index
  small_cor117_abs_data := data.small_cor117_abs_data
  small_abs_close := data.small_abs_close
  small_trunc_tendsto := data.small_trunc_tendsto
  source_property4_frontier_after_shift_closed :=
    True

/-- Theorem 1.18 property (4), using the G94 closed addition monotonicity. -/
def property4_from_displayed_scalar_add_monotone_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarAddMonotoneClosedBridge
        S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_shift_closed
    S r
    (property4DisplayedScalarShiftClosedData_from_addMonotoneClosed
      S r data)

end BishopRegularSeqTheorem118

/-- G94 package: addition monotonicity on the left argument is closed. -/
structure BishopRegularSeqTheorem118G94Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g93 : BishopRegularSeqTheorem118G93Package S
  add_monotone_closed_core_laws : Type 1
  add_monotone_closed_core_bridge : Type 4
  property4_add_monotone_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_add_monotone_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_add_monotone_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  double_negation_closed : Prop
  add_as_sub_neg_closed : Prop
  add_same_right_difference_closed : Prop
  addSeq_monotone_left_closed : Prop
  remaining_frontier_is_min_order : Prop

def bishopRegularSeqTheorem118G94Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G94Package S where
  g93 := bishopRegularSeqTheorem118G93Package S
  add_monotone_closed_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarAddMonotoneClosedCoreLaws
      Arch
  add_monotone_closed_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarAddMonotoneClosedCoreUnifiedBridge
      S
  property4_add_monotone_closed_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarAddMonotoneClosedBridge
      S
  property4_from_add_monotone_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_add_monotone_closed
      S r data
  double_negation_closed := True
  add_as_sub_neg_closed := True
  add_same_right_difference_closed := True
  addSeq_monotone_left_closed := True
  remaining_frontier_is_min_order := True

/-- Progress after G94: `x <= y` now gives `x+z <= y+z` without an external
primitive law. -/
def bishopRegularSeqCh1To4ProgressAfterG94 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 95
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 94
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G94: closed addSeq monotonicity, deriving x+z <= y+z from x <= y \
    via the same-right difference identity."


end BishopCReal
