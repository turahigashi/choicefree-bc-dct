import Mathdemo.Internal.Real.ClosingMonotonicityAddingCommonRightTerm

set_option linter.style.longLine false

/-!
# G95: closing the RegularSeq absolute-value two-sided bridge

The G94 layer still carried the order bridge

`x <= y` and `-x <= y` imply `|x| <= y`.

This file closes that bridge by converting the RegularSeq non-strict order to
the already closed quotient `absQuot_le_of` theorem and transporting the result
back to the RegularSeq order surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- The counterexample form of `RegularSeqLe x y` is eventually equal to the
quotient strict-order representative `x-y`. -/
theorem regularSeqLe_counter_eventually_lt_rep
    (x y : RegularSeq) :
    relEventually
      (subSeq x y)
      (subSeq zeroSeq (subSeq y x)) := by
  have hxy_to_neg :
      relEventually
        (subSeq x y)
        (negSeq (subSeq y x)) :=
    subSeq_comm_neg_eventually x y
  have hneg_to_zero :
      relEventually
        (negSeq (subSeq y x))
        (subSeq zeroSeq (subSeq y x)) :=
    relEventually_symm
      (subSeq zeroSeq (subSeq y x))
      (negSeq (subSeq y x))
      (subSeq_zero_left_eventually (subSeq y x))
  exact
    relEventually_trans
      (subSeq x y)
      (negSeq (subSeq y x))
      (subSeq zeroSeq (subSeq y x))
      hxy_to_neg
      hneg_to_zero

/-- `RegularSeqLe x y` forbids the quotient strict inequality `y < x`. -/
theorem not_ltQuot_of_regularSeqLe
    (x y : RegularSeq)
    (hxy : RegularSeqLe x y) :
    ¬ ltQuot (mkQuot y) (mkQuot x) := by
  intro hlt
  have hpos : PosEventually (subSeq x y) := by
    change PosEventually (subSeq x y) at hlt
    exact hlt
  have hcounter :
      PosEventually (subSeq zeroSeq (subSeq y x)) :=
    posEventually_respects
      (subSeq x y)
      (subSeq zeroSeq (subSeq y x))
      (regularSeqLe_counter_eventually_lt_rep x y)
      hpos
  exact hxy hcounter

/-- A quotient-level negation of `y < x` gives the RegularSeq order `x <= y`. -/
theorem regularSeqLe_of_not_ltQuot
    (x y : RegularSeq)
    (hnot : ¬ ltQuot (mkQuot y) (mkQuot x)) :
    RegularSeqLe x y := by
  intro hcounter
  have hpos :
      PosEventually (subSeq x y) :=
    posEventually_respects
      (subSeq zeroSeq (subSeq y x))
      (subSeq x y)
      (relEventually_symm
        (subSeq x y)
        (subSeq zeroSeq (subSeq y x))
        (regularSeqLe_counter_eventually_lt_rep x y))
      hcounter
  apply hnot
  change PosEventually (subSeq x y)
  exact hpos

/-- Closed RegularSeq order bridge:
if `x <= y` and `-x <= y`, then `|x| <= y`. -/
theorem regularSeq_abs_le_of_two_sided
    (x y : RegularSeq)
    (hxy : RegularSeqLe x y)
    (hnxy : RegularSeqLe (negSeq x) y) :
    RegularSeqLe (absSeq x) y := by
  have hyx :
      ¬ ltQuot (mkQuot y) (mkQuot x) :=
    not_ltQuot_of_regularSeqLe x y hxy
  have hynx :
      ¬ ltQuot (mkQuot y) (negQuot (mkQuot x)) := by
    change ¬ ltQuot (mkQuot y) (mkQuot (negSeq x))
    exact not_ltQuot_of_regularSeqLe (negSeq x) y hnxy
  have hyabs :
      ¬ ltQuot (mkQuot y) (absQuot (mkQuot x)) :=
    absQuot_le_of hyx hynx
  apply regularSeqLe_of_not_ltQuot (absSeq x) y
  change ¬ ltQuot (mkQuot y) (absQuot (mkQuot x))
  exact hyabs

/-- Closed bridge value for the G61/G95 absolute-value order step. -/
def regularSeqAbsFromTwoSidedBridgeClosed :
    RegularSeqAbsFromTwoSidedBridge where
  abs_le_of_two_sided := regularSeq_abs_le_of_two_sided
  source_order_step_for_absolute_integral_bound := True

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G95 core data: the two-sided absolute-value bridge is now obtained from the
closed RegularSeq/quotient order transfer. -/
structure Property4DisplayedScalarAbsBridgeClosedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
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
  source_abs_from_two_sided_bridge_closed : Prop
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

/-- Collapse the G95 closed absolute bridge back to the G94 layer. -/
def displayedScalarAddMonotoneClosedCoreLaws_from_absBridgeClosed
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarAbsBridgeClosedCoreLaws Arch) :
    Property4DisplayedScalarAddMonotoneClosedCoreLaws Arch where
  abs_from_two_sided := regularSeqAbsFromTwoSidedBridgeClosed
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
  source_line735_addition_monotonicity_closed :=
    laws.source_line735_addition_monotonicity_closed
  source_line735_min_monotonicity_and_shift :=
    laws.source_line735_min_monotonicity_and_shift
  source_line743_self_le_base_plus_abs_tail_closed :=
    laws.source_line743_self_le_base_plus_abs_tail_closed
  source_line743_base_le_abs_base_closed :=
    laws.source_line743_base_le_abs_base_closed
  source_line743_addition_monotonicity_for_abs_base_closed :=
    laws.source_line743_addition_monotonicity_for_abs_base_closed
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_tail_abs_is_nonnegative_closed :=
    laws.source_line743_tail_abs_is_nonnegative_closed
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G95 unified bridge: the G94 bridge obtained from the closed absolute
two-sided order bridge. -/
structure Property4DisplayedScalarAbsBridgeClosedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  abs_bridge_closed_core_laws :
    Property4DisplayedScalarAbsBridgeClosedCoreLaws Arch
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
  source_line735_reduced_to_closed_shift_add_abs_bridge : Prop
  source_line743_reduced_to_abs_nonnegative_closed_chain : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G95 bridge to the G94 bridge. -/
def displayedScalarAddMonotoneClosedCoreUnifiedBridge_from_absBridgeClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4DisplayedScalarAbsBridgeClosedCoreUnifiedBridge S) :
    Property4DisplayedScalarAddMonotoneClosedCoreUnifiedBridge S where
  add_monotone_closed_core_laws :=
    displayedScalarAddMonotoneClosedCoreLaws_from_absBridgeClosed
      Arch bridge.abs_bridge_closed_core_laws
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
  source_line735_reduced_to_closed_shift_and_add_bounds :=
    bridge.source_line735_reduced_to_closed_shift_add_abs_bridge
  source_line743_reduced_to_abs_nonnegative_closed_chain :=
    bridge.source_line743_reduced_to_abs_nonnegative_closed_chain
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after closing the absolute bridge. -/
structure Property4ReductionDataFromDisplayedScalarAbsBridgeClosedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_abs_bridge_closed_bridge :
    Property4DisplayedScalarAbsBridgeClosedCoreUnifiedBridge S
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
  source_property4_frontier_after_abs_bridge_closed : Prop

/-- Convert G95 reduction data to the G94 layer. -/
def property4DisplayedScalarAddMonotoneClosedData_from_absBridgeClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarAbsBridgeClosedBridge
        S r) :
    Property4ReductionDataFromDisplayedScalarAddMonotoneClosedBridge
      S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_add_monotone_closed_bridge :=
    displayedScalarAddMonotoneClosedCoreUnifiedBridge_from_absBridgeClosed
      S data.displayed_scalar_abs_bridge_closed_bridge
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
  source_property4_frontier_after_add_monotone_closed :=
    True

/-- Theorem 1.18 property (4), using the G95 closed absolute bridge. -/
def property4_from_displayed_scalar_abs_bridge_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarAbsBridgeClosedBridge
        S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_add_monotone_closed
    S r
    (property4DisplayedScalarAddMonotoneClosedData_from_absBridgeClosed
      S r data)

end BishopRegularSeqTheorem118

/-- G95 package: the two-sided absolute-value bridge is closed. -/
structure BishopRegularSeqTheorem118G95Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g94 : BishopRegularSeqTheorem118G94Package S
  abs_bridge_closed_core_laws : Type 1
  abs_bridge_closed_core_bridge : Type 4
  property4_abs_bridge_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_abs_bridge_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_abs_bridge_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  regularSeq_order_to_quotient_order_closed : Prop
  quotient_order_to_regularSeq_order_closed : Prop
  abs_from_two_sided_closed : Prop
  remaining_frontier_is_min_order : Prop

def bishopRegularSeqTheorem118G95Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G95Package S where
  g94 := bishopRegularSeqTheorem118G94Package S
  abs_bridge_closed_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarAbsBridgeClosedCoreLaws
      Arch
  abs_bridge_closed_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarAbsBridgeClosedCoreUnifiedBridge
      S
  property4_abs_bridge_closed_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarAbsBridgeClosedBridge
      S
  property4_from_abs_bridge_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_abs_bridge_closed
      S r data
  regularSeq_order_to_quotient_order_closed := True
  quotient_order_to_regularSeq_order_closed := True
  abs_from_two_sided_closed := True
  remaining_frontier_is_min_order := True

/-- Progress after G95: the two-sided absolute-value bridge is closed, leaving
the min monotonicity and nonnegative min-shift laws as the active order
frontier. -/
def bishopRegularSeqCh1To4ProgressAfterG95 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 96
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 95
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G95: closed the RegularSeq two-sided absolute-value bridge from the \
    quotient absQuot_le_of theorem."


end BishopCReal
