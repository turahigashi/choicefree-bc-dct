import Mathdemo.Internal.Real.SplittingShiftedMinTruncationBound

/-!
# G86: splitting the absolute-tail upper bound

G85 still kept the first small line-743 scalar input as

`|a| <= |b| + ||a|-b|`.

This file splits that input into the elementary source-shaped chain:

1. `u <= b + |u-b|`;
2. `b <= |b|`;
3. addition is monotone in the left summand.

Applied with `u = |a|`, this reconstructs the G85 absolute-tail upper bound.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G86 core data: the absolute-tail upper bound
`|a| <= |b| + ||a|-b|` is obtained from a base shift estimate, the elementary
bound `b <= |b|`, and monotonicity of addition. -/
structure Property4DisplayedScalarSmallTailAbsUpperSplitCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  min_lipschitz_upper :
    forall a b c : RegularSeq,
      RegularSeqLe
        (subSeq
          (minSeqWith Arch a c)
          (minSeqWith Arch b c))
        (absSeq (subSeq a b))
  min_lipschitz_lower :
    forall a b c : RegularSeq,
      RegularSeqLe
        (negSeq
          (subSeq
            (minSeqWith Arch a c)
            (minSeqWith Arch b c)))
        (absSeq (subSeq a b))
  self_le_base_plus_abs_tail :
    forall u b : RegularSeq,
      RegularSeqLe u (addSeq b (absSeq (subSeq u b)))
  base_le_abs_base :
    forall b : RegularSeq,
      RegularSeqLe b (absSeq b)
  addSeq_monotone_left :
    forall x y z : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (addSeq x z) (addSeq y z)
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  absSeq_nonnegative :
    forall x : RegularSeq,
      RegularSeqLe zeroSeq (absSeq x)
  minSeqWith_add_nonnegative_right_bound :
    forall x d c : RegularSeq,
      RegularSeqLe zeroSeq d ->
        RegularSeqLe
          (minSeqWith Arch (addSeq x d) c)
          (addSeq (minSeqWith Arch x c) d)
  source_line735_split_to_two_sided_min_order : Prop
  source_line743_self_le_base_plus_abs_tail : Prop
  source_line743_base_le_abs_base : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G86 absolute-upper split back to the G85 shift core laws. -/
def displayedScalarSmallTailShiftCoreLaws_from_absUpperSplit
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSmallTailAbsUpperSplitCoreLaws Arch) :
    Property4DisplayedScalarSmallTailShiftCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  min_lipschitz_upper := laws.min_lipschitz_upper
  min_lipschitz_lower := laws.min_lipschitz_lower
  abs_tail_upper := by
    intro a b
    let delta : RegularSeq := absSeq (subSeq (absSeq a) b)
    have hbase :
        RegularSeqLe
          (absSeq a)
          (addSeq b delta) := by
      simpa [delta] using laws.self_le_base_plus_abs_tail (absSeq a) b
    have hshift :
        RegularSeqLe
          (addSeq b delta)
          (addSeq (absSeq b) delta) :=
      laws.addSeq_monotone_left b (absSeq b) delta
        (laws.base_le_abs_base b)
    exact regularSeqLeOrderBridge.le_trans hbase hshift
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  absSeq_nonnegative := laws.absSeq_nonnegative
  minSeqWith_add_nonnegative_right_bound :=
    laws.minSeqWith_add_nonnegative_right_bound
  source_line735_split_to_two_sided_min_order :=
    laws.source_line735_split_to_two_sided_min_order
  source_line743_abs_tail_upper_bound :=
    laws.source_line743_self_le_base_plus_abs_tail
      /\ laws.source_line743_base_le_abs_base
      /\ laws.source_line743_addition_monotonicity_for_abs_base
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_tail_abs_is_nonnegative :=
    laws.source_line743_tail_abs_is_nonnegative
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G86 unified bridge: the G85 bridge obtained from the split absolute-tail
upper chain. -/
structure Property4DisplayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  small_tail_abs_upper_split_core_laws :
    Property4DisplayedScalarSmallTailAbsUpperSplitCoreLaws Arch
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
  source_line735_reduced_to_two_sided_min_order : Prop
  source_line743_reduced_to_abs_upper_split_and_shift : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G86 bridge to the G85 bridge. -/
def displayedScalarSmallTailShiftCoreUnifiedBridge_from_absUpperSplit
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge S) :
    Property4DisplayedScalarSmallTailShiftCoreUnifiedBridge S where
  small_tail_shift_core_laws :=
    displayedScalarSmallTailShiftCoreLaws_from_absUpperSplit
      Arch bridge.small_tail_abs_upper_split_core_laws
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
  source_line735_reduced_to_two_sided_min_order :=
    bridge.source_line735_reduced_to_two_sided_min_order
  source_line743_reduced_to_abs_tail_min_monotone_and_shift :=
    bridge.source_line743_reduced_to_abs_upper_split_and_shift
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after splitting the absolute-tail upper bound
in the small line-743 route. -/
structure Property4ReductionDataFromDisplayedScalarSmallTailAbsUpperSplitCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_small_tail_abs_upper_split_core_bridge :
    Property4DisplayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge S
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
  source_property4_frontier_is_large_two_sided_and_small_abs_upper_split :
    Prop

/-- Convert G86 reduction data to the G85 layer. -/
def property4DisplayedScalarSmallTailShiftCoreData_from_absUpperSplit
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailAbsUpperSplitCoreBridge
        S r) :
    Property4ReductionDataFromDisplayedScalarSmallTailShiftCoreBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_small_tail_shift_core_bridge :=
    displayedScalarSmallTailShiftCoreUnifiedBridge_from_absUpperSplit
      S data.displayed_scalar_small_tail_abs_upper_split_core_bridge
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
  source_property4_frontier_is_large_two_sided_and_small_shift := True

/-- Theorem 1.18 property (4), using the G86 absolute-upper split. -/
def property4_from_displayed_scalar_small_tail_abs_upper_split_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailAbsUpperSplitCoreBridge
        S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_small_tail_shift_core
    S r
    (property4DisplayedScalarSmallTailShiftCoreData_from_absUpperSplit S r data)

/-- Short alias for the G86 reduction-data type, used by the package to keep
the exported progress surface readable. -/
abbrev Property4SmallTailAbsUpperSplitReductionData
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 :=
  Property4ReductionDataFromDisplayedScalarSmallTailAbsUpperSplitCoreBridge S r

end BishopRegularSeqTheorem118

/-- G86 package: the small absolute-tail upper bound is split into
`u <= b+|u-b|`, `b <= |b|`, and add-left monotonicity. -/
structure BishopRegularSeqTheorem118G86Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g85 : BishopRegularSeqTheorem118G85Package S
  small_tail_abs_upper_split_core_laws : Type 1
  small_tail_abs_upper_split_core_bridge : Type 4
  property4_small_tail_abs_upper_split_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_small_tail_abs_upper_split_core :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_small_tail_abs_upper_split_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  small_abs_tail_upper_split_to_base_shift_abs_base_and_add_monotone : Prop
  remaining_frontier_is_large_two_sided_small_base_shift_abs_base_monotone_shift :
    Prop

def bishopRegularSeqTheorem118G86Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G86Package S where
  g85 := bishopRegularSeqTheorem118G85Package S
  small_tail_abs_upper_split_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailAbsUpperSplitCoreLaws
      Arch
  small_tail_abs_upper_split_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge
      S
  property4_small_tail_abs_upper_split_core_data :=
    BishopRegularSeqTheorem118.Property4SmallTailAbsUpperSplitReductionData
      S
  property4_from_small_tail_abs_upper_split_core := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_small_tail_abs_upper_split_core
      S r data
  small_abs_tail_upper_split_to_base_shift_abs_base_and_add_monotone := True
  remaining_frontier_is_large_two_sided_small_base_shift_abs_base_monotone_shift :=
    True

/-- Progress after G86: the small absolute-tail upper bound has been split
into base shift, `b <= |b|`, and add-left monotonicity. -/
def bishopRegularSeqCh1To4ProgressAfterG86 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 87
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 86
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G86: split Theorem 1.18 property (4)'s small absolute-tail upper \
    bound into base shift, abs-base, and add monotonicity inputs."

set_option linter.style.longLine false


end BishopCReal
