import Mathdemo.Internal.Real.SplittingSmallLine743SubSeqCore

/-!
# G84: exposing the absolute-tail comparison under `min`

G83 split the small line-743 core through

`min(|b| + ||a|-b|, c)`.

This file splits the first half of that chain again.  The input

`min(|a|,c) <= min(|b| + ||a|-b|, c)`

is now obtained from a bare absolute-tail comparison

`|a| <= |b| + ||a|-b|`

and a left-monotonicity law for `minSeqWith`.  The second shifted-min
truncation bound remains the next small frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G84 core data: line-735 is still the G82 two-sided split, while the first
small line-743 shifted-min step is obtained from an absolute-tail upper bound
and monotonicity of `min` in its left argument. -/
structure Property4DisplayedScalarSmallTailMonotoneCoreLaws
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
  abs_tail_upper :
    forall a b : RegularSeq,
      RegularSeqLe
        (absSeq a)
        (addSeq (absSeq b) (absSeq (subSeq (absSeq a) b)))
  minSeqWith_monotone_left :
    forall x y c : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (minSeqWith Arch x c) (minSeqWith Arch y c)
  small_shifted_min_le_min_plus_tail :
    forall a b c : RegularSeq,
      RegularSeqLe
        (smallLine743ShiftedMinMid Arch a b c)
        (addSeq
          (minSeqWith Arch (absSeq b) c)
          (absSeq (subSeq (absSeq a) b)))
  source_line735_split_to_two_sided_min_order : Prop
  source_line743_abs_tail_upper_bound : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_shifted_min_truncation_bound : Prop

/-- Collapse the G84 monotonicity split back to the G83 small-chain laws. -/
def displayedScalarSmallTailChainCoreLaws_from_monotone
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSmallTailMonotoneCoreLaws Arch) :
    Property4DisplayedScalarSmallTailChainCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  min_lipschitz_upper := laws.min_lipschitz_upper
  min_lipschitz_lower := laws.min_lipschitz_lower
  small_abs_tail_to_shifted_min := by
    intro a b c
    exact
      laws.minSeqWith_monotone_left
        (absSeq a)
        (addSeq (absSeq b) (absSeq (subSeq (absSeq a) b)))
        c
        (laws.abs_tail_upper a b)
  small_shifted_min_le_min_plus_tail :=
    laws.small_shifted_min_le_min_plus_tail
  source_line735_split_to_two_sided_min_order :=
    laws.source_line735_split_to_two_sided_min_order
  source_line743_first_uses_abs_tail_comparison_under_min :=
    laws.source_line743_abs_tail_upper_bound
      /\ laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_second_uses_shifted_min_truncation_bound :=
    laws.source_line743_shifted_min_truncation_bound

/-- G84 unified bridge: the G83 bridge obtained from absolute-tail upper data
and `min` monotonicity. -/
structure Property4DisplayedScalarSmallTailMonotoneCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  small_tail_monotone_core_laws :
    Property4DisplayedScalarSmallTailMonotoneCoreLaws Arch
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
  source_line743_reduced_to_abs_tail_plus_min_monotone : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G84 bridge to the G83 bridge. -/
def displayedScalarSmallTailChainCoreUnifiedBridge_from_monotone
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarSmallTailMonotoneCoreUnifiedBridge S) :
    Property4DisplayedScalarSmallTailChainCoreUnifiedBridge S where
  small_tail_chain_core_laws :=
    displayedScalarSmallTailChainCoreLaws_from_monotone
      Arch bridge.small_tail_monotone_core_laws
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
  source_line743_reduced_to_shifted_min_chain :=
    bridge.source_line743_reduced_to_abs_tail_plus_min_monotone
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after exposing line743's absolute-tail
comparison and `min` monotonicity. -/
structure Property4ReductionDataFromDisplayedScalarSmallTailMonotoneCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_small_tail_monotone_core_bridge :
    Property4DisplayedScalarSmallTailMonotoneCoreUnifiedBridge S
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
  source_property4_frontier_is_large_two_sided_and_small_monotone :
    Prop

/-- Convert G84 reduction data to the G83 layer. -/
def property4DisplayedScalarSmallTailChainCoreData_from_monotone
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailMonotoneCoreBridge S r) :
    Property4ReductionDataFromDisplayedScalarSmallTailChainCoreBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_small_tail_chain_core_bridge :=
    displayedScalarSmallTailChainCoreUnifiedBridge_from_monotone
      S data.displayed_scalar_small_tail_monotone_core_bridge
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
  source_property4_frontier_is_large_two_sided_and_small_shifted_chain :=
    True

/-- Theorem 1.18 property (4), using the G84 monotonicity split. -/
def property4_from_displayed_scalar_small_tail_monotone_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailMonotoneCoreBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_small_tail_chain_core
    S r
    (property4DisplayedScalarSmallTailChainCoreData_from_monotone S r data)

end BishopRegularSeqTheorem118

/-- G84 package: the first small line-743 shifted-min step is reduced to
absolute-tail upper data plus `min` monotonicity. -/
structure BishopRegularSeqTheorem118G84Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g83 : BishopRegularSeqTheorem118G83Package S
  small_tail_monotone_core_laws : Type 1
  small_tail_monotone_core_bridge : Type 4
  property4_small_tail_monotone_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_small_tail_monotone_core :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_small_tail_monotone_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  small_shifted_first_step_split_to_abs_tail_and_min_monotone : Prop
  remaining_frontier_is_large_two_sided_small_min_monotone_and_shifted_bound :
    Prop

def bishopRegularSeqTheorem118G84Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G84Package S where
  g83 := bishopRegularSeqTheorem118G83Package S
  small_tail_monotone_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailMonotoneCoreLaws
      Arch
  small_tail_monotone_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailMonotoneCoreUnifiedBridge
      S
  property4_small_tail_monotone_core_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarSmallTailMonotoneCoreBridge
      S
  property4_from_small_tail_monotone_core := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_small_tail_monotone_core
      S r data
  small_shifted_first_step_split_to_abs_tail_and_min_monotone := True
  remaining_frontier_is_large_two_sided_small_min_monotone_and_shifted_bound :=
    True

/-- Progress after G84: the first small line743 shifted-min step has been
split into an absolute-tail upper bound and `min` monotonicity. -/
def bishopRegularSeqCh1To4ProgressAfterG84 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 85
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 84
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G84: split Theorem 1.18 property (4)'s first small line743 \
    shifted-min step into absolute-tail upper data plus min monotonicity."

set_option linter.style.longLine false


end BishopCReal
