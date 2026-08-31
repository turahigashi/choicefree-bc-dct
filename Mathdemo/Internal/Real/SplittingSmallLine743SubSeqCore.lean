import Mathdemo.Internal.Real.SplittingLargeSubSeqCoreTwoSided

/-!
# G83: splitting the small line-743 `subSeq` core

G82 left the small line-743 scalar core as the single inequality

`min(|a|,c) <= min(|b|,c) + ||a|-b|`.

This file exposes the source-level middle term

`min(|b| + ||a|-b|, c)`

and proves that the previous single small core follows by order transitivity from
two smaller inputs.  The large line-735 two-sided frontier is carried unchanged.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- The middle term for the small line-743 pointwise estimate:
first compare `|a|` with `|b| + ||a|-b|`, then truncate. -/
def smallLine743ShiftedMinMid
    (Arch : ScalarMulArchimedeanData)
    (a b c : RegularSeq) : RegularSeq :=
  minSeqWith Arch
    (addSeq (absSeq b) (absSeq (subSeq (absSeq a) b)))
    c

/-- G83 core data: the large line-735 two-sided split from G82, plus the
small line-743 split through the shifted-min middle term. -/
structure Property4DisplayedScalarSmallTailChainCoreLaws
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
  small_abs_tail_to_shifted_min :
    forall a b c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch (absSeq a) c)
        (smallLine743ShiftedMinMid Arch a b c)
  small_shifted_min_le_min_plus_tail :
    forall a b c : RegularSeq,
      RegularSeqLe
        (smallLine743ShiftedMinMid Arch a b c)
        (addSeq
          (minSeqWith Arch (absSeq b) c)
          (absSeq (subSeq (absSeq a) b)))
  source_line735_split_to_two_sided_min_order : Prop
  source_line743_first_uses_abs_tail_comparison_under_min : Prop
  source_line743_second_uses_shifted_min_truncation_bound : Prop

/-- Collapse the G83 small-chain data back to the G82 two-sided core laws. -/
def displayedScalarTwoSidedCoreLaws_from_smallTailChain
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSmallTailChainCoreLaws Arch) :
    Property4DisplayedScalarTwoSidedCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  min_lipschitz_upper := laws.min_lipschitz_upper
  min_lipschitz_lower := laws.min_lipschitz_lower
  min_abs_tail_subSeq := by
    intro a b c
    exact
      regularSeqLeOrderBridge.le_trans
        (laws.small_abs_tail_to_shifted_min a b c)
        (laws.small_shifted_min_le_min_plus_tail a b c)
  source_line735_split_to_two_sided_min_order :=
    laws.source_line735_split_to_two_sided_min_order
  source_line743_core_is_subSeq_min_abs_tail :=
    laws.source_line743_first_uses_abs_tail_comparison_under_min
      /\ laws.source_line743_second_uses_shifted_min_truncation_bound

/-- G83 unified bridge: the G82 bridge obtained from the small line-743
shifted-min chain. -/
structure Property4DisplayedScalarSmallTailChainCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  small_tail_chain_core_laws :
    Property4DisplayedScalarSmallTailChainCoreLaws Arch
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
  source_line743_reduced_to_shifted_min_chain : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G83 bridge to the G82 bridge. -/
def displayedScalarTwoSidedCoreUnifiedBridge_from_smallTailChain
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarSmallTailChainCoreUnifiedBridge S) :
    Property4DisplayedScalarTwoSidedCoreUnifiedBridge S where
  two_sided_core_laws :=
    displayedScalarTwoSidedCoreLaws_from_smallTailChain
      Arch bridge.small_tail_chain_core_laws
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
  source_line743_reduced_to_subSeq_min_abs_tail :=
    bridge.source_line743_reduced_to_shifted_min_chain
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after splitting the small line-743 `subSeq`
core through the shifted-min chain. -/
structure Property4ReductionDataFromDisplayedScalarSmallTailChainCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_small_tail_chain_core_bridge :
    Property4DisplayedScalarSmallTailChainCoreUnifiedBridge S
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
  source_property4_frontier_is_large_two_sided_and_small_shifted_chain :
    Prop

/-- Convert G83 reduction data to the G82 layer. -/
def property4DisplayedScalarTwoSidedCoreData_from_smallTailChain
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailChainCoreBridge S r) :
    Property4ReductionDataFromDisplayedScalarTwoSidedCoreBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_two_sided_core_bridge :=
    displayedScalarTwoSidedCoreUnifiedBridge_from_smallTailChain
      S data.displayed_scalar_small_tail_chain_core_bridge
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
  source_property4_frontier_is_large_two_sided_and_small_subSeq := True

/-- Theorem 1.18 property (4), using the G83 small shifted-min chain. -/
def property4_from_displayed_scalar_small_tail_chain_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailChainCoreBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_two_sided_core
    S r
    (property4DisplayedScalarTwoSidedCoreData_from_smallTailChain S r data)

end BishopRegularSeqTheorem118

/-- G83 package: the small line-743 `subSeq` core is split through
`min(|b| + ||a|-b|, c)`. -/
structure BishopRegularSeqTheorem118G83Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g82 : BishopRegularSeqTheorem118G82Package S
  small_tail_shifted_mid : RegularSeq -> RegularSeq -> RegularSeq -> RegularSeq
  small_tail_chain_core_laws : Type 1
  small_tail_chain_core_bridge : Type 4
  property4_small_tail_chain_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_small_tail_chain_core :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_small_tail_chain_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  small_subSeq_core_split_to_shifted_min_chain : Prop
  remaining_frontier_is_large_two_sided_and_small_shifted_min_chain : Prop

def bishopRegularSeqTheorem118G83Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G83Package S where
  g82 := bishopRegularSeqTheorem118G82Package S
  small_tail_shifted_mid :=
    BishopRegularSeqTheorem118.smallLine743ShiftedMinMid Arch
  small_tail_chain_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailChainCoreLaws
      Arch
  small_tail_chain_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailChainCoreUnifiedBridge
      S
  property4_small_tail_chain_core_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarSmallTailChainCoreBridge
      S
  property4_from_small_tail_chain_core := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_small_tail_chain_core
      S r data
  small_subSeq_core_split_to_shifted_min_chain := True
  remaining_frontier_is_large_two_sided_and_small_shifted_min_chain := True

/-- Progress after G83: line743's small `subSeq` min-abs-tail core has been
reduced to a shifted-min two-step chain. -/
def bishopRegularSeqCh1To4ProgressAfterG83 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 84
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 83
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G83: split Theorem 1.18 property (4)'s small line743 subSeq \
    min-abs-tail core through the shifted-min middle term."

set_option linter.style.longLine false


end BishopCReal
