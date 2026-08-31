import Mathdemo.Internal.Real.SplittingAbsoluteTailUpperBound

set_option linter.style.longLine false

/-!
# G87: add-bound presentation of the large line-735 one-sided laws

G82 split the large line-735 min-Lipschitz inequality into two one-sided
`subSeq` inequalities.  This file exposes the source-shaped add-bound form
behind those one-sided laws:

`min(a,c) <= min(b,c) + |a-b|`

and the swapped version.  A general bridge

`x <= y+z -> x-y <= z`

collapses these add-bound inputs back to G86's `subSeq` surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G87 core data: the large line-735 one-sided min-order laws are supplied in
the add-bound form closer to the displayed source estimate. -/
structure Property4DisplayedScalarLargeAddBoundCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  sub_le_of_add_bound :
    forall x y z : RegularSeq,
      RegularSeqLe x (addSeq y z) ->
        RegularSeqLe (subSeq x y) z
  large_min_add_upper :
    forall a b c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch a c)
        (addSeq
          (minSeqWith Arch b c)
          (absSeq (subSeq a b)))
  large_min_add_lower :
    forall a b c : RegularSeq,
      RegularSeqLe
        (minSeqWith Arch b c)
        (addSeq
          (minSeqWith Arch a c)
          (absSeq (subSeq a b)))
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
  source_line735_add_bound_upper : Prop
  source_line735_add_bound_lower : Prop
  source_line735_add_bound_to_subSeq_order : Prop
  source_line743_self_le_base_plus_abs_tail : Prop
  source_line743_base_le_abs_base : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G87 add-bound presentation back to the G86 split-core laws. -/
def displayedScalarSmallTailAbsUpperSplitCoreLaws_from_largeAddBound
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarLargeAddBoundCoreLaws Arch) :
    Property4DisplayedScalarSmallTailAbsUpperSplitCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  min_lipschitz_upper := by
    intro a b c
    exact
      laws.sub_le_of_add_bound
        (minSeqWith Arch a c)
        (minSeqWith Arch b c)
        (absSeq (subSeq a b))
        (laws.large_min_add_upper a b c)
  min_lipschitz_lower := by
    intro a b c
    have hswap :
        RegularSeqLe
          (subSeq
            (minSeqWith Arch b c)
            (minSeqWith Arch a c))
          (absSeq (subSeq a b)) :=
      laws.sub_le_of_add_bound
        (minSeqWith Arch b c)
        (minSeqWith Arch a c)
        (absSeq (subSeq a b))
        (laws.large_min_add_lower a b c)
    have hleft :
        relEventually
          (negSeq
            (subSeq
              (minSeqWith Arch a c)
              (minSeqWith Arch b c)))
          (subSeq
            (minSeqWith Arch b c)
            (minSeqWith Arch a c)) :=
      relEventually_symm
        (subSeq
          (minSeqWith Arch b c)
          (minSeqWith Arch a c))
        (negSeq
          (subSeq
            (minSeqWith Arch a c)
            (minSeqWith Arch b c)))
        (subSeq_comm_neg_eventually
          (minSeqWith Arch b c)
          (minSeqWith Arch a c))
    exact regularSeqLe_of_left_eventual hleft hswap
  self_le_base_plus_abs_tail := laws.self_le_base_plus_abs_tail
  base_le_abs_base := laws.base_le_abs_base
  addSeq_monotone_left := laws.addSeq_monotone_left
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  absSeq_nonnegative := laws.absSeq_nonnegative
  minSeqWith_add_nonnegative_right_bound :=
    laws.minSeqWith_add_nonnegative_right_bound
  source_line735_split_to_two_sided_min_order :=
    laws.source_line735_add_bound_upper
      /\ laws.source_line735_add_bound_lower
      /\ laws.source_line735_add_bound_to_subSeq_order
  source_line743_self_le_base_plus_abs_tail :=
    laws.source_line743_self_le_base_plus_abs_tail
  source_line743_base_le_abs_base :=
    laws.source_line743_base_le_abs_base
  source_line743_addition_monotonicity_for_abs_base :=
    laws.source_line743_addition_monotonicity_for_abs_base
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_tail_abs_is_nonnegative :=
    laws.source_line743_tail_abs_is_nonnegative
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G87 unified bridge: the G86 bridge obtained from add-bound large-min
inputs. -/
structure Property4DisplayedScalarLargeAddBoundCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_add_bound_core_laws :
    Property4DisplayedScalarLargeAddBoundCoreLaws Arch
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
  source_line735_reduced_to_add_bound_min_order : Prop
  source_line743_reduced_to_abs_upper_split_and_shift : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G87 bridge to the G86 bridge. -/
def displayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge_from_largeAddBound
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarLargeAddBoundCoreUnifiedBridge S) :
    Property4DisplayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge S where
  small_tail_abs_upper_split_core_laws :=
    displayedScalarSmallTailAbsUpperSplitCoreLaws_from_largeAddBound
      Arch bridge.large_add_bound_core_laws
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
    bridge.source_line735_reduced_to_add_bound_min_order
  source_line743_reduced_to_abs_upper_split_and_shift :=
    bridge.source_line743_reduced_to_abs_upper_split_and_shift
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after replacing the large `subSeq` one-sided
frontier by add-bound large-min inputs. -/
structure Property4ReductionDataFromDisplayedScalarLargeAddBoundCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_large_add_bound_core_bridge :
    Property4DisplayedScalarLargeAddBoundCoreUnifiedBridge S
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
  source_property4_frontier_is_large_add_bound_and_small_abs_upper_split :
    Prop

/-- Convert G87 reduction data to the G86 layer. -/
def property4DisplayedScalarSmallTailAbsUpperSplitCoreData_from_largeAddBound
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarLargeAddBoundCoreBridge S r) :
    Property4ReductionDataFromDisplayedScalarSmallTailAbsUpperSplitCoreBridge
      S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_small_tail_abs_upper_split_core_bridge :=
    displayedScalarSmallTailAbsUpperSplitCoreUnifiedBridge_from_largeAddBound
      S data.displayed_scalar_large_add_bound_core_bridge
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
  source_property4_frontier_is_large_two_sided_and_small_abs_upper_split :=
    True

/-- Theorem 1.18 property (4), using the G87 large add-bound split. -/
def property4_from_displayed_scalar_large_add_bound_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarLargeAddBoundCoreBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_small_tail_abs_upper_split_core
    S r
    (property4DisplayedScalarSmallTailAbsUpperSplitCoreData_from_largeAddBound
      S r data)

end BishopRegularSeqTheorem118

/-- G87 package: the large line-735 one-sided `subSeq` laws are replaced by
source-shaped add-bound min inequalities. -/
structure BishopRegularSeqTheorem118G87Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g86 : BishopRegularSeqTheorem118G86Package S
  large_add_bound_core_laws : Type 1
  large_add_bound_core_bridge : Type 4
  property4_large_add_bound_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_large_add_bound_core :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_add_bound_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  large_subSeq_order_reduced_to_add_bound_min_order : Prop
  remaining_frontier_is_large_add_bound_and_small_primitive_order_laws : Prop

def bishopRegularSeqTheorem118G87Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G87Package S where
  g86 := bishopRegularSeqTheorem118G86Package S
  large_add_bound_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarLargeAddBoundCoreLaws
      Arch
  large_add_bound_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarLargeAddBoundCoreUnifiedBridge
      S
  property4_large_add_bound_core_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarLargeAddBoundCoreBridge
      S
  property4_from_large_add_bound_core := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_large_add_bound_core
      S r data
  large_subSeq_order_reduced_to_add_bound_min_order := True
  remaining_frontier_is_large_add_bound_and_small_primitive_order_laws := True

/-- Progress after G87: the large line735 one-sided `subSeq` laws have been
replaced by source-shaped add-bound min-order inputs. -/
def bishopRegularSeqCh1To4ProgressAfterG87 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 88
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 87
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G87: replaced Theorem 1.18 property (4)'s large line735 one-sided \
    subSeq min-order frontier by add-bound min-order inputs."


end BishopCReal
