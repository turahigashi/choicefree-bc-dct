import Mathdemo.Internal.Real.AddBoundPresentationLargeLine735

set_option linter.style.longLine false

/-!
# G88: generating the large add-bound min laws

G87 replaced the large line-735 one-sided `subSeq` laws by add-bound min
inequalities.  This file splits those add-bound min inequalities into the same
primitive order ingredients already exposed in the small line-743 route:

* `u <= v + |u-v|`;
* `v <= u + |u-v|`;
* monotonicity of `minSeqWith` in the left argument;
* the nonnegative shift law for `min`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G88 core data: the large line-735 add-bound min inequalities are generated
from symmetric absolute-tail shift estimates and `min` monotonicity. -/
structure Property4DisplayedScalarLargeAddBoundGeneratedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  sub_le_of_add_bound :
    forall x y z : RegularSeq,
      RegularSeqLe x (addSeq y z) ->
        RegularSeqLe (subSeq x y) z
  self_le_base_plus_abs_tail :
    forall u b : RegularSeq,
      RegularSeqLe u (addSeq b (absSeq (subSeq u b)))
  base_le_self_plus_abs_tail :
    forall u b : RegularSeq,
      RegularSeqLe b (addSeq u (absSeq (subSeq u b)))
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
  source_line735_self_shift_upper : Prop
  source_line735_base_shift_lower : Prop
  source_line735_min_monotonicity_and_shift : Prop
  source_line735_add_bound_to_subSeq_order : Prop
  source_line743_self_le_base_plus_abs_tail : Prop
  source_line743_base_le_abs_base : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G88 generated large add-bound laws back to the G87 layer. -/
def displayedScalarLargeAddBoundCoreLaws_from_generated
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarLargeAddBoundGeneratedCoreLaws Arch) :
    Property4DisplayedScalarLargeAddBoundCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  sub_le_of_add_bound := laws.sub_le_of_add_bound
  large_min_add_upper := by
    intro a b c
    let delta : RegularSeq := absSeq (subSeq a b)
    have hself :
        RegularSeqLe a (addSeq b delta) := by
      simpa [delta] using laws.self_le_base_plus_abs_tail a b
    have hmin :
        RegularSeqLe
          (minSeqWith Arch a c)
          (minSeqWith Arch (addSeq b delta) c) :=
      laws.minSeqWith_monotone_left a (addSeq b delta) c hself
    have hshift :
        RegularSeqLe
          (minSeqWith Arch (addSeq b delta) c)
          (addSeq (minSeqWith Arch b c) delta) :=
      laws.minSeqWith_add_nonnegative_right_bound b delta c
        (by simpa [delta] using laws.absSeq_nonnegative (subSeq a b))
    exact regularSeqLeOrderBridge.le_trans hmin hshift
  large_min_add_lower := by
    intro a b c
    let delta : RegularSeq := absSeq (subSeq a b)
    have hbase :
        RegularSeqLe b (addSeq a delta) := by
      simpa [delta] using laws.base_le_self_plus_abs_tail a b
    have hmin :
        RegularSeqLe
          (minSeqWith Arch b c)
          (minSeqWith Arch (addSeq a delta) c) :=
      laws.minSeqWith_monotone_left b (addSeq a delta) c hbase
    have hshift :
        RegularSeqLe
          (minSeqWith Arch (addSeq a delta) c)
          (addSeq (minSeqWith Arch a c) delta) :=
      laws.minSeqWith_add_nonnegative_right_bound a delta c
        (by simpa [delta] using laws.absSeq_nonnegative (subSeq a b))
    exact regularSeqLeOrderBridge.le_trans hmin hshift
  self_le_base_plus_abs_tail := laws.self_le_base_plus_abs_tail
  base_le_abs_base := laws.base_le_abs_base
  addSeq_monotone_left := laws.addSeq_monotone_left
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  absSeq_nonnegative := laws.absSeq_nonnegative
  minSeqWith_add_nonnegative_right_bound :=
    laws.minSeqWith_add_nonnegative_right_bound
  source_line735_add_bound_upper :=
    laws.source_line735_self_shift_upper
      /\ laws.source_line735_min_monotonicity_and_shift
  source_line735_add_bound_lower :=
    laws.source_line735_base_shift_lower
      /\ laws.source_line735_min_monotonicity_and_shift
  source_line735_add_bound_to_subSeq_order :=
    laws.source_line735_add_bound_to_subSeq_order
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

/-- G88 unified bridge: the G87 bridge obtained from primitive large
add-bound ingredients. -/
structure Property4DisplayedScalarLargeAddBoundGeneratedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  large_add_bound_generated_core_laws :
    Property4DisplayedScalarLargeAddBoundGeneratedCoreLaws Arch
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
  source_line735_reduced_to_generated_add_bound_min_order : Prop
  source_line743_reduced_to_abs_upper_split_and_shift : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G88 bridge to the G87 bridge. -/
def displayedScalarLargeAddBoundCoreUnifiedBridge_from_generated
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarLargeAddBoundGeneratedCoreUnifiedBridge
      S) :
    Property4DisplayedScalarLargeAddBoundCoreUnifiedBridge S where
  large_add_bound_core_laws :=
    displayedScalarLargeAddBoundCoreLaws_from_generated
      Arch bridge.large_add_bound_generated_core_laws
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
  source_line735_reduced_to_add_bound_min_order :=
    bridge.source_line735_reduced_to_generated_add_bound_min_order
  source_line743_reduced_to_abs_upper_split_and_shift :=
    bridge.source_line743_reduced_to_abs_upper_split_and_shift
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after generating the large add-bound min laws
from primitive order ingredients. -/
structure Property4ReductionDataFromDisplayedScalarLargeAddBoundGeneratedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_large_add_bound_generated_bridge :
    Property4DisplayedScalarLargeAddBoundGeneratedCoreUnifiedBridge S
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
  source_property4_frontier_is_generated_large_add_bound : Prop

/-- Convert G88 reduction data to the G87 layer. -/
def property4DisplayedScalarLargeAddBoundCoreData_from_generated
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarLargeAddBoundGeneratedBridge
        S r) :
    Property4ReductionDataFromDisplayedScalarLargeAddBoundCoreBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_large_add_bound_core_bridge :=
    displayedScalarLargeAddBoundCoreUnifiedBridge_from_generated
      S data.displayed_scalar_large_add_bound_generated_bridge
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
  source_property4_frontier_is_large_add_bound_and_small_abs_upper_split :=
    True

/-- Theorem 1.18 property (4), using the G88 generated large add-bound laws. -/
def property4_from_displayed_scalar_large_add_bound_generated
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarLargeAddBoundGeneratedBridge
        S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_large_add_bound_core
    S r
    (property4DisplayedScalarLargeAddBoundCoreData_from_generated S r data)

end BishopRegularSeqTheorem118

/-- G88 package: the large add-bound min laws are obtained from symmetric
shift estimates, `min` monotonicity, and the nonnegative shift law. -/
structure BishopRegularSeqTheorem118G88Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g87 : BishopRegularSeqTheorem118G87Package S
  large_add_bound_generated_core_laws : Type 1
  large_add_bound_generated_core_bridge : Type 4
  property4_large_add_bound_generated_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_large_add_bound_generated :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_large_add_bound_generated_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  large_add_bound_min_order_generated_from_shift_and_min_monotone : Prop
  remaining_frontier_is_primitive_order_laws_for_large_and_small : Prop

def bishopRegularSeqTheorem118G88Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G88Package S where
  g87 := bishopRegularSeqTheorem118G87Package S
  large_add_bound_generated_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarLargeAddBoundGeneratedCoreLaws
      Arch
  large_add_bound_generated_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarLargeAddBoundGeneratedCoreUnifiedBridge
      S
  property4_large_add_bound_generated_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarLargeAddBoundGeneratedBridge
      S
  property4_from_large_add_bound_generated := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_large_add_bound_generated
      S r data
  large_add_bound_min_order_generated_from_shift_and_min_monotone := True
  remaining_frontier_is_primitive_order_laws_for_large_and_small := True

/-- Progress after G88: the large add-bound min laws have been reduced to
symmetric shift estimates, `min` monotonicity, and the nonnegative shift law. -/
def bishopRegularSeqCh1To4ProgressAfterG88 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 89
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 88
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G88: generated Theorem 1.18 property (4)'s large add-bound min laws \
    from symmetric shift, min monotonicity, and nonnegative shift inputs."


end BishopCReal
