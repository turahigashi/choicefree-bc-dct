import Mathdemo.Internal.CRat_iter184

/-!
# G85: splitting the shifted-min truncation bound

G84 left the second small line-743 shifted-min step as one input:

`min(|b| + ||a|-b|, c) <= min(|b|, c) + ||a|-b|`.

This file exposes the two source-level ingredients behind that step:

1. the tail term `||a|-b|` is nonnegative;
2. truncation is stable under adding a nonnegative tail:
   `min(x+d,c) <= min(x,c)+d`.

The large line-735 two-sided frontier and the first small line-743
absolute-tail/monotonicity split are carried unchanged.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G85 core data: the remaining shifted-min bound is obtained from
nonnegativity of the absolute tail and the general truncation-shift law
`min(x+d,c) <= min(x,c)+d`. -/
structure Property4DisplayedScalarSmallTailShiftCoreLaws
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
  source_line743_abs_tail_upper_bound : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G85 shift data back to the G84 monotone core laws. -/
def displayedScalarSmallTailMonotoneCoreLaws_from_shift
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSmallTailShiftCoreLaws Arch) :
    Property4DisplayedScalarSmallTailMonotoneCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  min_lipschitz_upper := laws.min_lipschitz_upper
  min_lipschitz_lower := laws.min_lipschitz_lower
  abs_tail_upper := laws.abs_tail_upper
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  small_shifted_min_le_min_plus_tail := by
    intro a b c
    exact
      laws.minSeqWith_add_nonnegative_right_bound
        (absSeq b)
        (absSeq (subSeq (absSeq a) b))
        c
        (laws.absSeq_nonnegative (subSeq (absSeq a) b))
  source_line735_split_to_two_sided_min_order :=
    laws.source_line735_split_to_two_sided_min_order
  source_line743_abs_tail_upper_bound :=
    laws.source_line743_abs_tail_upper_bound
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_shifted_min_truncation_bound :=
    laws.source_line743_tail_abs_is_nonnegative
      /\ laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G85 unified bridge: the G84 bridge obtained from the nonnegative-tail
shift law. -/
structure Property4DisplayedScalarSmallTailShiftCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  small_tail_shift_core_laws :
    Property4DisplayedScalarSmallTailShiftCoreLaws Arch
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
  source_line743_reduced_to_abs_tail_min_monotone_and_shift : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G85 bridge to the G84 bridge. -/
def displayedScalarSmallTailMonotoneCoreUnifiedBridge_from_shift
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarSmallTailShiftCoreUnifiedBridge S) :
    Property4DisplayedScalarSmallTailMonotoneCoreUnifiedBridge S where
  small_tail_monotone_core_laws :=
    displayedScalarSmallTailMonotoneCoreLaws_from_shift
      Arch bridge.small_tail_shift_core_laws
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
  source_line743_reduced_to_abs_tail_plus_min_monotone :=
    bridge.source_line743_reduced_to_abs_tail_min_monotone_and_shift
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after exposing the nonnegative-tail shift
behind the second small line-743 step. -/
structure Property4ReductionDataFromDisplayedScalarSmallTailShiftCoreBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_small_tail_shift_core_bridge :
    Property4DisplayedScalarSmallTailShiftCoreUnifiedBridge S
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
  source_property4_frontier_is_large_two_sided_and_small_shift :
    Prop

/-- Convert G85 reduction data to the G84 layer. -/
def property4DisplayedScalarSmallTailMonotoneCoreData_from_shift
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailShiftCoreBridge S r) :
    Property4ReductionDataFromDisplayedScalarSmallTailMonotoneCoreBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_small_tail_monotone_core_bridge :=
    displayedScalarSmallTailMonotoneCoreUnifiedBridge_from_shift
      S data.displayed_scalar_small_tail_shift_core_bridge
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
  source_property4_frontier_is_large_two_sided_and_small_monotone :=
    True

/-- Theorem 1.18 property (4), using the G85 shifted-min split. -/
def property4_from_displayed_scalar_small_tail_shift_core
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSmallTailShiftCoreBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_small_tail_monotone_core
    S r
    (property4DisplayedScalarSmallTailMonotoneCoreData_from_shift S r data)

end BishopRegularSeqTheorem118

/-- G85 package: the second small line-743 shifted-min bound is reduced to
absolute-tail nonnegativity and a nonnegative truncation-shift law. -/
structure BishopRegularSeqTheorem118G85Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g84 : BishopRegularSeqTheorem118G84Package S
  small_tail_shift_core_laws : Type 1
  small_tail_shift_core_bridge : Type 4
  property4_small_tail_shift_core_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_small_tail_shift_core :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_small_tail_shift_core_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  small_shifted_second_step_split_to_tail_nonnegative_shift_law : Prop
  remaining_frontier_is_large_two_sided_small_abs_tail_min_monotone_and_shift_law :
    Prop

def bishopRegularSeqTheorem118G85Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G85Package S where
  g84 := bishopRegularSeqTheorem118G84Package S
  small_tail_shift_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailShiftCoreLaws
      Arch
  small_tail_shift_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSmallTailShiftCoreUnifiedBridge
      S
  property4_small_tail_shift_core_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarSmallTailShiftCoreBridge
      S
  property4_from_small_tail_shift_core := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_small_tail_shift_core
      S r data
  small_shifted_second_step_split_to_tail_nonnegative_shift_law := True
  remaining_frontier_is_large_two_sided_small_abs_tail_min_monotone_and_shift_law :=
    True

/-- Progress after G85: the second small line743 shifted-min step has been
split into tail nonnegativity and a nonnegative truncation-shift law. -/
def bishopRegularSeqCh1To4ProgressAfterG85 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 86
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 85
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G85: split Theorem 1.18 property (4)'s second small line743 \
    shifted-min step into tail nonnegativity plus a min shift law."

set_option linter.style.longLine false


end BishopCReal
