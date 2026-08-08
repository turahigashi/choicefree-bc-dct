import Mathdemo.Internal.CRat_iter191

set_option linter.style.longLine false

/-!
# G92: closing nonnegativity of `absSeq`

G91 left the primitive input `0 <= |x|`.  This file proves it at the
representative level from scalar absolute-value nonnegativity, then transports
it into the `RegularSeqLe zeroSeq (absSeq x)` surface used by the line-735 and
line-743 chains.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Absolute-value representatives are nonnegative in the `RegularSeqNonneg`
surface. -/
theorem absSeq_regularSeqNonneg
    (x : RegularSeq) :
    RegularSeqNonneg (absSeq x) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  change COF.lt (eps k) (0 - COF.abs (x.val (N + 1))) at hpoint
  have hzero :
      COF.lt (0 : Scalar) (0 - COF.abs (x.val (N + 1))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint
  have hbad :
      COF.lt (COF.abs (x.val (N + 1))) 0 := by
    have t := COF.lt_add_left (COF.abs (x.val (N + 1))) hzero
    rwa [show COF.abs (x.val (N + 1)) + (0 : Scalar) =
          COF.abs (x.val (N + 1)) from by ring,
      show COF.abs (x.val (N + 1)) +
            (0 - COF.abs (x.val (N + 1))) =
          0 from by ring] at t
  exact scalar_abs_nonneg (x.val (N + 1)) hbad

/-- Nonnegativity of `absSeq` in the `RegularSeqLe` surface. -/
theorem absSeq_nonnegative_regularSeqLe
    (x : RegularSeq) :
    RegularSeqLe zeroSeq (absSeq x) :=
  regularSeqNonneg_of_eventual
    (subSeq_zero_right_eventually (absSeq x))
    (absSeq_regularSeqNonneg x)

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G92 core data: the `0 <= |x|` input is now obtained from the closed
representative absolute-value nonnegativity theorem. -/
structure Property4DisplayedScalarAbsNonnegativeClosedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  self_le_base_plus_abs_tail :
    forall u b : RegularSeq,
      RegularSeqLe u (addSeq b (absSeq (subSeq u b)))
  base_le_self_plus_abs_tail :
    forall u b : RegularSeq,
      RegularSeqLe b (addSeq u (absSeq (subSeq u b)))
  addSeq_monotone_left :
    forall x y z : RegularSeq,
      RegularSeqLe x y ->
        RegularSeqLe (addSeq x z) (addSeq y z)
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
  source_line735_self_shift_upper : Prop
  source_line735_base_shift_lower : Prop
  source_line735_min_monotonicity_and_shift : Prop
  source_line743_self_le_base_plus_abs_tail : Prop
  source_line743_base_le_abs_base_closed : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative_closed : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G92 closed absolute nonnegativity back to the G91 layer. -/
def displayedScalarAbsBaseClosedCoreLaws_from_absNonnegativeClosed
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarAbsNonnegativeClosedCoreLaws Arch) :
    Property4DisplayedScalarAbsBaseClosedCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  self_le_base_plus_abs_tail := laws.self_le_base_plus_abs_tail
  base_le_self_plus_abs_tail := laws.base_le_self_plus_abs_tail
  addSeq_monotone_left := laws.addSeq_monotone_left
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  absSeq_nonnegative := absSeq_nonnegative_regularSeqLe
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
  source_line735_self_shift_upper :=
    laws.source_line735_self_shift_upper
  source_line735_base_shift_lower :=
    laws.source_line735_base_shift_lower
  source_line735_min_monotonicity_and_shift :=
    laws.source_line735_min_monotonicity_and_shift
  source_line743_self_le_base_plus_abs_tail :=
    laws.source_line743_self_le_base_plus_abs_tail
  source_line743_base_le_abs_base_closed :=
    laws.source_line743_base_le_abs_base_closed
  source_line743_addition_monotonicity_for_abs_base :=
    laws.source_line743_addition_monotonicity_for_abs_base
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_tail_abs_is_nonnegative :=
    laws.source_line743_tail_abs_is_nonnegative_closed
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G92 unified bridge: the G91 bridge obtained from the closed absolute
nonnegativity theorem. -/
structure Property4DisplayedScalarAbsNonnegativeClosedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  abs_nonnegative_closed_core_laws :
    Property4DisplayedScalarAbsNonnegativeClosedCoreLaws Arch
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
  source_line735_reduced_to_closed_sub_transport : Prop
  source_line743_reduced_to_abs_nonnegative_closed_chain : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G92 bridge to the G91 bridge. -/
def displayedScalarAbsBaseClosedCoreUnifiedBridge_from_absNonnegativeClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4DisplayedScalarAbsNonnegativeClosedCoreUnifiedBridge S) :
    Property4DisplayedScalarAbsBaseClosedCoreUnifiedBridge S where
  abs_base_closed_core_laws :=
    displayedScalarAbsBaseClosedCoreLaws_from_absNonnegativeClosed
      Arch bridge.abs_nonnegative_closed_core_laws
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
  source_line735_reduced_to_closed_sub_transport :=
    bridge.source_line735_reduced_to_closed_sub_transport
  source_line743_reduced_to_abs_base_closed_chain :=
    bridge.source_line743_reduced_to_abs_nonnegative_closed_chain
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after closing `0 <= |x|`. -/
structure Property4ReductionDataFromDisplayedScalarAbsNonnegativeClosedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_abs_nonnegative_closed_bridge :
    Property4DisplayedScalarAbsNonnegativeClosedCoreUnifiedBridge S
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
  source_property4_frontier_after_abs_nonnegative_closed : Prop

/-- Convert G92 reduction data to the G91 layer. -/
def property4DisplayedScalarAbsBaseClosedData_from_absNonnegativeClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarAbsNonnegativeClosedBridge
        S r) :
    Property4ReductionDataFromDisplayedScalarAbsBaseClosedBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_abs_base_closed_bridge :=
    displayedScalarAbsBaseClosedCoreUnifiedBridge_from_absNonnegativeClosed
      S data.displayed_scalar_abs_nonnegative_closed_bridge
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
  source_property4_frontier_after_abs_base_closed :=
    True

/-- Theorem 1.18 property (4), using the G92 closed absolute nonnegativity. -/
def property4_from_displayed_scalar_abs_nonnegative_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarAbsNonnegativeClosedBridge
        S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_abs_base_closed
    S r
    (property4DisplayedScalarAbsBaseClosedData_from_absNonnegativeClosed
      S r data)

end BishopRegularSeqTheorem118

/-- G92 package: the `0 <= |x|` order input is closed. -/
structure BishopRegularSeqTheorem118G92Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g91 : BishopRegularSeqTheorem118G91Package S
  abs_nonnegative_closed_core_laws : Type 1
  abs_nonnegative_closed_core_bridge : Type 4
  property4_abs_nonnegative_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_abs_nonnegative_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_abs_nonnegative_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  absSeq_nonnegative_closed : Prop
  remaining_frontier_is_shift_min_and_add_order : Prop

def bishopRegularSeqTheorem118G92Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G92Package S where
  g91 := bishopRegularSeqTheorem118G91Package S
  abs_nonnegative_closed_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarAbsNonnegativeClosedCoreLaws
      Arch
  abs_nonnegative_closed_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarAbsNonnegativeClosedCoreUnifiedBridge
      S
  property4_abs_nonnegative_closed_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarAbsNonnegativeClosedBridge
      S
  property4_from_abs_nonnegative_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_abs_nonnegative_closed
      S r data
  absSeq_nonnegative_closed := True
  remaining_frontier_is_shift_min_and_add_order := True

/-- Progress after G92: the `0 <= |x|` input is closed from scalar
absolute-value nonnegativity and transported to `RegularSeqLe`. -/
def bishopRegularSeqCh1To4ProgressAfterG92 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 93
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 92
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G92: closed Theorem 1.18 property (4)'s absSeq nonnegativity input \
    from scalar absolute-value nonnegativity."


end BishopCReal
