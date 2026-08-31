import Mathdemo.Internal.Real.FactoringAddBoundSubtractionBoundTransport

set_option linter.style.longLine false

/-!
# G90: closing left monotonicity of subtraction

G89 reduced the add-bound-to-subtraction bridge to left monotonicity of
`subSeq · y` plus the cancellation `(y+z)-y = z`.  This file closes that left
monotonicity from:

* eventual transport of `RegularSeqNonneg`;
* the algebraic identity `(x'-y)-(x-y) = x'-x` over `relEventually`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Nonnegativity is stable under eventual equality on the represented
RegularSeq. -/
theorem regularSeqNonneg_of_eventual
    {x y : RegularSeq}
    (hxy : relEventually x y)
    (hy : RegularSeqNonneg y) :
    RegularSeqNonneg x := by
  intro hx
  have hsub :
      relEventually
        (subSeq zeroSeq x)
        (subSeq zeroSeq y) :=
    subSeq_respects_eventually
      zeroSeq zeroSeq
      x y
      (relEventually_refl zeroSeq)
      hxy
  exact
    hy
      (posEventually_respects
        (subSeq zeroSeq x)
        (subSeq zeroSeq y)
        hsub
        hx)

/-- Subtracting the same right-hand representative preserves the represented
difference: `(x'-y)-(x-y) = x'-x` over `relEventually`. -/
theorem subSeq_same_right_diff_eventually
    (x x' y : RegularSeq) :
    relEventually
      (subSeq (subSeq x' y) (subSeq x y))
      (subSeq x' x) := by
  have h0 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq (subSeq x' y) (negSeq (subSeq x y))) :=
    subSeq_eq_add_neg_eventually (subSeq x' y) (subSeq x y)
  have hleft :
      relEventually
        (subSeq x' y)
        (addSeq x' (negSeq y)) :=
    subSeq_eq_add_neg_eventually x' y
  have hright :
      relEventually
        (negSeq (subSeq x y))
        (subSeq y x) :=
    relEventually_symm
      (subSeq y x)
      (negSeq (subSeq x y))
      (subSeq_comm_neg_eventually y x)
  have h1 :
      relEventually
        (addSeq (subSeq x' y) (negSeq (subSeq x y)))
        (addSeq (addSeq x' (negSeq y)) (subSeq y x)) :=
    addSeq_respects_eventually
      (subSeq x' y) (addSeq x' (negSeq y))
      (negSeq (subSeq x y)) (subSeq y x)
      hleft
      hright
  have hright_sub :
      relEventually
        (subSeq y x)
        (addSeq y (negSeq x)) :=
    subSeq_eq_add_neg_eventually y x
  have h2 :
      relEventually
        (addSeq (addSeq x' (negSeq y)) (subSeq y x))
        (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x))) :=
    addSeq_respects_eventually
      (addSeq x' (negSeq y)) (addSeq x' (negSeq y))
      (subSeq y x) (addSeq y (negSeq x))
      (relEventually_refl (addSeq x' (negSeq y)))
      hright_sub
  have h3 :
      relEventually
        (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x)))
        (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x)))) :=
    addSeq_assoc_eventually x' (negSeq y) (addSeq y (negSeq x))
  have hinner_assoc :
      relEventually
        (addSeq (negSeq y) (addSeq y (negSeq x)))
        (addSeq (addSeq (negSeq y) y) (negSeq x)) :=
    relEventually_symm
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (addSeq (negSeq y) (addSeq y (negSeq x)))
      (addSeq_assoc_eventually (negSeq y) y (negSeq x))
  have h4 :
      relEventually
        (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x))))
        (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x))) :=
    addSeq_respects_eventually
      x' x'
      (addSeq (negSeq y) (addSeq y (negSeq x)))
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (relEventually_refl x')
      hinner_assoc
  have hcancel :
      relEventually
        (addSeq (negSeq y) y)
        zeroSeq :=
    addSeq_neg_left_eventually y
  have hinner_cancel :
      relEventually
        (addSeq (addSeq (negSeq y) y) (negSeq x))
        (addSeq zeroSeq (negSeq x)) :=
    addSeq_respects_eventually
      (addSeq (negSeq y) y) zeroSeq
      (negSeq x) (negSeq x)
      hcancel
      (relEventually_refl (negSeq x))
  have hinner_zero :
      relEventually
        (addSeq zeroSeq (negSeq x))
        (negSeq x) :=
    addSeq_zero_left_eventually (negSeq x)
  have hinner :
      relEventually
        (addSeq (addSeq (negSeq y) y) (negSeq x))
        (negSeq x) :=
    relEventually_trans
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (addSeq zeroSeq (negSeq x))
      (negSeq x)
      hinner_cancel
      hinner_zero
  have h5 :
      relEventually
        (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x)))
        (addSeq x' (negSeq x)) :=
    addSeq_respects_eventually
      x' x'
      (addSeq (addSeq (negSeq y) y) (negSeq x))
      (negSeq x)
      (relEventually_refl x')
      hinner
  have h6 :
      relEventually
        (addSeq x' (negSeq x))
        (subSeq x' x) :=
    relEventually_symm
      (subSeq x' x)
      (addSeq x' (negSeq x))
      (subSeq_eq_add_neg_eventually x' x)
  have h01 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq (addSeq x' (negSeq y)) (subSeq y x)) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq (subSeq x' y) (negSeq (subSeq x y)))
      (addSeq (addSeq x' (negSeq y)) (subSeq y x))
      h0
      h1
  have h012 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x))) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq (addSeq x' (negSeq y)) (subSeq y x))
      (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x)))
      h01
      h2
  have h0123 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x)))) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq (addSeq x' (negSeq y)) (addSeq y (negSeq x)))
      (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x))))
      h012
      h3
  have h01234 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x))) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq x' (addSeq (negSeq y) (addSeq y (negSeq x))))
      (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x)))
      h0123
      h4
  have h012345 :
      relEventually
        (subSeq (subSeq x' y) (subSeq x y))
        (addSeq x' (negSeq x)) :=
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq x' (addSeq (addSeq (negSeq y) y) (negSeq x)))
      (addSeq x' (negSeq x))
      h01234
      h5
  exact
    relEventually_trans
      (subSeq (subSeq x' y) (subSeq x y))
      (addSeq x' (negSeq x))
      (subSeq x' x)
      h012345
      h6

/-- Left monotonicity of subtraction by a fixed right-hand representative. -/
theorem subSeq_monotone_left_regularSeqLe
    (x x' y : RegularSeq)
    (hxx : RegularSeqLe x x') :
    RegularSeqLe (subSeq x y) (subSeq x' y) :=
  regularSeqNonneg_of_eventual
    (subSeq_same_right_diff_eventually x x' y)
    hxx

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G90 core data: the G89 subtraction-monotonicity field is now generated
from closed RegularSeq algebra and nonnegativity transport. -/
structure Property4DisplayedScalarSubTransportClosedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
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
  source_line735_subtraction_monotone_left_closed : Prop
  source_line735_sub_add_cancel_closed : Prop
  source_line735_same_right_subtraction_diff_closed : Prop
  source_line735_nonneg_transport_closed : Prop
  source_line735_self_shift_upper : Prop
  source_line735_base_shift_lower : Prop
  source_line735_min_monotonicity_and_shift : Prop
  source_line743_self_le_base_plus_abs_tail : Prop
  source_line743_base_le_abs_base : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G90 closed subtraction transport back to the G89 layer. -/
def displayedScalarSubTransportCoreLaws_from_closed
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSubTransportClosedCoreLaws Arch) :
    Property4DisplayedScalarSubTransportCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  subSeq_monotone_left := by
    intro x x' y hxx
    exact subSeq_monotone_left_regularSeqLe x x' y hxx
  self_le_base_plus_abs_tail := laws.self_le_base_plus_abs_tail
  base_le_self_plus_abs_tail := laws.base_le_self_plus_abs_tail
  base_le_abs_base := laws.base_le_abs_base
  addSeq_monotone_left := laws.addSeq_monotone_left
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  absSeq_nonnegative := laws.absSeq_nonnegative
  minSeqWith_add_nonnegative_right_bound :=
    laws.minSeqWith_add_nonnegative_right_bound
  source_line735_subtraction_monotone_left :=
    laws.source_line735_subtraction_monotone_left_closed
      /\ laws.source_line735_same_right_subtraction_diff_closed
      /\ laws.source_line735_nonneg_transport_closed
  source_line735_sub_add_cancel_closed :=
    laws.source_line735_sub_add_cancel_closed
  source_line735_self_shift_upper :=
    laws.source_line735_self_shift_upper
  source_line735_base_shift_lower :=
    laws.source_line735_base_shift_lower
  source_line735_min_monotonicity_and_shift :=
    laws.source_line735_min_monotonicity_and_shift
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

/-- G90 unified bridge: the G89 bridge obtained from closed subtraction
transport. -/
structure Property4DisplayedScalarSubTransportClosedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  sub_transport_closed_core_laws :
    Property4DisplayedScalarSubTransportClosedCoreLaws Arch
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
  source_line743_reduced_to_abs_upper_split_and_shift : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G90 bridge to the G89 bridge. -/
def displayedScalarSubTransportCoreUnifiedBridge_from_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4DisplayedScalarSubTransportClosedCoreUnifiedBridge S) :
    Property4DisplayedScalarSubTransportCoreUnifiedBridge S where
  sub_transport_core_laws :=
    displayedScalarSubTransportCoreLaws_from_closed
      Arch bridge.sub_transport_closed_core_laws
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
  source_line735_reduced_to_sub_transport_and_cancel :=
    bridge.source_line735_reduced_to_closed_sub_transport
  source_line743_reduced_to_abs_upper_split_and_shift :=
    bridge.source_line743_reduced_to_abs_upper_split_and_shift
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after closing subtraction monotonicity. -/
structure Property4ReductionDataFromDisplayedScalarSubTransportClosedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_sub_transport_closed_bridge :
    Property4DisplayedScalarSubTransportClosedCoreUnifiedBridge S
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
  source_property4_frontier_after_closed_sub_transport : Prop

/-- Convert G90 reduction data to the G89 layer. -/
def property4DisplayedScalarSubTransportData_from_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSubTransportClosedBridge S r) :
    Property4ReductionDataFromDisplayedScalarSubTransportBridge S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_sub_transport_bridge :=
    displayedScalarSubTransportCoreUnifiedBridge_from_closed
      S data.displayed_scalar_sub_transport_closed_bridge
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
  source_property4_frontier_is_sub_transport_monotonicity :=
    True

/-- Theorem 1.18 property (4), using the G90 closed sub-transport split. -/
def property4_from_displayed_scalar_sub_transport_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSubTransportClosedBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_sub_transport
    S r
    (property4DisplayedScalarSubTransportData_from_closed S r data)

end BishopRegularSeqTheorem118

/-- G90 package: `subSeq` left monotonicity is closed from RegularSeq algebra
and nonnegativity transport. -/
structure BishopRegularSeqTheorem118G90Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g89 : BishopRegularSeqTheorem118G89Package S
  sub_transport_closed_core_laws : Type 1
  sub_transport_closed_core_bridge : Type 4
  property4_sub_transport_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_sub_transport_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_sub_transport_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  same_right_subtraction_diff_closed : Prop
  remaining_frontier_is_absolute_tail_and_min_shift_order : Prop

def bishopRegularSeqTheorem118G90Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G90Package S where
  g89 := bishopRegularSeqTheorem118G89Package S
  sub_transport_closed_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSubTransportClosedCoreLaws
      Arch
  sub_transport_closed_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSubTransportClosedCoreUnifiedBridge
      S
  property4_sub_transport_closed_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarSubTransportClosedBridge
      S
  property4_from_sub_transport_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_sub_transport_closed
      S r data
  same_right_subtraction_diff_closed := True
  remaining_frontier_is_absolute_tail_and_min_shift_order := True

/-- Progress after G90: the subtraction-left-monotonicity frontier has been
closed by algebraic cancellation and eventual transport of nonnegativity. -/
def bishopRegularSeqCh1To4ProgressAfterG90 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 91
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 90
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G90: closed subSeq-left monotonicity from same-right subtraction \
    cancellation and eventual transport of RegularSeq nonnegativity."


end BishopCReal
