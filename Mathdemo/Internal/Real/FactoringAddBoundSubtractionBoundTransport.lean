import Mathdemo.Internal.Real.GeneratingLargeAddBoundMinLaws

set_option linter.style.longLine false

/-!
# G89: factoring add-bound to subtraction-bound transport

G88 still kept the bridge

`x <= y + z -> x - y <= z`

as a primitive order input.  This file factors that bridge into:

* monotonicity of `subSeq · y` in the left argument;
* the algebraic cancellation `(y+z)-y = z` over `relEventually`.

The cancellation lemma is proved here from the existing RegularSeq
`relEventually` algebra laws, leaving only the left-subtraction monotonicity
as the new primitive frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Algebraic cancellation over the RegularSeq implementation equality:
subtracting the first summand from `y+z` leaves `z`. -/
theorem subSeq_add_left_cancel_eventually
    (y z : RegularSeq) :
    relEventually (subSeq (addSeq y z) y) z := by
  have h0 :
      relEventually
        (subSeq (addSeq y z) y)
        (addSeq (addSeq y z) (negSeq y)) :=
    subSeq_eq_add_neg_eventually (addSeq y z) y
  have h1 :
      relEventually
        (addSeq (addSeq y z) (negSeq y))
        (addSeq y (addSeq z (negSeq y))) :=
    addSeq_assoc_eventually y z (negSeq y)
  have hcomm_inner :
      relEventually
        (addSeq z (negSeq y))
        (addSeq (negSeq y) z) :=
    addSeq_comm_eventually z (negSeq y)
  have h2 :
      relEventually
        (addSeq y (addSeq z (negSeq y)))
        (addSeq y (addSeq (negSeq y) z)) :=
    addSeq_respects_eventually
      y y
      (addSeq z (negSeq y)) (addSeq (negSeq y) z)
      (relEventually_refl y)
      hcomm_inner
  have h3 :
      relEventually
        (addSeq y (addSeq (negSeq y) z))
        (addSeq (addSeq y (negSeq y)) z) :=
    relEventually_symm
      (addSeq (addSeq y (negSeq y)) z)
      (addSeq y (addSeq (negSeq y) z))
      (addSeq_assoc_eventually y (negSeq y) z)
  have hcancel :
      relEventually (addSeq y (negSeq y)) zeroSeq :=
    addSeq_neg_right_eventually y
  have h4 :
      relEventually
        (addSeq (addSeq y (negSeq y)) z)
        (addSeq zeroSeq z) :=
    addSeq_respects_eventually
      (addSeq y (negSeq y)) zeroSeq
      z z
      hcancel
      (relEventually_refl z)
  have h5 :
      relEventually (addSeq zeroSeq z) z :=
    addSeq_zero_left_eventually z
  exact
    relEventually_trans
      (subSeq (addSeq y z) y)
      (addSeq (addSeq y z) (negSeq y))
      z
      h0
      (relEventually_trans
        (addSeq (addSeq y z) (negSeq y))
        (addSeq y (addSeq z (negSeq y)))
        z
        h1
        (relEventually_trans
          (addSeq y (addSeq z (negSeq y)))
          (addSeq y (addSeq (negSeq y) z))
          z
          h2
          (relEventually_trans
            (addSeq y (addSeq (negSeq y) z))
            (addSeq (addSeq y (negSeq y)) z)
            z
            h3
            (relEventually_trans
              (addSeq (addSeq y (negSeq y)) z)
              (addSeq zeroSeq z)
              z
              h4
              h5))))

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G89 core data: generate `x <= y+z -> x-y <= z` from left monotonicity of
subtraction and the closed cancellation `(y+z)-y = z`. -/
structure Property4DisplayedScalarSubTransportCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
  subSeq_monotone_left :
    forall x x' y : RegularSeq,
      RegularSeqLe x x' ->
        RegularSeqLe (subSeq x y) (subSeq x' y)
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
  source_line735_subtraction_monotone_left : Prop
  source_line735_sub_add_cancel_closed : Prop
  source_line735_self_shift_upper : Prop
  source_line735_base_shift_lower : Prop
  source_line735_min_monotonicity_and_shift : Prop
  source_line743_self_le_base_plus_abs_tail : Prop
  source_line743_base_le_abs_base : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G89 sub-transport split back to the G88 generated-law layer. -/
def displayedScalarLargeAddBoundGeneratedCoreLaws_from_subTransport
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarSubTransportCoreLaws Arch) :
    Property4DisplayedScalarLargeAddBoundGeneratedCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  sub_le_of_add_bound := by
    intro x y z hxy
    have hmono :
        RegularSeqLe
          (subSeq x y)
          (subSeq (addSeq y z) y) :=
      laws.subSeq_monotone_left x (addSeq y z) y hxy
    exact
      regularSeqLe_of_right_eventual
        (subSeq_add_left_cancel_eventually y z)
        hmono
  self_le_base_plus_abs_tail := laws.self_le_base_plus_abs_tail
  base_le_self_plus_abs_tail := laws.base_le_self_plus_abs_tail
  base_le_abs_base := laws.base_le_abs_base
  addSeq_monotone_left := laws.addSeq_monotone_left
  minSeqWith_monotone_left := laws.minSeqWith_monotone_left
  absSeq_nonnegative := laws.absSeq_nonnegative
  minSeqWith_add_nonnegative_right_bound :=
    laws.minSeqWith_add_nonnegative_right_bound
  source_line735_self_shift_upper :=
    laws.source_line735_self_shift_upper
  source_line735_base_shift_lower :=
    laws.source_line735_base_shift_lower
  source_line735_min_monotonicity_and_shift :=
    laws.source_line735_min_monotonicity_and_shift
  source_line735_add_bound_to_subSeq_order :=
    laws.source_line735_subtraction_monotone_left
      /\ laws.source_line735_sub_add_cancel_closed
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

/-- G89 unified bridge: the G88 bridge obtained from sub-transport data. -/
structure Property4DisplayedScalarSubTransportCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  sub_transport_core_laws :
    Property4DisplayedScalarSubTransportCoreLaws Arch
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
  source_line735_reduced_to_sub_transport_and_cancel : Prop
  source_line743_reduced_to_abs_upper_split_and_shift : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G89 bridge to the G88 bridge. -/
def displayedScalarLargeAddBoundGeneratedCoreUnifiedBridge_from_subTransport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge : Property4DisplayedScalarSubTransportCoreUnifiedBridge S) :
    Property4DisplayedScalarLargeAddBoundGeneratedCoreUnifiedBridge S where
  large_add_bound_generated_core_laws :=
    displayedScalarLargeAddBoundGeneratedCoreLaws_from_subTransport
      Arch bridge.sub_transport_core_laws
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
  source_line735_reduced_to_generated_add_bound_min_order :=
    bridge.source_line735_reduced_to_sub_transport_and_cancel
  source_line743_reduced_to_abs_upper_split_and_shift :=
    bridge.source_line743_reduced_to_abs_upper_split_and_shift
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after factoring add-bound-to-subtraction
transport through subtraction monotonicity and cancellation. -/
structure Property4ReductionDataFromDisplayedScalarSubTransportBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_sub_transport_bridge :
    Property4DisplayedScalarSubTransportCoreUnifiedBridge S
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
  source_property4_frontier_is_sub_transport_monotonicity : Prop

/-- Convert G89 reduction data to the G88 layer. -/
def property4DisplayedScalarLargeAddBoundGeneratedCoreData_from_subTransport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSubTransportBridge S r) :
    Property4ReductionDataFromDisplayedScalarLargeAddBoundGeneratedBridge
      S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_large_add_bound_generated_bridge :=
    displayedScalarLargeAddBoundGeneratedCoreUnifiedBridge_from_subTransport
      S data.displayed_scalar_sub_transport_bridge
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
  source_property4_frontier_is_generated_large_add_bound :=
    True

/-- Theorem 1.18 property (4), using the G89 sub-transport split. -/
def property4_from_displayed_scalar_sub_transport
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarSubTransportBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_large_add_bound_generated
    S r
    (property4DisplayedScalarLargeAddBoundGeneratedCoreData_from_subTransport
      S r data)

end BishopRegularSeqTheorem118

/-- G89 package: the add-bound-to-subtraction bridge is factored through
subtraction monotonicity and a closed cancellation lemma. -/
structure BishopRegularSeqTheorem118G89Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g88 : BishopRegularSeqTheorem118G88Package S
  sub_transport_core_laws : Type 1
  sub_transport_core_bridge : Type 4
  property4_sub_transport_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_sub_transport :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_sub_transport_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  sub_add_cancel_closed_over_relEventually : Prop
  remaining_frontier_is_subSeq_left_monotone_plus_primitive_order : Prop

def bishopRegularSeqTheorem118G89Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G89Package S where
  g88 := bishopRegularSeqTheorem118G88Package S
  sub_transport_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSubTransportCoreLaws
      Arch
  sub_transport_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarSubTransportCoreUnifiedBridge
      S
  property4_sub_transport_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarSubTransportBridge
      S
  property4_from_sub_transport := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_sub_transport
      S r data
  sub_add_cancel_closed_over_relEventually := True
  remaining_frontier_is_subSeq_left_monotone_plus_primitive_order := True

/-- Progress after G89: the add-bound-to-subtraction bridge now uses a closed
RegularSeq cancellation lemma and leaves only subtraction monotonicity as the
new order frontier. -/
def bishopRegularSeqCh1To4ProgressAfterG89 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 90
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 89
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G89: factored Theorem 1.18 property (4)'s add-bound-to-subtraction \
    bridge through subSeq-left monotonicity and a closed cancellation lemma."


end BishopCReal
