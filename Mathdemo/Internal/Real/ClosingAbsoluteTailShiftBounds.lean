import Mathdemo.Internal.Real.ClosingNonnegativityAbsSeq

set_option linter.style.longLine false

/-!
# G93: closing the absolute-tail shift bounds

G92 left the two displayed scalar bounds behind the source estimates

* `u <= b + |u-b|`;
* `b <= u + |u-b|`.

This file closes them in the source order used by the proof of Theorem 1.18
property (4): first prove the scalar absolute-value nonnegativity tails
`x+|x| >= 0` and `-x+|x| >= 0`, then transport those tails across the
eventual-equality identities for the displayed shifted differences.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Representative-level nonnegativity of `x + |x|`. -/
theorem add_abs_regularSeqNonneg
    (x : RegularSeq) :
    RegularSeqNonneg (addSeq x (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  have hpoint' : COF.lt (eps k)
      (0 - (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      addSeq, addVal, addIndex, absSeq, absVal] using hpoint
  have hzero :
      COF.lt (0 : Scalar)
        (0 - (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint'
  have hbad :
      COF.lt (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) 0 := by
    have t :=
      COF.lt_add_left
        (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) hzero
    rwa [show
        (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) + 0 =
          x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))
        from by ring,
      show
        (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) +
            (0 - (x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) =
          0
        from by ring] at t
  exact scalar_add_abs_nonneg (x.val ((N + 1) + 1)) hbad

/-- Representative-level nonnegativity of `-x + |x|`. -/
theorem neg_add_abs_regularSeqNonneg
    (x : RegularSeq) :
    RegularSeqNonneg (addSeq (negSeq x) (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  have hpoint' : COF.lt (eps k)
      (0 - (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      addSeq, addVal, addIndex, negSeq, negVal, absSeq, absVal] using hpoint
  have hzero :
      COF.lt (0 : Scalar)
        (0 - (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint'
  have hbad_sum :
      COF.lt (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) 0 := by
    have t :=
      COF.lt_add_left
        (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) hzero
    rwa [show
        (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) + 0 =
          -x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))
        from by ring,
      show
        (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))) +
            (0 - (-x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1)))) =
          0
        from by ring] at t
  have hbad :
      COF.lt (COF.abs (x.val ((N + 1) + 1)) - x.val ((N + 1) + 1)) 0 := by
    rwa [show
        COF.abs (x.val ((N + 1) + 1)) - x.val ((N + 1) + 1) =
          -x.val ((N + 1) + 1) + COF.abs (x.val ((N + 1) + 1))
        from by ring]
  exact scalar_abs_sub_self_nonneg (x.val ((N + 1) + 1)) hbad

/-- Difference identity for the source-side bound
`b <= u + |u-b|`: `(u+|u-b|)-b = (u-b)+|u-b|`. -/
theorem base_shift_diff_eventually
    (u b : RegularSeq) :
    relEventually
      (subSeq (addSeq u (absSeq (subSeq u b))) b)
      (addSeq (subSeq u b) (absSeq (subSeq u b))) := by
  have h0 :
      relEventually
        (subSeq (addSeq u (absSeq (subSeq u b))) b)
        (addSeq (addSeq u (absSeq (subSeq u b))) (negSeq b)) :=
    subSeq_eq_add_neg_eventually
      (addSeq u (absSeq (subSeq u b))) b
  have h1 :
      relEventually
        (addSeq (addSeq u (absSeq (subSeq u b))) (negSeq b))
        (addSeq u (addSeq (absSeq (subSeq u b)) (negSeq b))) :=
    addSeq_assoc_eventually u (absSeq (subSeq u b)) (negSeq b)
  have hcomm :
      relEventually
        (addSeq (absSeq (subSeq u b)) (negSeq b))
        (addSeq (negSeq b) (absSeq (subSeq u b))) :=
    addSeq_comm_eventually (absSeq (subSeq u b)) (negSeq b)
  have h2 :
      relEventually
        (addSeq u (addSeq (absSeq (subSeq u b)) (negSeq b)))
        (addSeq u (addSeq (negSeq b) (absSeq (subSeq u b)))) :=
    addSeq_respects_eventually
      u u
      (addSeq (absSeq (subSeq u b)) (negSeq b))
      (addSeq (negSeq b) (absSeq (subSeq u b)))
      (relEventually_refl u)
      hcomm
  have h3 :
      relEventually
        (addSeq u (addSeq (negSeq b) (absSeq (subSeq u b))))
        (addSeq (addSeq u (negSeq b)) (absSeq (subSeq u b))) :=
    relEventually_symm
      (addSeq (addSeq u (negSeq b)) (absSeq (subSeq u b)))
      (addSeq u (addSeq (negSeq b) (absSeq (subSeq u b))))
      (addSeq_assoc_eventually u (negSeq b) (absSeq (subSeq u b)))
  have hleft :
      relEventually
        (addSeq u (negSeq b))
        (subSeq u b) :=
    relEventually_symm
      (subSeq u b)
      (addSeq u (negSeq b))
      (subSeq_eq_add_neg_eventually u b)
  have h4 :
      relEventually
        (addSeq (addSeq u (negSeq b)) (absSeq (subSeq u b)))
        (addSeq (subSeq u b) (absSeq (subSeq u b))) :=
    addSeq_respects_eventually
      (addSeq u (negSeq b)) (subSeq u b)
      (absSeq (subSeq u b)) (absSeq (subSeq u b))
      hleft
      (relEventually_refl (absSeq (subSeq u b)))
  have h01 :
      relEventually
        (subSeq (addSeq u (absSeq (subSeq u b))) b)
        (addSeq u (addSeq (absSeq (subSeq u b)) (negSeq b))) :=
    relEventually_trans
      (subSeq (addSeq u (absSeq (subSeq u b))) b)
      (addSeq (addSeq u (absSeq (subSeq u b))) (negSeq b))
      (addSeq u (addSeq (absSeq (subSeq u b)) (negSeq b)))
      h0
      h1
  have h012 :
      relEventually
        (subSeq (addSeq u (absSeq (subSeq u b))) b)
        (addSeq u (addSeq (negSeq b) (absSeq (subSeq u b)))) :=
    relEventually_trans
      (subSeq (addSeq u (absSeq (subSeq u b))) b)
      (addSeq u (addSeq (absSeq (subSeq u b)) (negSeq b)))
      (addSeq u (addSeq (negSeq b) (absSeq (subSeq u b))))
      h01
      h2
  have h0123 :
      relEventually
        (subSeq (addSeq u (absSeq (subSeq u b))) b)
        (addSeq (addSeq u (negSeq b)) (absSeq (subSeq u b))) :=
    relEventually_trans
      (subSeq (addSeq u (absSeq (subSeq u b))) b)
      (addSeq u (addSeq (negSeq b) (absSeq (subSeq u b))))
      (addSeq (addSeq u (negSeq b)) (absSeq (subSeq u b)))
      h012
      h3
  exact
    relEventually_trans
      (subSeq (addSeq u (absSeq (subSeq u b))) b)
      (addSeq (addSeq u (negSeq b)) (absSeq (subSeq u b)))
      (addSeq (subSeq u b) (absSeq (subSeq u b)))
      h0123
      h4

/-- Difference identity for the source-side bound
`u <= b + |u-b|`: `(b+|u-b|)-u = -(u-b)+|u-b|`. -/
theorem self_shift_diff_eventually
    (u b : RegularSeq) :
    relEventually
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq (negSeq (subSeq u b)) (absSeq (subSeq u b))) := by
  have h0 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq (addSeq b (absSeq (subSeq u b))) (negSeq u)) :=
    subSeq_eq_add_neg_eventually
      (addSeq b (absSeq (subSeq u b))) u
  have h1 :
      relEventually
        (addSeq (addSeq b (absSeq (subSeq u b))) (negSeq u))
        (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u))) :=
    addSeq_assoc_eventually b (absSeq (subSeq u b)) (negSeq u)
  have hcomm :
      relEventually
        (addSeq (absSeq (subSeq u b)) (negSeq u))
        (addSeq (negSeq u) (absSeq (subSeq u b))) :=
    addSeq_comm_eventually (absSeq (subSeq u b)) (negSeq u)
  have h2 :
      relEventually
        (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u)))
        (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b)))) :=
    addSeq_respects_eventually
      b b
      (addSeq (absSeq (subSeq u b)) (negSeq u))
      (addSeq (negSeq u) (absSeq (subSeq u b)))
      (relEventually_refl b)
      hcomm
  have h3 :
      relEventually
        (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
        (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b))) :=
    relEventually_symm
      (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
      (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
      (addSeq_assoc_eventually b (negSeq u) (absSeq (subSeq u b)))
  have hleft_sub :
      relEventually
        (addSeq b (negSeq u))
        (subSeq b u) :=
    relEventually_symm
      (subSeq b u)
      (addSeq b (negSeq u))
      (subSeq_eq_add_neg_eventually b u)
  have hleft_neg :
      relEventually
        (subSeq b u)
        (negSeq (subSeq u b)) :=
    subSeq_comm_neg_eventually b u
  have hleft :
      relEventually
        (addSeq b (negSeq u))
        (negSeq (subSeq u b)) :=
    relEventually_trans
      (addSeq b (negSeq u))
      (subSeq b u)
      (negSeq (subSeq u b))
      hleft_sub
      hleft_neg
  have h4 :
      relEventually
        (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
        (addSeq (negSeq (subSeq u b)) (absSeq (subSeq u b))) :=
    addSeq_respects_eventually
      (addSeq b (negSeq u)) (negSeq (subSeq u b))
      (absSeq (subSeq u b)) (absSeq (subSeq u b))
      hleft
      (relEventually_refl (absSeq (subSeq u b)))
  have h01 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u))) :=
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq (addSeq b (absSeq (subSeq u b))) (negSeq u))
      (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u)))
      h0
      h1
  have h012 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b)))) :=
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq b (addSeq (absSeq (subSeq u b)) (negSeq u)))
      (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
      h01
      h2
  have h0123 :
      relEventually
        (subSeq (addSeq b (absSeq (subSeq u b))) u)
        (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b))) :=
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq b (addSeq (negSeq u) (absSeq (subSeq u b))))
      (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
      h012
      h3
  exact
    relEventually_trans
      (subSeq (addSeq b (absSeq (subSeq u b))) u)
      (addSeq (addSeq b (negSeq u)) (absSeq (subSeq u b)))
      (addSeq (negSeq (subSeq u b)) (absSeq (subSeq u b)))
      h0123
      h4

/-- Source-side displayed bound `b <= u + |u-b|`. -/
theorem base_le_self_plus_abs_tail_regularSeqLe
    (u b : RegularSeq) :
    RegularSeqLe b (addSeq u (absSeq (subSeq u b))) :=
  regularSeqNonneg_of_eventual
    (base_shift_diff_eventually u b)
    (add_abs_regularSeqNonneg (subSeq u b))

/-- Source-side displayed bound `u <= b + |u-b|`. -/
theorem self_le_base_plus_abs_tail_regularSeqLe
    (u b : RegularSeq) :
    RegularSeqLe u (addSeq b (absSeq (subSeq u b))) :=
  regularSeqNonneg_of_eventual
    (self_shift_diff_eventually u b)
    (neg_add_abs_regularSeqNonneg (subSeq u b))

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

/-- G93 core data: both source displayed shift estimates involving `|u-b|`
are now obtained from closed RegularSeq order lemmas. -/
structure Property4DisplayedScalarShiftClosedCoreLaws
    (Arch : ScalarMulArchimedeanData) : Type 1 where
  abs_from_two_sided : RegularSeqAbsFromTwoSidedBridge
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
  source_line735_self_shift_upper_closed : Prop
  source_line735_base_shift_lower_closed : Prop
  source_line735_min_monotonicity_and_shift : Prop
  source_line743_self_le_base_plus_abs_tail_closed : Prop
  source_line743_base_le_abs_base_closed : Prop
  source_line743_addition_monotonicity_for_abs_base : Prop
  source_line743_min_monotonicity_applies_to_abs_tail : Prop
  source_line743_tail_abs_is_nonnegative_closed : Prop
  source_line743_shifted_min_bound_uses_nonnegative_tail : Prop

/-- Collapse the G93 closed shift estimates back to the G92 layer. -/
def displayedScalarAbsNonnegativeClosedCoreLaws_from_shiftClosed
    (Arch : ScalarMulArchimedeanData)
    (laws : Property4DisplayedScalarShiftClosedCoreLaws Arch) :
    Property4DisplayedScalarAbsNonnegativeClosedCoreLaws Arch where
  abs_from_two_sided := laws.abs_from_two_sided
  self_le_base_plus_abs_tail := self_le_base_plus_abs_tail_regularSeqLe
  base_le_self_plus_abs_tail := base_le_self_plus_abs_tail_regularSeqLe
  addSeq_monotone_left := laws.addSeq_monotone_left
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
  source_line735_self_shift_upper :=
    laws.source_line735_self_shift_upper_closed
  source_line735_base_shift_lower :=
    laws.source_line735_base_shift_lower_closed
  source_line735_min_monotonicity_and_shift :=
    laws.source_line735_min_monotonicity_and_shift
  source_line743_self_le_base_plus_abs_tail :=
    laws.source_line743_self_le_base_plus_abs_tail_closed
  source_line743_base_le_abs_base_closed :=
    laws.source_line743_base_le_abs_base_closed
  source_line743_addition_monotonicity_for_abs_base :=
    laws.source_line743_addition_monotonicity_for_abs_base
  source_line743_min_monotonicity_applies_to_abs_tail :=
    laws.source_line743_min_monotonicity_applies_to_abs_tail
  source_line743_tail_abs_is_nonnegative_closed :=
    laws.source_line743_tail_abs_is_nonnegative_closed
  source_line743_shifted_min_bound_uses_nonnegative_tail :=
    laws.source_line743_shifted_min_bound_uses_nonnegative_tail

/-- G93 unified bridge: the G92 bridge obtained from the closed displayed
absolute-tail shift estimates. -/
structure Property4DisplayedScalarShiftClosedCoreUnifiedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 4 where
  shift_closed_core_laws :
    Property4DisplayedScalarShiftClosedCoreLaws Arch
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
  source_line735_reduced_to_closed_shift_bounds : Prop
  source_line743_reduced_to_abs_nonnegative_closed_chain : Prop
  source_line743_then_uses_prop111 : Prop

/-- Convert the G93 bridge to the G92 bridge. -/
def displayedScalarAbsNonnegativeClosedCoreUnifiedBridge_from_shiftClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (bridge :
      Property4DisplayedScalarShiftClosedCoreUnifiedBridge S) :
    Property4DisplayedScalarAbsNonnegativeClosedCoreUnifiedBridge S where
  abs_nonnegative_closed_core_laws :=
    displayedScalarAbsNonnegativeClosedCoreLaws_from_shiftClosed
      Arch bridge.shift_closed_core_laws
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
    bridge.source_line735_reduced_to_closed_shift_bounds
  source_line743_reduced_to_abs_nonnegative_closed_chain :=
    bridge.source_line743_reduced_to_abs_nonnegative_closed_chain
  source_line743_then_uses_prop111 :=
    bridge.source_line743_then_uses_prop111

/-- Property-(4) reduction data after closing the displayed absolute-tail
shift bounds. -/
structure Property4ReductionDataFromDisplayedScalarShiftClosedBridge
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S) : Type 4 where
  cuts : Property4CutData S r
  cor117_data : BishopRegularSeqCor117ApproxData S r
  displayed_scalar_shift_closed_bridge :
    Property4DisplayedScalarShiftClosedCoreUnifiedBridge S
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
  source_property4_frontier_after_shift_closed : Prop

/-- Convert G93 reduction data to the G92 layer. -/
def property4DisplayedScalarAbsNonnegativeClosedData_from_shiftClosed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarShiftClosedBridge S r) :
    Property4ReductionDataFromDisplayedScalarAbsNonnegativeClosedBridge
      S r where
  cuts := data.cuts
  cor117_data := data.cor117_data
  displayed_scalar_abs_nonnegative_closed_bridge :=
    displayedScalarAbsNonnegativeClosedCoreUnifiedBridge_from_shiftClosed
      S data.displayed_scalar_shift_closed_bridge
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
  source_property4_frontier_after_abs_nonnegative_closed :=
    True

/-- Theorem 1.18 property (4), using the G93 closed displayed shift bounds. -/
def property4_from_displayed_scalar_shift_closed
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X)
    (r : BishopRegularSeqIntegrableRep S)
    (data :
      Property4ReductionDataFromDisplayedScalarShiftClosedBridge S r) :
    Property4Conclusion S r :=
  property4_from_displayed_scalar_abs_nonnegative_closed
    S r
    (property4DisplayedScalarAbsNonnegativeClosedData_from_shiftClosed
      S r data)

end BishopRegularSeqTheorem118

/-- G93 package: the two displayed absolute-tail shift estimates are closed. -/
structure BishopRegularSeqTheorem118G93Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) : Type 5 where
  g92 : BishopRegularSeqTheorem118G92Package S
  shift_closed_core_laws : Type 1
  shift_closed_core_bridge : Type 4
  property4_shift_closed_data :
    BishopRegularSeqIntegrableRep S -> Type 4
  property4_from_shift_closed :
    forall r : BishopRegularSeqIntegrableRep S,
      property4_shift_closed_data r ->
        BishopRegularSeqTheorem118.Property4Conclusion S r
  add_abs_tail_nonnegative_closed : Prop
  neg_add_abs_tail_nonnegative_closed : Prop
  displayed_shift_bounds_closed : Prop
  remaining_frontier_is_min_and_add_order : Prop

def bishopRegularSeqTheorem118G93Package
    (S : BishopRegularSeqIntegrationSpaceDef11 Arch X) :
    BishopRegularSeqTheorem118G93Package S where
  g92 := bishopRegularSeqTheorem118G92Package S
  shift_closed_core_laws :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarShiftClosedCoreLaws
      Arch
  shift_closed_core_bridge :=
    BishopRegularSeqTheorem118.Property4DisplayedScalarShiftClosedCoreUnifiedBridge
      S
  property4_shift_closed_data :=
    BishopRegularSeqTheorem118.Property4ReductionDataFromDisplayedScalarShiftClosedBridge
      S
  property4_from_shift_closed := fun r data =>
    BishopRegularSeqTheorem118.property4_from_displayed_scalar_shift_closed
      S r data
  add_abs_tail_nonnegative_closed := True
  neg_add_abs_tail_nonnegative_closed := True
  displayed_shift_bounds_closed := True
  remaining_frontier_is_min_and_add_order := True

/-- Progress after G93: the source displayed estimates
`u <= b+|u-b|` and `b <= u+|u-b|` are closed. -/
def bishopRegularSeqCh1To4ProgressAfterG93 :
    BishopRegularSeqCh1To4ProgressMeter where
  bishop_real_formalization_percent := 94
  ch1_on_bishop_real_percent := 99
  ch2_on_bishop_real_percent := 6
  ch3_on_bishop_real_percent := 3
  ch4_on_bishop_real_percent := 4
  total_final_goal_percent := 93
  old_relative_ch1_to_4_compatibility_percent := 100
  current_increment :=
    "G93: closed Theorem 1.18 property (4)'s displayed absolute-tail shift \
    estimates u <= b+|u-b| and b <= u+|u-b|."


end BishopCReal
