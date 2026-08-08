import Mathdemo.BishopSec3PresentedEnhancements

/-!
# CReal countable-avoidance support for dyadic smooth levels

This module provides the CReal-native port of the countable-avoidance construction
used to supply smooth level points.  The declarations below establish the
data-valued nested-interval step: from an interval avoiding the first `n`
exception values, construct a nested subinterval avoiding the first `n + 1`
values, using only the CReal strict-order data cotransitivity.
-/

open BishopCReal BishopSec1P

namespace BishopSec3P

universe u

/-- The left retained cut of a CReal interval, expressed in the same grid
coordinates used by the profile-partition machinery. -/
noncomputable def thm36B1_leftCutC (l r : CReal) : CReal :=
  CReal.add (bptRC l (CReal.sub r l) 0) (sigmaScaleC (CReal.sub r l))

/-- The right retained cut of a CReal interval, expressed in the same grid
coordinates used by the profile-partition machinery. -/
noncomputable def thm36B1_rightCutC (l r : CReal) : CReal :=
  CReal.sub (bptRC l (CReal.sub r l) 1) (sigmaScaleC (CReal.sub r l))

/-- The first recursive grid point of the interval `[l,r]` is extensionally
equal to the right endpoint when the grid width is `r-l`. -/
theorem thm36B1_bptRC_one_subC (l r : CReal) :
    bptRC l (CReal.sub r l) 1 ≈ r := by
  have hrc : bptRC l (CReal.sub r l) 1 ≈ bptC l (CReal.sub r l) 1 :=
    bptRC_equiv_bptC l (CReal.sub r l) 1
  have hs : bptC l (CReal.sub r l) 1 ≈
      CReal.add (bptC l (CReal.sub r l) 0) (CReal.sub r l) := by
    simpa using bptC_succC l (CReal.sub r l) 0
  have h0 : bptC l (CReal.sub r l) 0 ≈ l :=
    bptC_zeroC l (CReal.sub r l)
  have hadd : CReal.add (bptC l (CReal.sub r l) 0) (CReal.sub r l) ≈
      CReal.add l (CReal.sub r l) :=
    CReal.add_respects_equiv _ _ _ _ h0 (Setoid.refl (CReal.sub r l))
  have hcancel : CReal.add l (CReal.sub r l) ≈ r := by
    exact Setoid.trans (addSeq_comm_eventually l (CReal.sub r l))
      (addSeq_sub_right_cancel_eventually r l)
  exact Setoid.trans hrc (Setoid.trans hs (Setoid.trans hadd hcancel))

/-- Positivity of the grid margin inside a proper CReal interval. -/
theorem thm36B1_sigma_posC {l r : CReal}
    (hlr : regularSeqLtProp l r) :
    regularSeqLtProp CReal.zero (sigmaScaleC (CReal.sub r l)) :=
  sigmaScaleC_pos_prop
    (regularSeqLtData_of_ltPropC (regularSeqLtProp_zero_lt_sub hlr))

/-- The left cut lies strictly to the right of the left endpoint. -/
theorem thm36B1_left_lt_leftCutC {l r : CReal}
    (hlr : regularSeqLtProp l r) :
    regularSeqLtProp l (thm36B1_leftCutC l r) := by
  have h0 : bptRC l (CReal.sub r l) 0 ≈ l :=
    Setoid.trans (bptRC_equiv_bptC l (CReal.sub r l) 0)
      (bptC_zeroC l (CReal.sub r l))
  have hbase : regularSeqLtProp (bptRC l (CReal.sub r l) 0)
      (CReal.add (bptRC l (CReal.sub r l) 0)
        (sigmaScaleC (CReal.sub r l))) :=
    regularSeqLtProp_self_add_sigmaC (bptRC l (CReal.sub r l) 0)
      (thm36B1_sigma_posC hlr)
  exact regularSeqLtProp_of_left_eventual (Setoid.symm h0) hbase

/-- The right cut lies strictly to the left of the right endpoint. -/
theorem thm36B1_rightCut_lt_rightC {l r : CReal}
    (hlr : regularSeqLtProp l r) :
    regularSeqLtProp (thm36B1_rightCutC l r) r := by
  have h1 : bptRC l (CReal.sub r l) 1 ≈ r :=
    thm36B1_bptRC_one_subC l r
  have hbase : regularSeqLtProp
      (CReal.sub (bptRC l (CReal.sub r l) 1)
        (sigmaScaleC (CReal.sub r l)))
      (bptRC l (CReal.sub r l) 1) :=
    regularSeqLtProp_sub_sigma_selfC (bptRC l (CReal.sub r l) 1)
      (thm36B1_sigma_posC hlr)
  exact regularSeqLtProp_of_right_eventual h1 hbase

/-- The two retained cuts leave a strict middle gap. -/
theorem thm36B1_leftCut_lt_rightCutC {l r : CReal}
    (hlr : regularSeqLtProp l r) :
    regularSeqLtProp (thm36B1_leftCutC l r) (thm36B1_rightCutC l r) := by
  exact regularSeqLtData_to_prop
    (gridSlot_lt_dataC (a := l)
      (regularSeqLtData_of_ltPropC (regularSeqLtProp_zero_lt_sub hlr)) 0)


/-- Eventual form of the raw bridge `2 * sigmaScaleC d = halfScaleC d`. -/
theorem two_sigma_relEventually_halfScaleC (d : CReal) :
    relEventually (addSeq (sigmaScaleC d) (sigmaScaleC d)) (halfScaleC d) :=
  rel_to_relEventually _ _ (two_sigma_rel_halfScale d)

/-- Twice the pointwise half-scale is eventually the original representative. -/
theorem halfScaleC_add_self_eventuallyC (x : CReal) :
    relEventually (addSeq (halfScaleC x) (halfScaleC x)) x := by
  apply rel_to_relEventually
  intro n
  change Le
    (BishopC.COF_core.abs
      ((BishopC.COF_core.half * x.val (n + 1) +
          BishopC.COF_core.half * x.val (n + 1)) - x.val n))
    (tol n)
  rw [show BishopC.COF_core.half * x.val (n + 1) +
          BishopC.COF_core.half * x.val (n + 1) = x.val (n + 1) by
        exact scalar_half_add_self_mul (x.val (n + 1))]
  exact BishopC.le_trans (x.regular (n + 1) n) (eps_succ_add_le_tol n)

/-- The pointwise half-scale is weakly below the concrete CReal half-product. -/
theorem halfScaleC_le_mul_halfC (x : CReal) :
    RegularSeqLe (halfScaleC x) (CReal.mul CReal.half x) := by
  intro hbad
  have hbad_lt : regularSeqLtProp (CReal.mul CReal.half x) (halfScaleC x) :=
    regularSeqLtProp_reverse_of_le_counterexample hbad
  have hadd : regularSeqLtProp
      (addSeq (CReal.mul CReal.half x) (CReal.mul CReal.half x))
      (addSeq (halfScaleC x) (halfScaleC x)) :=
    regularSeqLtProp_add hbad_lt hbad_lt
  have hleft : relEventually
      (addSeq (CReal.mul CReal.half x) (CReal.mul CReal.half x)) x := by
    simpa [CReal.mul, CReal.half] using
      (addSeq_half_mul_self_eventually cRatScalarMulArch x)
  have hright : relEventually (addSeq (halfScaleC x) (halfScaleC x)) x :=
    halfScaleC_add_self_eventuallyC x
  have hxx : regularSeqLtProp x x :=
    regularSeqLtProp_of_left_eventual (relEventually_symm _ _ hleft)
      (regularSeqLtProp_of_right_eventual hright hadd)
  exact regularSeqLtProp_irrefl x hxx

/-- `sigmaScaleC d` is weakly bounded by the pointwise half-scale of `d`. -/
theorem sigmaScaleC_le_halfScaleC {d : CReal}
    (hd : regularSeqLtData CReal.zero d) :
    RegularSeqLe (sigmaScaleC d) (halfScaleC d) := by
  have h0σ : RegularSeqLe CReal.zero (sigmaScaleC d) :=
    sigmaScaleC_nonneg hd
  have hσ_le_σ0 : RegularSeqLe (sigmaScaleC d)
      (addSeq (sigmaScaleC d) CReal.zero) := by
    exact regularSeqLe_of_right_eventual
      (relEventually_symm _ _ (CReal.add_zero (sigmaScaleC d)))
      (regularSeqLe_refl (sigmaScaleC d))
  have hσ0_le_σσ : RegularSeqLe (addSeq (sigmaScaleC d) CReal.zero)
      (addSeq (sigmaScaleC d) (sigmaScaleC d)) :=
    regularSeqLe_add (regularSeqLe_refl (sigmaScaleC d)) h0σ
  exact regularSeqLe_of_right_eventual (two_sigma_relEventually_halfScaleC d)
    (regularSeqLe_trans hσ_le_σ0 hσ0_le_σσ)

/-- Successor width scale doubles to the previous width scale. -/
theorem lemma34WidthScale_succ_add_selfC (a b : CReal) (n : Nat) :
    CReal.add (lemma34WidthScaleC a b (n + 1))
      (lemma34WidthScaleC a b (n + 1)) ≈ lemma34WidthScaleC a b n := by
  unfold lemma34WidthScaleC
  have hdist : CReal.add
        (CReal.mul (CReal.sub b a) (halfPow (n + 1)))
        (CReal.mul (CReal.sub b a) (halfPow (n + 1))) ≈
      CReal.mul (CReal.sub b a)
        (CReal.add (halfPow (n + 1)) (halfPow (n + 1))) := by
    exact Setoid.symm
      (CReal.left_distrib (CReal.sub b a) (halfPow (n + 1)) (halfPow (n + 1)))
  exact Setoid.trans hdist
    (CReal.mul_respects_equiv _ _ _ _ (Setoid.refl (CReal.sub b a))
      (halfPow_succ_add_self n))

/-- Multiplying the level-n width scale by one half is bounded by the successor scale. -/
theorem mul_half_widthScale_le_succC (a b : CReal) (n : Nat) :
    RegularSeqLe (CReal.mul CReal.half (lemma34WidthScaleC a b n))
      (lemma34WidthScaleC a b (n + 1)) := by
  intro hbad
  have hbad_lt : regularSeqLtProp (lemma34WidthScaleC a b (n + 1))
      (CReal.mul CReal.half (lemma34WidthScaleC a b n)) :=
    regularSeqLtProp_reverse_of_le_counterexample hbad
  have hadd : regularSeqLtProp
      (CReal.add (lemma34WidthScaleC a b (n + 1))
        (lemma34WidthScaleC a b (n + 1)))
      (CReal.add (CReal.mul CReal.half (lemma34WidthScaleC a b n))
        (CReal.mul CReal.half (lemma34WidthScaleC a b n))) :=
    regularSeqLtProp_add hbad_lt hbad_lt
  have hleft : relEventually
      (CReal.add (lemma34WidthScaleC a b (n + 1))
        (lemma34WidthScaleC a b (n + 1)))
      (lemma34WidthScaleC a b n) :=
    lemma34WidthScale_succ_add_selfC a b n
  have hright : relEventually
      (CReal.add (CReal.mul CReal.half (lemma34WidthScaleC a b n))
        (CReal.mul CReal.half (lemma34WidthScaleC a b n)))
      (lemma34WidthScaleC a b n) :=
    half_mul_add_selfC (lemma34WidthScaleC a b n)
  have hxx : regularSeqLtProp (lemma34WidthScaleC a b n)
      (lemma34WidthScaleC a b n) :=
    regularSeqLtProp_of_left_eventual (relEventually_symm _ _ hleft)
      (regularSeqLtProp_of_right_eventual hright hadd)
  exact regularSeqLtProp_irrefl _ hxx

/-- A retained `sigmaScaleC` width bounded at level `n` is bounded at level `n+1`. -/
theorem thm36B1_sigmaScale_le_next_widthScaleC {a b d : CReal} {n : Nat}
    (hd : regularSeqLtData CReal.zero d)
    (hwidth : RegularSeqLe d (lemma34WidthScaleC a b n)) :
    RegularSeqLe (sigmaScaleC d) (lemma34WidthScaleC a b (n + 1)) := by
  have hσ_half : RegularSeqLe (sigmaScaleC d) (halfScaleC d) :=
    sigmaScaleC_le_halfScaleC hd
  have hhalf_mul : RegularSeqLe (halfScaleC d) (CReal.mul CReal.half d) :=
    halfScaleC_le_mul_halfC d
  have hhalf_nn : RegularSeqNonneg CReal.half :=
    regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC CReal.half_pos_E)
  have hmul : RegularSeqLe (CReal.mul CReal.half d)
      (CReal.mul CReal.half (lemma34WidthScaleC a b n)) :=
    regularSeqLe_mul_left_of_nonnegC hwidth hhalf_nn
  exact regularSeqLe_trans hσ_half
    (regularSeqLe_trans hhalf_mul
      (regularSeqLe_trans hmul (mul_half_widthScale_le_succC a b n)))

/-- Width of the left retained interval is extensionally `sigmaScaleC`. -/
theorem thm36B1_leftCut_width_equivC (l r : CReal) :
    CReal.sub (thm36B1_leftCutC l r) l ≈ sigmaScaleC (CReal.sub r l) := by
  have h0 : bptRC l (CReal.sub r l) 0 ≈ l :=
    Setoid.trans (bptRC_equiv_bptC l (CReal.sub r l) 0)
      (bptC_zeroC l (CReal.sub r l))
  have hsub : CReal.sub (thm36B1_leftCutC l r) l ≈
      CReal.sub (CReal.add (bptRC l (CReal.sub r l) 0)
        (sigmaScaleC (CReal.sub r l))) (bptRC l (CReal.sub r l) 0) :=
    CReal.sub_respects_equiv _ _ _ _ (Setoid.refl _) (Setoid.symm h0)
  exact Setoid.trans hsub
    (add_sub_cancel_leftC (bptRC l (CReal.sub r l) 0)
      (sigmaScaleC (CReal.sub r l)))

/-- Width of the right retained interval is extensionally `sigmaScaleC`. -/
theorem thm36B1_rightCut_width_equivC (l r : CReal) :
    CReal.sub r (thm36B1_rightCutC l r) ≈ sigmaScaleC (CReal.sub r l) := by
  have h1 : bptRC l (CReal.sub r l) 1 ≈ r :=
    thm36B1_bptRC_one_subC l r
  have hsub : CReal.sub r (thm36B1_rightCutC l r) ≈
      CReal.sub (bptRC l (CReal.sub r l) 1)
        (CReal.sub (bptRC l (CReal.sub r l) 1) (sigmaScaleC (CReal.sub r l))) :=
    CReal.sub_respects_equiv _ _ _ _ (Setoid.symm h1) (Setoid.refl _)
  have hcancel : CReal.sub (bptRC l (CReal.sub r l) 1)
        (CReal.sub (bptRC l (CReal.sub r l) 1) (sigmaScaleC (CReal.sub r l)))
        ≈ sigmaScaleC (CReal.sub r l) := by
    have hq : mkQuot (CReal.sub (bptRC l (CReal.sub r l) 1)
        (CReal.sub (bptRC l (CReal.sub r l) 1) (sigmaScaleC (CReal.sub r l)))) =
        mkQuot (sigmaScaleC (CReal.sub r l)) := by
      letI : CommRing CRealQuot :=
        cRealQuotCommRingConcreteWith cRatScalarMulArch
      let B : CRealQuot := mkQuot (bptRC l (CReal.sub r l) 1)
      let S : CRealQuot := mkQuot (sigmaScaleC (CReal.sub r l))
      change B - (B - S) = S
      ring
    exact Quotient.exact hq
  exact Setoid.trans hsub hcancel

/-- Width of the base interval is bounded by the level-zero ambient width scale. -/
theorem thm36B1_interval_base_width_boundC {a b : CReal}
    (hab : regularSeqLtProp a b) :
    RegularSeqLe (CReal.sub (thm36B1_rightCutC a b) (thm36B1_leftCutC a b))
      (lemma34WidthScaleC a b 0) := by
  have hd : regularSeqLtData CReal.zero (CReal.sub b a) :=
    regularSeqLtData_of_ltPropC (regularSeqLtProp_zero_lt_sub hab)
  have hle_half : RegularSeqLe
      (CReal.sub (thm36B1_rightCutC a b) (thm36B1_leftCutC a b))
      (halfScaleC (CReal.sub b a)) := by
    have hgrid : relEventually
        (CReal.sub (CReal.sub (bptRC a (CReal.sub b a) 1) (sigmaScaleC (CReal.sub b a)))
          (CReal.add (bptRC a (CReal.sub b a) 0) (sigmaScaleC (CReal.sub b a))))
        (CReal.sub (CReal.sub b a)
          (CReal.add (sigmaScaleC (CReal.sub b a)) (sigmaScaleC (CReal.sub b a)))) :=
      relEventually_symm _ _
        (rel_to_relEventually _ _ (two_sigma_sub_bridge_grid a (CReal.sub b a) 0))
    have hhalf0 : relEventually
        (CReal.sub (CReal.sub b a)
          (CReal.add (sigmaScaleC (CReal.sub b a)) (sigmaScaleC (CReal.sub b a))))
        (CReal.sub (halfScaleC (CReal.sub b a)) CReal.zero) :=
      relEventually_symm _ _
        (rel_to_relEventually _ _
          (two_sigma_sub_bridge (CReal.sub b a) CReal.zero (fun _ => rfl)))
    have hzero : relEventually
        (CReal.sub (halfScaleC (CReal.sub b a)) CReal.zero)
        (halfScaleC (CReal.sub b a)) :=
      subSeq_zero_right_eventually (halfScaleC (CReal.sub b a))
    have hraw : relEventually
        (CReal.sub (thm36B1_rightCutC a b) (thm36B1_leftCutC a b))
        (halfScaleC (CReal.sub b a)) := by
      exact relEventually_trans _ _ _ hgrid (relEventually_trans _ _ _ hhalf0 hzero)
    exact regularSeqLe_of_relEventually hraw
  have hhalf_mul : RegularSeqLe (halfScaleC (CReal.sub b a))
      (CReal.mul CReal.half (CReal.sub b a)) := halfScaleC_le_mul_halfC _
  have hmul_le : RegularSeqLe (CReal.mul CReal.half (CReal.sub b a))
      (CReal.sub b a) := by
    have hhalf_le_one : RegularSeqLe CReal.half CReal.one := by
      have h := thm36C_halfPow_le_oneC 1
      simpa [halfPow, CReal.epsSeq] using h
    have hdnn : RegularSeqNonneg (CReal.sub b a) :=
      regularSeqNonneg_of_zero_le (regularSeqLe_of_ltPropC (regularSeqLtProp_zero_lt_sub hab))
    exact regularSeqLe_of_right_eventual (CReal.one_mul (CReal.sub b a))
      (regularSeqLe_mul_right_of_nonnegC hhalf_le_one hdnn)
  have hws0 : lemma34WidthScaleC a b 0 ≈ CReal.sub b a := by
    unfold lemma34WidthScaleC
    exact Setoid.trans
      (CReal.mul_respects_equiv _ _ _ _ (Setoid.refl (CReal.sub b a)) halfPow_zero)
      (CReal.mul_one (CReal.sub b a))
  exact regularSeqLe_of_right_eventual (Setoid.symm hws0)
    (regularSeqLe_trans hle_half (regularSeqLe_trans hhalf_mul hmul_le))

/-- State of the CReal nested interval after avoiding `s 0, ..., s(n-1)`. -/
structure Thm36B1IntervalC (s : Nat -> CReal) (a b : CReal) (n : Nat) :
    Type where
  left : CReal
  right : CReal
  proper : regularSeqLtProp left right
  a_lt_left : regularSeqLtProp a left
  right_lt_b : regularSeqLtProp right b
  width : RegularSeqLe (CReal.sub right left) (lemma34WidthScaleC a b n)
  avoided : forall j : Nat, j < n ->
    regularSeqLtProp (s j) left ∨ regularSeqLtProp right (s j)

/-- Previously avoided values remain avoided when passing to a nested
subinterval. -/
theorem thm36B1_preserve_avoidedC {s : Nat -> CReal} {a b : CReal} {n : Nat}
    (I : Thm36B1IntervalC s a b n) {l r : CReal}
    (hleft : RegularSeqLe I.left l) (hright : RegularSeqLe r I.right)
    {j : Nat} (hj : j < n) :
    regularSeqLtProp (s j) l ∨ regularSeqLtProp r (s j) := by
  rcases I.avoided j hj with hsj | hjs
  · left
    exact regularSeqLtProp_of_lt_of_le hsj hleft
  · right
    exact regularSeqLtProp_of_le_of_lt hright hjs

/-- Base interval obtained by trimming both endpoints. -/
noncomputable def thm36B1_interval_baseC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) : Thm36B1IntervalC s a b 0 where
  left := thm36B1_leftCutC a b
  right := thm36B1_rightCutC a b
  proper := thm36B1_leftCut_lt_rightCutC hab
  a_lt_left := thm36B1_left_lt_leftCutC hab
  right_lt_b := thm36B1_rightCut_lt_rightC hab
  width := thm36B1_interval_base_width_boundC hab
  avoided := by
    intro j hj
    exact False.elim (Nat.not_lt_zero j hj)

/-- One constructive avoidance step, using data-valued cotransitivity across
the middle gap between the two cuts. -/
noncomputable def thm36B1_interval_stepC {s : Nat -> CReal} {a b : CReal}
    {n : Nat} (I : Thm36B1IntervalC s a b n) :
    {J : Thm36B1IntervalC s a b (n + 1) //
      RegularSeqLe I.left J.left ∧ RegularSeqLe J.right I.right} := by
  let ql : CReal := thm36B1_leftCutC I.left I.right
  let qr : CReal := thm36B1_rightCutC I.left I.right
  have hlql : regularSeqLtProp I.left ql :=
    thm36B1_left_lt_leftCutC I.proper
  have hqlqr : regularSeqLtProp ql qr :=
    thm36B1_leftCut_lt_rightCutC I.proper
  have hqrr : regularSeqLtProp qr I.right :=
    thm36B1_rightCut_lt_rightC I.proper
  have hgapData : regularSeqLtData ql qr :=
    regularSeqLtData_of_ltPropC hqlqr
  have hql_le_right : RegularSeqLe ql I.right :=
    regularSeqLe_of_ltPropC (regularSeqLtProp_trans ql qr I.right hqlqr hqrr)
  have hleft_le_qr : RegularSeqLe I.left qr :=
    regularSeqLe_of_ltPropC (regularSeqLtProp_trans I.left ql qr hlql hqlqr)
  cases regularSeqLtData_cotrans ql qr (s n) hgapData with
  | inl hqls =>
      let J : Thm36B1IntervalC s a b (n + 1) := {
        left := I.left
        right := ql
        proper := hlql
        a_lt_left := I.a_lt_left
        right_lt_b := regularSeqLtProp_of_le_of_lt hql_le_right I.right_lt_b
        width := by
          have hd : regularSeqLtData CReal.zero (CReal.sub I.right I.left) :=
            regularSeqLtData_of_ltPropC (regularSeqLtProp_zero_lt_sub I.proper)
          have hσ : RegularSeqLe (sigmaScaleC (CReal.sub I.right I.left))
              (lemma34WidthScaleC a b (n + 1)) :=
            thm36B1_sigmaScale_le_next_widthScaleC hd I.width
          exact regularSeqLe_of_left_eventual
            (thm36B1_leftCut_width_equivC I.left I.right) hσ
        avoided := by
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjn | hjeq
          · exact thm36B1_preserve_avoidedC I
              (regularSeqLe_refl I.left) hql_le_right hjn
          · right
            simpa [hjeq] using regularSeqLtData_to_prop hqls
      }
      exact ⟨J, regularSeqLe_refl I.left, hql_le_right⟩
  | inr hsqr =>
      let J : Thm36B1IntervalC s a b (n + 1) := {
        left := qr
        right := I.right
        proper := hqrr
        a_lt_left := regularSeqLtProp_trans a I.left qr I.a_lt_left
          (regularSeqLtProp_trans I.left ql qr hlql hqlqr)
        right_lt_b := I.right_lt_b
        width := by
          have hd : regularSeqLtData CReal.zero (CReal.sub I.right I.left) :=
            regularSeqLtData_of_ltPropC (regularSeqLtProp_zero_lt_sub I.proper)
          have hσ : RegularSeqLe (sigmaScaleC (CReal.sub I.right I.left))
              (lemma34WidthScaleC a b (n + 1)) :=
            thm36B1_sigmaScale_le_next_widthScaleC hd I.width
          exact regularSeqLe_of_left_eventual
            (thm36B1_rightCut_width_equivC I.left I.right) hσ
        avoided := by
          intro j hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjn | hjeq
          · exact thm36B1_preserve_avoidedC I
              hleft_le_qr (regularSeqLe_refl I.right) hjn
          · left
            simpa [hjeq] using regularSeqLtData_to_prop hsqr
      }
      exact ⟨J, hleft_le_qr, regularSeqLe_refl I.right⟩

/-- The recursively constructed CReal interval sequence. -/
noncomputable def thm36B1_intervalSeqC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) :
    (n : Nat) -> Thm36B1IntervalC s a b n
  | 0 => thm36B1_interval_baseC hab
  | n + 1 => (thm36B1_interval_stepC (thm36B1_intervalSeqC hab n)).val

/-- Consecutive intervals are nested. -/
theorem thm36B1_intervalSeq_step_nestedC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (n : Nat) :
    RegularSeqLe (thm36B1_intervalSeqC (s := s) hab n).left
        (thm36B1_intervalSeqC (s := s) hab (n + 1)).left ∧
      RegularSeqLe (thm36B1_intervalSeqC (s := s) hab (n + 1)).right
        (thm36B1_intervalSeqC (s := s) hab n).right := by
  exact (thm36B1_interval_stepC
    (thm36B1_intervalSeqC (s := s) hab n)).property

/-- Any later interval is nested in any earlier interval. -/
theorem thm36B1_intervalSeq_nestedC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) {p q : Nat} (hpq : p <= q) :
    RegularSeqLe (thm36B1_intervalSeqC (s := s) hab p).left
        (thm36B1_intervalSeqC (s := s) hab q).left ∧
      RegularSeqLe (thm36B1_intervalSeqC (s := s) hab q).right
        (thm36B1_intervalSeqC (s := s) hab p).right := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
  induction d with
  | zero =>
      exact ⟨regularSeqLe_refl _, regularSeqLe_refl _⟩
  | succ d ih =>
      have ih' := ih (Nat.le_add_right p d)
      have hs := thm36B1_intervalSeq_step_nestedC (s := s) hab (p + d)
      exact ⟨regularSeqLe_trans ih'.1 hs.1,
        regularSeqLe_trans hs.2 ih'.2⟩

/-- Left endpoints of the CReal avoidance intervals. -/
noncomputable def thm36B1_leftSeqC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (n : Nat) : CReal :=
  (thm36B1_intervalSeqC (s := s) hab n).left

/-- Right endpoints of the CReal avoidance intervals. -/
noncomputable def thm36B1_rightSeqC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (n : Nat) : CReal :=
  (thm36B1_intervalSeqC (s := s) hab n).right

/-- The left endpoint sequence is monotone increasing. -/
theorem thm36B1_leftSeq_monoC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) {p q : Nat} (hpq : p <= q) :
    RegularSeqLe (thm36B1_leftSeqC (s := s) hab p)
      (thm36B1_leftSeqC (s := s) hab q) := by
  exact (thm36B1_intervalSeq_nestedC (s := s) hab hpq).1

/-- The right endpoint sequence is monotone decreasing. -/
theorem thm36B1_rightSeq_antitoneC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) {p q : Nat} (hpq : p <= q) :
    RegularSeqLe (thm36B1_rightSeqC (s := s) hab q)
      (thm36B1_rightSeqC (s := s) hab p) := by
  exact (thm36B1_intervalSeq_nestedC (s := s) hab hpq).2

/-- Any left endpoint is below any right endpoint. -/
theorem thm36B1_leftSeq_le_rightSeqC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (m k : Nat) :
    RegularSeqLe (thm36B1_leftSeqC (s := s) hab m)
      (thm36B1_rightSeqC (s := s) hab k) := by
  rcases Nat.le_total m k with hmk | hkm
  · exact regularSeqLe_trans
      (thm36B1_leftSeq_monoC (s := s) hab hmk)
      (regularSeqLe_of_ltPropC
        (thm36B1_intervalSeqC (s := s) hab k).proper)
  · exact regularSeqLe_trans
      (regularSeqLe_of_ltPropC
        (thm36B1_intervalSeqC (s := s) hab m).proper)
      (thm36B1_rightSeq_antitoneC (s := s) hab hkm)

/-- Differences of later left endpoints are bounded by the width of any
earlier interval containing both of them. -/
theorem thm36B1_leftSeq_absSub_le_widthC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (M m k : Nat) (hm : M <= m) (hk : M <= k) :
    RegularSeqLe
      (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab m)
                      (thm36B1_leftSeqC (s := s) hab k)))
      (CReal.sub (thm36B1_rightSeqC (s := s) hab M)
                 (thm36B1_leftSeqC (s := s) hab M)) := by
  rcases Nat.le_total m k with hmk | hkm
  · have hmk_le : RegularSeqLe (thm36B1_leftSeqC (s := s) hab m)
        (thm36B1_leftSeqC (s := s) hab k) :=
      thm36B1_leftSeq_monoC (s := s) hab hmk
    have hdiff_nonneg :
        RegularSeqLe zeroSeq
          (subSeq (thm36B1_leftSeqC (s := s) hab k)
                  (thm36B1_leftSeqC (s := s) hab m)) :=
      regularSeqLe_zero_of_nonneg hmk_le
    have habs_rev :
        RegularSeqLe
          (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab k)
                          (thm36B1_leftSeqC (s := s) hab m)))
          (subSeq (thm36B1_leftSeqC (s := s) hab k)
                  (thm36B1_leftSeqC (s := s) hab m)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have habs :
        RegularSeqLe
          (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab m)
                          (thm36B1_leftSeqC (s := s) hab k)))
          (subSeq (thm36B1_leftSeqC (s := s) hab k)
                  (thm36B1_leftSeqC (s := s) hab m)) :=
      regularSeqLe_of_left_eventual
        (absSeq_subSeq_comm_eventually _ _) habs_rev
    have hA :
        RegularSeqLe
          (subSeq (thm36B1_leftSeqC (s := s) hab k)
                  (thm36B1_leftSeqC (s := s) hab m))
          (subSeq (thm36B1_rightSeqC (s := s) hab M)
                  (thm36B1_leftSeqC (s := s) hab m)) :=
      subSeq_monotone_left_regularSeqLe _ _ _
        (thm36B1_leftSeq_le_rightSeqC (s := s) hab k M)
    have hB :
        RegularSeqLe
          (subSeq (thm36B1_rightSeqC (s := s) hab M)
                  (thm36B1_leftSeqC (s := s) hab m))
          (subSeq (thm36B1_rightSeqC (s := s) hab M)
                  (thm36B1_leftSeqC (s := s) hab M)) :=
      regularSeqLe_subSeq_right _
        (thm36B1_leftSeq_monoC (s := s) hab hm)
    exact regularSeqLe_trans habs
      (regularSeqLe_trans hA hB)
  · have hkm_le : RegularSeqLe (thm36B1_leftSeqC (s := s) hab k)
        (thm36B1_leftSeqC (s := s) hab m) :=
      thm36B1_leftSeq_monoC (s := s) hab hkm
    have hdiff_nonneg :
        RegularSeqLe zeroSeq
          (subSeq (thm36B1_leftSeqC (s := s) hab m)
                  (thm36B1_leftSeqC (s := s) hab k)) :=
      regularSeqLe_zero_of_nonneg hkm_le
    have habs :
        RegularSeqLe
          (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab m)
                          (thm36B1_leftSeqC (s := s) hab k)))
          (subSeq (thm36B1_leftSeqC (s := s) hab m)
                  (thm36B1_leftSeqC (s := s) hab k)) :=
      regularSeqLe_abs_of_nonneg hdiff_nonneg
    have hA :
        RegularSeqLe
          (subSeq (thm36B1_leftSeqC (s := s) hab m)
                  (thm36B1_leftSeqC (s := s) hab k))
          (subSeq (thm36B1_rightSeqC (s := s) hab M)
                  (thm36B1_leftSeqC (s := s) hab k)) :=
      subSeq_monotone_left_regularSeqLe _ _ _
        (thm36B1_leftSeq_le_rightSeqC (s := s) hab m M)
    have hB :
        RegularSeqLe
          (subSeq (thm36B1_rightSeqC (s := s) hab M)
                  (thm36B1_leftSeqC (s := s) hab k))
          (subSeq (thm36B1_rightSeqC (s := s) hab M)
                  (thm36B1_leftSeqC (s := s) hab M)) :=
      regularSeqLe_subSeq_right _
        (thm36B1_leftSeq_monoC (s := s) hab hk)
    exact regularSeqLe_trans habs
      (regularSeqLe_trans hA hB)

/-- Width of the canonical interval at level `n`. -/
theorem thm36B1_intervalSeq_widthC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (n : Nat) :
    RegularSeqLe
      (CReal.sub (thm36B1_rightSeqC (s := s) hab n)
        (thm36B1_leftSeqC (s := s) hab n))
      (lemma34WidthScaleC a b n) :=
  (thm36B1_intervalSeqC (s := s) hab n).width

/-- Later left endpoints are bounded by the dyadic ambient width scale. -/
theorem thm36B1_leftSeq_absSub_le_widthScaleC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (M m k : Nat) (hm : M <= m) (hk : M <= k) :
    RegularSeqLe
      (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab m)
                      (thm36B1_leftSeqC (s := s) hab k)))
      (lemma34WidthScaleC a b M) :=
  regularSeqLe_trans
    (thm36B1_leftSeq_absSub_le_widthC (s := s) hab M m k hm hk)
    (thm36B1_intervalSeq_widthC (s := s) hab M)

/-- Explicit Cauchy data for the left endpoints of the CReal avoidance tower. -/
noncomputable def thm36B1_leftSeqCauchyDataC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) :
    CRealRepSequenceCauchyData (fun k => thm36B1_leftSeqC (s := s) hab k) where
  cmod := fun g =>
    (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
      (halfPow g) (posEventuallyData_halfPowC g)).val
  close_eventually := by
    intro g m k hm hk
    have hK :
        regularSeqLtProp
          (lemma34WidthScaleC a b
            (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
              (halfPow g) (posEventuallyData_halfPowC g)).val)
          (halfPow g) :=
      (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
        (halfPow g) (posEventuallyData_halfPowC g)).property
    have hcm :
        RegularSeqLe
          (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab m)
                          (thm36B1_leftSeqC (s := s) hab k)))
          (lemma34WidthScaleC a b
            (lemma34WidthScaleEventualSmallDataC_standard (a := a) (b := b)
              (halfPow g) (posEventuallyData_halfPowC g)).val) :=
      thm36B1_leftSeq_absSub_le_widthScaleC (s := s) hab _ m k hm hk
    have hlt :
        regularSeqLtProp
          (absSeq (subSeq (thm36B1_leftSeqC (s := s) hab m)
                          (thm36B1_leftSeqC (s := s) hab k)))
          (halfPow g) :=
      regularSeqLtProp_of_le_of_lt hcm hK
    exact repCloseAtGauge_of_absGap _ _ g hlt

/-- Rep-carrying limit of the left endpoint sequence. -/
noncomputable def thm36B1_leftLimitReprC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) :
    CRealRepLimitData (fun k => thm36B1_leftSeqC (s := s) hab k) :=
  CReal.complete_repCarrying_data _ (thm36B1_leftSeqCauchyDataC (s := s) hab)

/-- Each left endpoint lies weakly below the constructed limit. -/
theorem thm36B1_leftSeq_le_limitC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (k : Nat) :
    RegularSeqLe (thm36B1_leftSeqC (s := s) hab k)
      (thm36B1_leftLimitReprC (s := s) hab).limit :=
  repLimitData_ge_of_eventually_ge (thm36B1_leftLimitReprC (s := s) hab)
    (thm36B1_leftSeqC (s := s) hab k) k
    (fun m hm => thm36B1_leftSeq_monoC (s := s) hab hm)

/-- The constructed limit lies weakly below each right endpoint. -/
theorem thm36B1_limit_le_rightSeqC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (k : Nat) :
    RegularSeqLe (thm36B1_leftLimitReprC (s := s) hab).limit
      (thm36B1_rightSeqC (s := s) hab k) :=
  repLimitData_le_of_eventually_le (thm36B1_leftLimitReprC (s := s) hab)
    (thm36B1_rightSeqC (s := s) hab k) 0
    (fun m _hm => thm36B1_leftSeq_le_rightSeqC (s := s) hab m k)

/-- The constructed limit lies strictly inside the ambient interval. -/
theorem thm36B1_limit_strict_boundsC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) :
    regularSeqLtProp a (thm36B1_leftLimitReprC (s := s) hab).limit ∧
      regularSeqLtProp (thm36B1_leftLimitReprC (s := s) hab).limit b := by
  constructor
  · exact regularSeqLtProp_of_lt_of_le
      (thm36B1_intervalSeqC (s := s) hab 0).a_lt_left
      (thm36B1_leftSeq_le_limitC (s := s) hab 0)
  · exact regularSeqLtProp_of_le_of_lt
      (thm36B1_limit_le_rightSeqC (s := s) hab 0)
      (thm36B1_intervalSeqC (s := s) hab 0).right_lt_b

/-- The limit point is apart from every forbidden value. -/
theorem thm36B1_limit_apartC {s : Nat -> CReal} {a b : CReal}
    (hab : regularSeqLtProp a b) (n : Nat) :
    regularSeqLtProp CReal.zero
      (CReal.abs (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))) := by
  have hav := (thm36B1_intervalSeqC (s := s) hab (n + 1)).avoided n
    (Nat.lt_succ_self n)
  have hleft_in := thm36B1_leftSeq_le_limitC (s := s) hab (n + 1)
  have hright_in := thm36B1_limit_le_rightSeqC (s := s) hab (n + 1)
  rcases hav with hsn_left | hright_sn
  · have hst : regularSeqLtProp (s n)
        (thm36B1_leftLimitReprC (s := s) hab).limit :=
      regularSeqLtProp_of_lt_of_le hsn_left hleft_in
    have hdiff : regularSeqLtProp CReal.zero
        (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)) :=
      regularSeqLtProp_zero_lt_sub hst
    have hnonneg : ¬ CReal.ltE
        (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))
        CReal.zero := fun hc =>
      regularSeqLtProp_irrefl CReal.zero
        (regularSeqLtProp_trans CReal.zero
          (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))
          CReal.zero hdiff hc)
    have habs_eq : CReal.abs
        (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)) ≈
        CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n) :=
      CReal.abs_of_nonneg_E hnonneg
    exact regularSeqLtProp_of_right_eventual (Setoid.symm habs_eq) hdiff
  · have hts : regularSeqLtProp
        (thm36B1_leftLimitReprC (s := s) hab).limit (s n) :=
      regularSeqLtProp_of_le_of_lt hright_in hright_sn
    have hdiff : regularSeqLtProp CReal.zero
        (CReal.sub (s n) (thm36B1_leftLimitReprC (s := s) hab).limit) :=
      regularSeqLtProp_zero_lt_sub hts
    have h0neg : regularSeqLtProp CReal.zero
        (CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))) :=
      regularSeqLtProp_of_right_eventual
        (Setoid.symm (neg_sub_eventualC
          (thm36B1_leftLimitReprC (s := s) hab).limit (s n))) hdiff
    have hnonneg : ¬ CReal.ltE
        (CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)))
        CReal.zero := fun hc =>
      regularSeqLtProp_irrefl CReal.zero
        (regularSeqLtProp_trans CReal.zero
          (CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)))
          CReal.zero h0neg hc)
    have h1 : CReal.abs
        (CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))) ≈
        CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)) :=
      CReal.abs_of_nonneg_E hnonneg
    have h2 : CReal.abs
        (CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))) ≈
        CReal.abs (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)) :=
      CReal.abs_neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n))
    have habs_eq : CReal.abs
        (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)) ≈
        CReal.neg (CReal.sub (thm36B1_leftLimitReprC (s := s) hab).limit (s n)) :=
      Setoid.trans (Setoid.symm h2) h1
    exact regularSeqLtProp_of_right_eventual (Setoid.symm habs_eq) h0neg

/-- Data form of a point inside `(a,b)` apart from a prescribed sequence. -/
structure Thm36B1ApartPointDataC
    (s : Nat -> CReal) (a b : CReal) (hab : regularSeqLtProp a b) where
  t : CReal
  a_lt : regularSeqLtProp a t
  lt_b : regularSeqLtProp t b
  apart : forall n : Nat, regularSeqLtProp CReal.zero (CReal.abs (CReal.sub t (s n)))

/-- Canonical apart point obtained from the nested CReal interval construction. -/
noncomputable def thm36B1_apartPointDataC
    (s : Nat -> CReal) {a b : CReal} (hab : regularSeqLtProp a b) :
    Thm36B1ApartPointDataC s a b hab where
  t := (thm36B1_leftLimitReprC (s := s) hab).limit
  a_lt := (thm36B1_limit_strict_boundsC (s := s) hab).1
  lt_b := (thm36B1_limit_strict_boundsC (s := s) hab).2
  apart := thm36B1_limit_apartC (s := s) hab

/-- Smooth point data in any positive interval, obtained by countably avoiding
the profile exception sequence. -/
noncomputable def thm36B_smoothPointDataC_construct {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) {a b : CReal}
    (hab : regularSeqLtProp a b) (ha : PosEventuallyData a) :
    Thm36BSmoothPointDataC h a b hab ha := by
  let A := thm36B1_apartPointDataC (thm36ExceptionSeqC h hab ha) hab
  exact thm36B_smoothPointData_of_apartC h hab ha A.t A.a_lt A.lt_b A.apart

/-- Dyadic smooth level data constructed internally from the exception
sequence, without an external smoothness selector. -/
noncomputable def lemma43DyadicSmoothDataC_construct {X : Type*} {S : IntSpaceC X}
    (h : IntegrableRepC3 S) : Lemma43DyadicSmoothDataC h where
  smooth := fun n =>
    thm36B_smoothPointDataC_construct h
      (regularSeqLtProp_halfPow_succ n)
      (posEventuallyData_halfPowC (n + 1))

end BishopSec3P
