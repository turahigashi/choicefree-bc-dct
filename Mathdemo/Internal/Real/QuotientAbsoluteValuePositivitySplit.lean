import Mathdemo.Internal.Real.FirstQuotientAbsoluteOrderBounds

/-!
# Quotient absolute-value positivity split

`FirstQuotientAbsoluteOrderBounds` closed the unary absolute-value order bounds.  This file closes
the next local `COFO` field that can still be proved at the representative
level:

* `0 < |c| -> 0 < c or c < 0`.

The scalar proof keeps the original dyadic lower bound.  From
`eps k < |a|`, scalar absolute-value positivity gives a sign split; the sign
then rewrites `|a|` to either `a` or `-a`.  The representative proof takes one
sufficiently late tail point and re-extends it with the existing
`posEventually_of_late_point` lemma.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar helper: a dyadic positive lower bound below `|a|` splits into a
directed lower bound below `a` or `-a`. -/
theorem scalar_eps_lt_abs_split_lower {a : Scalar} {k : Nat}
    (h : COF.lt (eps k) (COF.abs a)) :
    COF.lt (eps k) a ∨ COF.lt (eps k) (-a) := by
  have hzero_abs : COF.lt (0 : Scalar) (COF.abs a) :=
    scalarCOFOSeed.lt_trans (eps_pos k) h
  rcases scalarCOFOSeed.lt_or_lt_of_abs_pos hzero_abs with hpos | hneg
  · left
    have hnotneg : ¬ COF.lt a 0 := by
      intro ha0
      exact COF.lt_irrefl (0 : Scalar) (scalarCOFOSeed.lt_trans hpos ha0)
    change BishopCRat.CRat.lt (eps k) (BishopCRat.CRat.absF a) at h
    rw [scalarCOFOSeed.abs_of_nonneg hnotneg] at h
    exact h
  · right
    have hnotneg_neg : ¬ COF.lt (-a) 0 := by
      intro hna0
      have h0a : COF.lt (0 : Scalar) a := by
        have t := COF.lt_add_left a hna0
        rwa [show a + -a = (0 : Scalar) from by ring,
          show a + (0 : Scalar) = a from by ring] at t
      exact COF.lt_irrefl (0 : Scalar) (scalarCOFOSeed.lt_trans h0a hneg)
    change BishopCRat.CRat.lt (eps k) (BishopCRat.CRat.absF a) at h
    rw [← scalarCOFOSeed.abs_neg a, scalarCOFOSeed.abs_of_nonneg hnotneg_neg] at h
    exact h

/-- Representative form of `0 < |x| -> 0 < x or x < 0`. -/
theorem ltQuot_zero_abs_split_mk (x : RegularSeq) :
    ltQuot zeroQuot (absQuot (mkQuot x)) →
      ltQuot zeroQuot (mkQuot x) ∨ ltQuot (mkQuot x) zeroQuot := by
  change PosEventually (subSeq (absSeq x) zeroSeq) →
    PosEventually (subSeq x zeroSeq) ∨ PosEventually (subSeq zeroSeq x)
  intro h
  rcases h with ⟨k, N, hN⟩
  let M : Nat := N + (k + 3)
  have hNM : N ≤ M := by
    unfold M
    omega
  have hMlate : k + 2 ≤ M := by
    unfold M
    omega
  have habs := hN M hNM
  change COF.lt (eps k) (COF.abs (x.val (M + 1)) - 0) at habs
  have habs' : COF.lt (eps k) (COF.abs (x.val (M + 1))) := by
    rwa [sub_zero] at habs
  rcases scalar_eps_lt_abs_split_lower habs' with hxpos | hxneg
  · left
    have hpos_point : COF.lt (eps k) ((subSeq x zeroSeq).val M) := by
      change COF.lt (eps k) (x.val (M + 1) - 0)
      rwa [sub_zero]
    exact posEventually_of_late_point (subSeq x zeroSeq) hMlate hpos_point
  · right
    have hpos_point : COF.lt (eps k) ((subSeq zeroSeq x).val M) := by
      change COF.lt (eps k) (0 - x.val (M + 1))
      rwa [zero_sub]
    exact posEventually_of_late_point (subSeq zeroSeq x) hMlate hpos_point

/-- Quotient-level `0 < |c| -> 0 < c or c < 0`. -/
theorem ltQuot_zero_abs_split (c : CRealQuot) :
    ltQuot zeroQuot (absQuot c) → ltQuot zeroQuot c ∨ ltQuot c zeroQuot := by
  refine Quotient.inductionOn c ?_
  intro x
  exact ltQuot_zero_abs_split_mk x






end BishopCReal

