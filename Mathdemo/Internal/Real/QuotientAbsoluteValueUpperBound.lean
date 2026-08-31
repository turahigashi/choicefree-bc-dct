import Mathdemo.Internal.Real.QuotientAbsoluteValueNonnegativeElements

/-!
# Quotient absolute-value upper bound

`QuotientAbsoluteValueNonnegativeElements` closed `abs_of_nonneg`.  This file closes the companion order
field:

* if `b <= a` and `b <= -a`, then `b <= |a|`.

The quotient proof stays at the order layer.  A hypothetical `b < |a|` is
split by cotransitivity at `a`.  The direct branch contradicts `b <= a`; the
other branch gives `a < |a|`, which forces `a < 0` using `abs_of_nonneg`, and
therefore `|a| = -a`, contradicting `b <= -a`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- If `a < 0`, then `0 < -a` at quotient level. -/
theorem ltQuot_zero_neg_of_lt_zero {a : CRealQuot}
    (ha : ltQuot a zeroQuot) : ltQuot zeroQuot (negQuot a) := by
  revert ha
  refine Quotient.inductionOn a ?_
  intro ar ha
  change PosEventually (subSeq zeroSeq ar) at ha
  change PosEventually (subSeq (negSeq ar) zeroSeq)
  rcases ha with ⟨k, N, hN⟩
  refine ⟨k, N, ?_⟩
  intro n hn
  have h := hN n hn
  change COF.lt (eps k) (0 - ar.val (n + 1)) at h
  change COF.lt (eps k) (-ar.val (n + 1) - 0)
  rw [zero_sub] at h
  simpa [sub_zero] using h

/-- A strictly negative quotient has absolute value equal to its negation. -/
theorem absQuot_eq_neg_of_lt_zero {a : CRealQuot}
    (ha : ltQuot a zeroQuot) : absQuot a = negQuot a := by
  have hpos_neg : ltQuot zeroQuot (negQuot a) :=
    ltQuot_zero_neg_of_lt_zero ha
  have hnonneg_neg : ¬ ltQuot (negQuot a) zeroQuot := by
    intro hneg
    exact ltQuot_irrefl zeroQuot
      (ltQuot_trans zeroQuot (negQuot a) zeroQuot hpos_neg hneg)
  have h := absQuot_of_nonneg (negQuot a) hnonneg_neg
  rw [absQuot_neg a] at h
  exact h

/-- If `a < |a|`, then `a < 0`.

The only nonnegative alternative would rewrite `|a|` to `a`, contradicting
irreflexivity. -/
theorem ltQuot_self_abs_implies_lt_zero {a : CRealQuot}
    (ha_abs : ltQuot a (absQuot a)) : ltQuot a zeroQuot := by
  rcases ltQuot_cotrans a (absQuot a) zeroQuot ha_abs with ha0 | h0abs
  · exact ha0
  · rcases ltQuot_zero_abs_split a h0abs with h0a | ha0
    · have hnotneg : ¬ ltQuot a zeroQuot := by
        intro ha0
        exact ltQuot_irrefl zeroQuot
          (ltQuot_trans zeroQuot a zeroQuot h0a ha0)
      have habs : absQuot a = a := absQuot_of_nonneg a hnotneg
      rw [habs] at ha_abs
      exact False.elim (ltQuot_irrefl a ha_abs)
    · exact ha0

/-- Quotient-level `abs_le_of`: from `b <= a` and `b <= -a`, derive
`b <= |a|`. -/
theorem absQuot_le_of {a b : CRealQuot}
    (ha : ¬ ltQuot b a) (hna : ¬ ltQuot b (negQuot a)) :
    ¬ ltQuot b (absQuot a) := by
  intro hbabs
  rcases ltQuot_cotrans b (absQuot a) a hbabs with hba | haabs
  · exact ha hba
  · have ha0 : ltQuot a zeroQuot :=
      ltQuot_self_abs_implies_lt_zero haabs
    have habs_neg : absQuot a = negQuot a :=
      absQuot_eq_neg_of_lt_zero ha0
    rw [habs_neg] at hbabs
    exact hna hbabs





end BishopCReal

