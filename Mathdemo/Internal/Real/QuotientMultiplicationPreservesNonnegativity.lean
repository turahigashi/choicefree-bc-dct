import Mathdemo.Internal.Real.QuotientAbsoluteValueUpperBound

/-!
# Quotient multiplication preserves nonnegativity

`QuotientAbsoluteValueUpperBound` closed `abs_le_of`.  This file closes the next order field:

* if `a` and `b` are nonnegative, then `a*b` is nonnegative.

The proof is intentionally quotient-level.  Nonnegativity gives `|a| = a` and
`|b| = b`; the already proved multiplication law gives `|a*b| = a*b`.  A
hypothetical strict negativity of `a*b` would also give `|a*b| = -(a*b)`,
forcing `a*b = -(a*b)` and hence both `0 < a*b` and `a*b < 0`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Concrete quotient multiplication preserves nonnegativity. -/
theorem mul_nonnegQuotConcreteWith
    (A : ScalarMulArchimedeanData) {a b : CRealQuot}
    (ha : ¬ ltQuot a zeroQuot) (hb : ¬ ltQuot b zeroQuot) :
    ¬ ltQuot (mulQuotConcreteWith A a b) zeroQuot := by
  intro hneg
  let z : CRealQuot := mulQuotConcreteWith A a b
  have habs_prod : absQuot z = z := by
    unfold z
    rw [abs_mulQuotConcreteWith A a b,
      absQuot_of_nonneg a ha,
      absQuot_of_nonneg b hb]
  have habs_neg : absQuot z = negQuot z :=
    absQuot_eq_neg_of_lt_zero hneg
  have hz_eq_neg : z = negQuot z := by
    rw [habs_prod] at habs_neg
    exact habs_neg
  have hpos_neg : ltQuot zeroQuot (negQuot z) :=
    ltQuot_zero_neg_of_lt_zero hneg
  have hpos_z : ltQuot zeroQuot z := by
    rwa [← hz_eq_neg] at hpos_neg
  exact ltQuot_irrefl zeroQuot
    (ltQuot_trans zeroQuot z zeroQuot hpos_z hneg)





end BishopCReal

