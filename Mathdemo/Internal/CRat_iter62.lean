import Mathdemo.Internal.CRat_iter61

/-!
# Quotient multiplication preserves nonnegativity

`CRat_iter61` closed `abs_le_of`.  This file closes the next order field:

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

/-- Basic quotient `COFO` fields through `mul_nonneg`. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldData cof where
  mul_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ {a b : CRealQuot}, ¬ COF.lt a 0 → ¬ COF.lt b 0 → ¬ COF.lt (a * b) 0

/-- Data-order/representative branch package including `mul_nonneg`. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderMulNonnegFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinArchAbsOrderFieldDataWith
      A rep ltDataOf
  mul_nonneg := by
    intro a b ha hb
    change ¬ ltQuot (mulQuotConcreteWith A a b) zeroQuot
    exact mul_nonnegQuotConcreteWith A ha hb

/-- Frontier after quotient `mul_nonneg` is closed. -/
structure CRealQuotCOFOAfterMulNonnegFrontier : Type where
  mul_archimedean : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterMulNonnegFrontier :
    CRealQuotCOFOAfterMulNonnegFrontier where
  mul_archimedean := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

