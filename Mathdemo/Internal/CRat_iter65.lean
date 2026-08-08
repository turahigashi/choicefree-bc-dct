import Mathdemo.Internal.CRat_iter64

/-!
# COFO assembly from positive-inverse data

`CRat_iter64` closes all non-inverse `COFO` fields for the conditional
quotient branch.  This file does not construct the inverse itself.  Instead it
isolates the exact positive-inverse data still needed and proves that, once
that data is supplied, the existing field chain assembles into a live
`BishopC.COFO CRealQuot` record.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The exact positive-inverse block still required by `BishopC.COFO`. -/
structure CRealQuotPositiveInverseFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 where
  inv : CRealQuot → CRealQuot
  mul_inv_cancel :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, COF.lt 0 x → x * inv x = 1
  inv_pos :
    letI : BishopC.COF CRealQuot := cof
    ∀ {x : CRealQuot}, COF.lt 0 x → COF.lt 0 (inv x)

/-- Full quotient `COFO` field data, conditional only on the positive-inverse
block. -/
def cRealQuotCOFOFieldDataWithPositiveInverse
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (pinv : CRealQuotPositiveInverseFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf)) :
    CRealQuotCOFOFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) := by
  let base := cRealQuotCOFOAfterEqSmallFieldDataWith A rep ltDataOf
  exact {
    lt_trans := base.lt_trans
    abs_zero := base.abs_zero
    abs_neg := base.abs_neg
    neg_le_abs := base.neg_le_abs
    le_abs_self := base.le_abs_self
    abs_le_of := base.abs_le_of
    one_pos := base.one_pos
    half_pos := base.half_pos
    mul_pos := base.mul_pos
    archimedean := base.archimedean
    archimedean_pos := base.archimedean_pos
    abs_add_le := base.abs_add_le
    eq_of_small := base.eq_of_small
    abs_of_nonneg := base.abs_of_nonneg
    max_zero_nonneg := base.max_zero_nonneg
    max_le_abs := base.max_le_abs
    neg_min_zero_nonneg := base.neg_min_zero_nonneg
    neg_min_le_abs := base.neg_min_le_abs
    lt_or_lt_of_abs_pos := base.lt_or_lt_of_abs_pos
    abs_mul := base.abs_mul
    mul_nonneg := base.mul_nonneg
    mul_archimedean := base.mul_archimedean
    inv := pinv.inv
    mul_inv_cancel := pinv.mul_inv_cancel
    inv_pos := pinv.inv_pos
  }

/-- A live quotient `COFO` record once positive-inverse data is supplied. -/
@[reducible] def cRealQuotCOFOWithPositiveInverse
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b)
    (pinv : CRealQuotPositiveInverseFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf)) :
    BishopC.COFO CRealQuot :=
  cRealQuotCOFOConditionalWith A rep ltDataOf
    (cRealQuotCOFOFieldDataWithPositiveInverse A rep ltDataOf pinv)

/-- Frontier after the positive-inverse block has been isolated. -/
structure CRealQuotCOFOAfterPositiveInverseDataFrontier : Type where
  construct_positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterPositiveInverseDataFrontier :
    CRealQuotCOFOAfterPositiveInverseDataFrontier where
  construct_positive_inverse := True
  cauchy_completeness := True

end BishopCReal

