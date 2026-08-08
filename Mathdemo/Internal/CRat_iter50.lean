import Mathdemo.Internal.CRat_iter49

/-!
# First concrete CReal quotient COFO fields

`CRat_iter49` isolated the full `COFO` field data needed after a quotient
`COF` record is available.  This file starts filling that field data with
actual quotient-level proofs that are already local:

* `abs 0 = 0`;
* `abs (-x) = abs x`;
* `0 < 1`;
* `0 < half`.

The remaining `COFO` obligations are still not claimed here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Quotient-level absolute value sends zero to zero. -/
theorem absQuot_zero : absQuot zeroQuot = zeroQuot := by
  change mkQuot (absSeq zeroSeq) = mkQuot zeroSeq
  exact Quotient.sound (rel_to_relEventually (absSeq zeroSeq) zeroSeq abs_zero_raw)

/-- Quotient-level absolute value is invariant under negation. -/
theorem absQuot_neg (x : CRealQuot) : absQuot (negQuot x) = absQuot x := by
  refine Quotient.inductionOn x ?_
  intro a
  change mkQuot (absSeq (negSeq a)) = mkQuot (absSeq a)
  exact Quotient.sound
    (rel_to_relEventually (absSeq (negSeq a)) (absSeq a) (abs_neg_raw a))

/-- Quotient order sees the constant one as positive. -/
theorem ltQuot_zero_one : ltQuot zeroQuot oneQuot := by
  change PosEventually (subSeq oneSeq zeroSeq)
  rcases one_pos_raw with ⟨k, hk⟩
  refine ⟨k, 0, ?_⟩
  intro n _hn
  change COF.lt (eps k) ((1 : Scalar) - 0)
  rwa [sub_zero]

/-- Quotient order sees the constant half as positive. -/
theorem ltQuot_zero_half : ltQuot zeroQuot halfQuot := by
  change PosEventually (subSeq halfSeq zeroSeq)
  rcases half_pos_raw with ⟨k, hk⟩
  refine ⟨k, 0, ?_⟩
  intro n _hn
  change COF.lt (eps k) ((COF.half : Scalar) - 0)
  rwa [sub_zero]

/-- The first quotient `COFO` fields that have now been concretely supplied.
This is intentionally a smaller seed than `CRealQuotCOFOFieldData`: it records
only the closed local fields and leaves the remaining analytic/order fields
outside the record. -/
structure CRealQuotCOFOBasicFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 where
  abs_zero :
    letI : BishopC.COF CRealQuot := cof
    COF.abs (0 : CRealQuot) = 0
  abs_neg :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, COF.abs (-a) = COF.abs a
  one_pos :
    letI : BishopC.COF CRealQuot := cof
    COF.lt (0 : CRealQuot) 1
  half_pos :
    letI : BishopC.COF CRealQuot := cof
    COF.lt (0 : CRealQuot) COF.half

/-- Basic `COFO` fields for the data-order/representative COF fork. -/
def cRealQuotCOFOBasicFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  abs_zero := by
    change absQuot zeroQuot = zeroQuot
    exact absQuot_zero
  abs_neg := by
    intro a
    change absQuot (negQuot a) = absQuot a
    exact absQuot_neg a
  one_pos := by
    change ltQuot zeroQuot oneQuot
    exact ltQuot_zero_one
  half_pos := by
    change ltQuot zeroQuot halfQuot
    exact ltQuot_zero_half

/-- Basic `COFO` fields for the decidable strict-order COF fork. -/
def cRealQuotCOFOBasicFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  abs_zero := by
    change absQuot zeroQuot = zeroQuot
    exact absQuot_zero
  abs_neg := by
    intro a
    change absQuot (negQuot a) = absQuot a
    exact absQuot_neg a
  one_pos := by
    change ltQuot zeroQuot oneQuot
    exact ltQuot_zero_one
  half_pos := by
    change ltQuot zeroQuot halfQuot
    exact ltQuot_zero_half

/-- Frontier after the first four quotient `COFO` fields have been closed. -/
structure CRealQuotCOFOAfterBasicFieldsFrontier : Type where
  lt_trans : Prop
  abs_order_bounds : Prop
  abs_add_mul_laws : Prop
  archimedean_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterBasicFieldsFrontier :
    CRealQuotCOFOAfterBasicFieldsFrontier where
  lt_trans := True
  abs_order_bounds := True
  abs_add_mul_laws := True
  archimedean_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

