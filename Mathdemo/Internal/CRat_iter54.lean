import Mathdemo.Internal.CRat_iter53

/-!
# Quotient triangle inequality field

`CRat_iter53` closed the absolute-value positivity split.  This file closes
the next local `COFO` field:

* `¬ (|x| + |y| < |x + y|)`.

The proof is again representative-level.  A hypothetical eventual positive
gap `|x+y| - (|x|+|y|)` gives one scalar point where the reverse strict
triangle inequality holds, contradicting the audited scalar triangle
inequality `scalar_abs_add_le`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative form of the triangle inequality as a no-strict-reverse law. -/
theorem not_posEventually_abs_add_reverse (x y : RegularSeq) :
    ¬ PosEventually
      (subSeq (absSeq (addSeq x y)) (addSeq (absSeq x) (absSeq y))) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  change COF.lt (eps k)
    (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)) -
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))))
    at hpoint
  have hzero : COF.lt (0 : Scalar)
    (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)) -
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1)))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint
  have hbad : COF.lt
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1)))
      (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1))) := by
    have t := COF.lt_add_left
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1)))
      hzero
    rwa [show
        (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))) +
            (0 : Scalar) =
          COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))
        from by ring,
      show
        (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))) +
            (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)) -
              (COF.abs (x.val ((N + 1) + 1)) +
                COF.abs (y.val ((N + 1) + 1)))) =
          COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1))
        from by ring] at t
  have htri : Le
      (COF.abs (x.val ((N + 1) + 1) + y.val ((N + 1) + 1)))
      (COF.abs (x.val ((N + 1) + 1)) + COF.abs (y.val ((N + 1) + 1))) :=
    scalar_abs_add_le (x.val ((N + 1) + 1)) (y.val ((N + 1) + 1))
  exact htri hbad

/-- Quotient-level `¬ (|x| + |y| < |x+y|)`. -/
theorem abs_add_leQuot (x y : CRealQuot) :
    ¬ ltQuot (addQuot (absQuot x) (absQuot y)) (absQuot (addQuot x y)) := by
  refine Quotient.inductionOn x ?_
  intro xr
  refine Quotient.inductionOn y ?_
  intro yr
  change ¬ PosEventually
    (subSeq (absSeq (addSeq xr yr)) (addSeq (absSeq xr) (absSeq yr)))
  exact not_posEventually_abs_add_reverse xr yr

/-- Basic quotient `COFO` fields through the triangle inequality field. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitFieldData cof where
  abs_add_le :
    letI : BishopC.COF CRealQuot := cof
    ∀ a b : CRealQuot, ¬ COF.lt (COF.abs a + COF.abs b) (COF.abs (a + b))

/-- Data-order/representative branch package including the triangle
inequality field. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitFieldData :=
    cRealQuotCOFOBasicTransAbsSplitFieldDataWith A rep ltDataOf
  abs_add_le := by
    intro a b
    change ¬ ltQuot (addQuot (absQuot a) (absQuot b)) (absQuot (addQuot a b))
    exact abs_add_leQuot a b

/-- Decidable-order branch package including the triangle inequality field. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitFieldData :=
    cRealQuotCOFOBasicTransAbsSplitFieldDataWithDecidableLT A hdec
  abs_add_le := by
    intro a b
    change ¬ ltQuot (addQuot (absQuot a) (absQuot b)) (absQuot (addQuot a b))
    exact abs_add_leQuot a b

/-- Frontier after the triangle inequality field is closed. -/
structure CRealQuotCOFOAfterTriangleFrontier : Type where
  abs_le_of : Prop
  abs_mul_laws : Prop
  archimedean_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterTriangleFrontier :
    CRealQuotCOFOAfterTriangleFrontier where
  abs_le_of := True
  abs_mul_laws := True
  archimedean_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

