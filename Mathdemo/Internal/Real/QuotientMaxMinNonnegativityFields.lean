import Mathdemo.Internal.Real.QuotientMultiplicationPositivity

/-!
# Quotient max/min nonnegativity fields

`QuotientMultiplicationPositivity` closed multiplication positivity.  This file closes the first two
max/min fields in the live `COFO` interface:

* `max x 0` is nonnegative;
* `-min x 0` is nonnegative.

The quotient definitions of max and min are the COF half-sum expressions.  A
hypothetical strict negative tail therefore gives one scalar sample where a
half-sum is strictly negative.  The scalar contradiction uses only the audited
absolute-value order bounds and multiplication nonnegativity.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar helper: `a + |a|` is nonnegative. -/
theorem scalar_add_abs_nonneg (a : Scalar) : Le 0 (a + COF.abs a) := by
  intro h
  have hbad : COF.lt (COF.abs a) (-a) := by
    have t := COF.lt_add_left (-a) h
    rwa [show -a + (a + COF.abs a) = COF.abs a from by ring,
      show -a + (0 : Scalar) = -a from by ring] at t
  exact scalarCOFOSeed.neg_le_abs a hbad

/-- Scalar helper: `|a| - a` is nonnegative. -/
theorem scalar_abs_sub_self_nonneg (a : Scalar) : Le 0 (COF.abs a - a) := by
  intro h
  have hbad : COF.lt (COF.abs a) a := by
    have t := COF.lt_add_left a h
    rwa [show a + (COF.abs a - a) = COF.abs a from by ring,
      show a + (0 : Scalar) = a from by ring] at t
  exact scalarCOFOSeed.le_abs_self a hbad

/-- Scalar half-sum form of `max a 0` is nonnegative. -/
theorem scalar_half_mul_add_abs_nonneg (a : Scalar) :
    Le 0 ((COF.half : Scalar) * (a + COF.abs a)) := by
  exact scalarCOFOSeed.mul_nonneg
    (scalar_nonneg_of_pos scalarCOFOSeed.half_pos)
    (scalar_add_abs_nonneg a)

/-- Scalar half-sum form of `-min a 0` is nonnegative. -/
theorem scalar_half_mul_abs_sub_nonneg (a : Scalar) :
    Le 0 ((COF.half : Scalar) * (COF.abs a - a)) := by
  exact scalarCOFOSeed.mul_nonneg
    (scalar_nonneg_of_pos scalarCOFOSeed.half_pos)
    (scalar_abs_sub_self_nonneg a)

/-- Representative form of `max x 0 >= 0`. -/
theorem not_posEventually_zero_sub_max_with
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    ¬ PosEventually
      (subSeq zeroSeq
        (mulSeqConcreteWith A halfSeq
          (addSeq (addSeq x zeroSeq)
            (absSeq (addSeq x (negSeq zeroSeq)))))) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  set K : Nat := mulBoundWith A halfSeq
    (addSeq (addSeq x zeroSeq) (absSeq (addSeq x (negSeq zeroSeq)))) with hKdef
  set m : Nat := mulIndexFromBound K (N + 1) with hmdef
  have hpoint' : COF.lt (eps k)
      (0 - ((COF.half : Scalar) *
        (x.val (m + 2) + COF.abs (x.val (m + 2))))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      mulSeqConcreteWith, mulSeqWith, boundedMulValWith, mulValWithBound,
      halfSeq, halfVal, addSeq, addVal, addIndex, absSeq, absVal, negSeq,
      negVal, hKdef, hmdef, zero_add, add_zero] using hpoint
  have hzero : COF.lt (0 : Scalar)
      (0 - ((COF.half : Scalar) *
        (x.val (m + 2) + COF.abs (x.val (m + 2))))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint'
  have hbad : COF.lt
      ((COF.half : Scalar) * (x.val (m + 2) + COF.abs (x.val (m + 2)))) 0 := by
    have t := COF.lt_add_left
      ((COF.half : Scalar) * (x.val (m + 2) + COF.abs (x.val (m + 2)))) hzero
    rwa [show
        ((COF.half : Scalar) * (x.val (m + 2) + COF.abs (x.val (m + 2)))) + 0 =
          ((COF.half : Scalar) * (x.val (m + 2) + COF.abs (x.val (m + 2))))
        from by ring,
      show
        ((COF.half : Scalar) * (x.val (m + 2) + COF.abs (x.val (m + 2)))) +
            (0 - ((COF.half : Scalar) *
              (x.val (m + 2) + COF.abs (x.val (m + 2))))) =
          0
        from by ring] at t
  exact scalar_half_mul_add_abs_nonneg (x.val (m + 2)) hbad

/-- Representative form of `-min x 0 >= 0`. -/
theorem not_posEventually_min_positive_with
    (A : ScalarMulArchimedeanData) (x : RegularSeq) :
    ¬ PosEventually
      (subSeq zeroSeq
        (negSeq
          (mulSeqConcreteWith A halfSeq
            (addSeq (addSeq x zeroSeq)
              (negSeq (absSeq (addSeq x (negSeq zeroSeq)))))))) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  set K : Nat := mulBoundWith A halfSeq
    (addSeq (addSeq x zeroSeq)
      (negSeq (absSeq (addSeq x (negSeq zeroSeq))))) with hKdef
  set m : Nat := mulIndexFromBound K (N + 1) with hmdef
  have hpoint' : COF.lt (eps k)
      ((COF.half : Scalar) *
        (x.val (m + 2) - COF.abs (x.val (m + 2)))) := by
    simpa [subSeq, subVal, zeroSeq, constSeq, zeroVal, constVal,
      mulSeqConcreteWith, mulSeqWith, boundedMulValWith, mulValWithBound,
      halfSeq, halfVal, addSeq, addVal, addIndex, absSeq, absVal, negSeq,
      negVal, hKdef, hmdef, zero_add, add_zero, sub_eq_add_neg] using hpoint
  have hzero : COF.lt (0 : Scalar)
      ((COF.half : Scalar) *
        (x.val (m + 2) - COF.abs (x.val (m + 2)))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint'
  have hbad : COF.lt
      (-((COF.half : Scalar) *
        (x.val (m + 2) - COF.abs (x.val (m + 2))))) 0 := by
    have t := COF.lt_add_left
      (-((COF.half : Scalar) *
        (x.val (m + 2) - COF.abs (x.val (m + 2))))) hzero
    rwa [show
        -((COF.half : Scalar) *
          (x.val (m + 2) - COF.abs (x.val (m + 2)))) + 0 =
          -((COF.half : Scalar) *
            (x.val (m + 2) - COF.abs (x.val (m + 2))))
        from by ring,
      show
        -((COF.half : Scalar) *
          (x.val (m + 2) - COF.abs (x.val (m + 2)))) +
            ((COF.half : Scalar) *
              (x.val (m + 2) - COF.abs (x.val (m + 2)))) =
          0
        from by ring] at t
  have hbad' : COF.lt
      ((COF.half : Scalar) *
        (COF.abs (x.val (m + 2)) - x.val (m + 2))) 0 := by
    rwa [show
        -((COF.half : Scalar) *
          (x.val (m + 2) - COF.abs (x.val (m + 2)))) =
          (COF.half : Scalar) *
            (COF.abs (x.val (m + 2)) - x.val (m + 2))
        from by ring] at hbad
  exact scalar_half_mul_abs_sub_nonneg (x.val (m + 2)) hbad'

/-- Quotient-level `max x 0 >= 0`. -/
theorem maxQuotCOF_zero_nonneg_with
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    ¬ ltQuot (maxQuotCOFWith A x zeroQuot) zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro xr
  change ¬ PosEventually
      (subSeq zeroSeq
        (mulSeqConcreteWith A halfSeq
          (addSeq (addSeq xr zeroSeq)
            (absSeq (addSeq xr (negSeq zeroSeq))))))
  exact not_posEventually_zero_sub_max_with A xr

/-- Quotient-level `-min x 0 >= 0`. -/
theorem neg_minQuotCOF_zero_nonneg_with
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    ¬ ltQuot (negQuot (minQuotCOFWith A x zeroQuot)) zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro xr
  change ¬ PosEventually
      (subSeq zeroSeq
        (negSeq
          (mulSeqConcreteWith A halfSeq
            (addSeq (addSeq xr zeroSeq)
              (negSeq (absSeq (addSeq xr (negSeq zeroSeq))))))))
  exact not_posEventually_min_positive_with A xr

/-- Basic quotient `COFO` fields through the two max/min nonnegativity fields. -/
structure CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinNonnegFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldData cof where
  max_zero_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.max a 0) 0
  neg_min_zero_nonneg :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (- COF.min a 0) 0

/-- Data-order/representative branch package including max/min nonnegativity. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinNonnegFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinNonnegFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldDataWith A rep ltDataOf
  max_zero_nonneg := by
    intro a
    change ¬ ltQuot (maxQuotCOFWith A a zeroQuot) zeroQuot
    exact maxQuotCOF_zero_nonneg_with A a
  neg_min_zero_nonneg := by
    intro a
    change ¬ ltQuot (negQuot (minQuotCOFWith A a zeroQuot)) zeroQuot
    exact neg_minQuotCOF_zero_nonneg_with A a

/-- Decidable-order branch package including max/min nonnegativity. -/
def cRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinNonnegFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsSplitTriangleMulPosMaxMinNonnegFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldData :=
    cRealQuotCOFOBasicTransAbsSplitTriangleMulPosFieldDataWithDecidableLT A hdec
  max_zero_nonneg := by
    intro a
    change ¬ ltQuot (maxQuotCOFWith A a zeroQuot) zeroQuot
    exact maxQuotCOF_zero_nonneg_with A a
  neg_min_zero_nonneg := by
    intro a
    change ¬ ltQuot (negQuot (minQuotCOFWith A a zeroQuot)) zeroQuot
    exact neg_minQuotCOF_zero_nonneg_with A a

/-- Frontier after the nonnegativity half of the max/min fields is closed. -/
structure CRealQuotCOFOAfterMaxMinNonnegFrontier : Type where
  abs_le_of : Prop
  abs_of_nonneg : Prop
  max_min_le_abs : Prop
  mul_nonneg : Prop
  archimedean_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterMaxMinNonnegFrontier :
    CRealQuotCOFOAfterMaxMinNonnegFrontier where
  abs_le_of := True
  abs_of_nonneg := True
  max_min_le_abs := True
  mul_nonneg := True
  archimedean_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

