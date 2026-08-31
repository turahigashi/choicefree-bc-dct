import Mathdemo.Internal.Real.CRealQuotientStrictOrderTransitivity

/-!
# First quotient absolute-order bounds

`CRealQuotientStrictOrderTransitivity` closed strict-order transitivity.  This file closes the two
unary absolute-value order bounds in the live `COFO` interface:

* `¬ abs x < -x`;
* `¬ abs x < x`.

Both arguments reduce to a single late tail witness.  If the forbidden
quotient inequality held eventually, then at one late index the scalar
inequality would contradict the audited scalar absolute-value bounds.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative form of `¬ |x| < -x`. -/
theorem not_posEventually_sub_neg_abs (x : RegularSeq) :
    ¬ PosEventually (subSeq (negSeq x) (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  change COF.lt (eps k) ((-x.val (N + 1)) - COF.abs (x.val (N + 1))) at hpoint
  have hzero :
      COF.lt (0 : Scalar) ((-x.val (N + 1)) - COF.abs (x.val (N + 1))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint
  have hbad : COF.lt (COF.abs (x.val (N + 1))) (-x.val (N + 1)) := by
    have t := COF.lt_add_left (COF.abs (x.val (N + 1))) hzero
    rwa [show COF.abs (x.val (N + 1)) + (0 : Scalar) =
          COF.abs (x.val (N + 1)) from by ring,
      show COF.abs (x.val (N + 1)) +
            ((-x.val (N + 1)) - COF.abs (x.val (N + 1))) =
          -x.val (N + 1) from by ring] at t
  exact scalarCOFOSeed.neg_le_abs (x.val (N + 1)) hbad

/-- Representative form of `¬ |x| < x`. -/
theorem not_posEventually_sub_self_abs (x : RegularSeq) :
    ¬ PosEventually (subSeq x (absSeq x)) := by
  intro h
  rcases h with ⟨k, N, hN⟩
  have hpoint := hN N (Nat.le_refl N)
  change COF.lt (eps k) (x.val (N + 1) - COF.abs (x.val (N + 1))) at hpoint
  have hzero :
      COF.lt (0 : Scalar) (x.val (N + 1) - COF.abs (x.val (N + 1))) :=
    scalarCOFOSeed.lt_trans (eps_pos k) hpoint
  have hbad : COF.lt (COF.abs (x.val (N + 1))) (x.val (N + 1)) := by
    have t := COF.lt_add_left (COF.abs (x.val (N + 1))) hzero
    rwa [show COF.abs (x.val (N + 1)) + (0 : Scalar) =
          COF.abs (x.val (N + 1)) from by ring,
      show COF.abs (x.val (N + 1)) +
            (x.val (N + 1) - COF.abs (x.val (N + 1))) =
          x.val (N + 1) from by ring] at t
  exact scalarCOFOSeed.le_abs_self (x.val (N + 1)) hbad

/-- Quotient-level `¬ |x| < -x`. -/
theorem neg_le_absQuot (x : CRealQuot) : ¬ ltQuot (absQuot x) (negQuot x) := by
  refine Quotient.inductionOn x ?_
  intro xr
  change ¬ PosEventually (subSeq (negSeq xr) (absSeq xr))
  exact not_posEventually_sub_neg_abs xr

/-- Quotient-level `¬ |x| < x`. -/
theorem le_abs_selfQuot (x : CRealQuot) : ¬ ltQuot (absQuot x) x := by
  refine Quotient.inductionOn x ?_
  intro xr
  change ¬ PosEventually (subSeq xr (absSeq xr))
  exact not_posEventually_sub_self_abs xr

/-- Basic quotient `COFO` fields, transitivity, and the two unary absolute
order bounds. -/
structure CRealQuotCOFOBasicTransAbsFieldData
    (cof : BishopC.COF CRealQuot) : Type 1 extends
    CRealQuotCOFOBasicAndTransFieldData cof where
  neg_le_abs :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.abs a) (-a)
  le_abs_self :
    letI : BishopC.COF CRealQuot := cof
    ∀ a : CRealQuot, ¬ COF.lt (COF.abs a) a

/-- Data-order/representative branch package for the closed unary absolute
order fields. -/
def cRealQuotCOFOBasicTransAbsFieldDataWith
    (A : ScalarMulArchimedeanData)
    (rep : ∀ x : CRealQuot, CRealQuotRepWitness x)
    (ltDataOf : ∀ {a b : CRealQuot}, ltQuot a b → ltQuotData a b) :
    CRealQuotCOFOBasicTransAbsFieldData
      (cRealQuotCOFConditionalWith A rep ltDataOf) where
  toCRealQuotCOFOBasicAndTransFieldData :=
    cRealQuotCOFOBasicAndTransFieldDataWith A rep ltDataOf
  neg_le_abs := by
    intro a
    change ¬ ltQuot (absQuot a) (negQuot a)
    exact neg_le_absQuot a
  le_abs_self := by
    intro a
    change ¬ ltQuot (absQuot a) a
    exact le_abs_selfQuot a

/-- Decidable-order branch package for the closed unary absolute order fields. -/
def cRealQuotCOFOBasicTransAbsFieldDataWithDecidableLT
    (A : ScalarMulArchimedeanData)
    (hdec : CRealQuotLTDecidable) :
    CRealQuotCOFOBasicTransAbsFieldData
      (cRealQuotCOFConditionalWithDecidableLT A hdec) where
  toCRealQuotCOFOBasicAndTransFieldData :=
    cRealQuotCOFOBasicAndTransFieldDataWithDecidableLT A hdec
  neg_le_abs := by
    intro a
    change ¬ ltQuot (absQuot a) (negQuot a)
    exact neg_le_absQuot a
  le_abs_self := by
    intro a
    change ¬ ltQuot (absQuot a) a
    exact le_abs_selfQuot a

/-- Frontier after strict-order transitivity and the two unary absolute order
bounds are closed. -/
structure CRealQuotCOFOAfterUnaryAbsFrontier : Type where
  abs_le_of : Prop
  abs_add_mul_laws : Prop
  archimedean_laws : Prop
  positive_inverse : Prop
  cauchy_completeness : Prop

def cRealQuotCOFOAfterUnaryAbsFrontier :
    CRealQuotCOFOAfterUnaryAbsFrontier where
  abs_le_of := True
  abs_add_mul_laws := True
  archimedean_laws := True
  positive_inverse := True
  cauchy_completeness := True

end BishopCReal

