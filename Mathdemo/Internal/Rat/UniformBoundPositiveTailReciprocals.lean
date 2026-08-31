import Mathdemo.Internal.Real.BoundSensitiveReciprocalTailScaffold

/-!
# Uniform bound for positive tail reciprocals

`BoundSensitiveReciprocalTailScaffold` introduced the bound-sensitive reciprocal tail.  This file closes
the scalar order fact that justifies the Lipschitz constant used there:

if `0 < e < a`, then `1/a <= 1/e`.

Applied to a positive tail witness `eps h.k < x_n`, this gives a uniform bound
on every reciprocal sample.
-/

namespace BishopCRat

open BishopC

namespace Q

/-- Positive reciprocal reverses strict lower bounds at the raw rational layer:
if `0 < e < a`, then it is impossible that `1/e < 1/a`. -/
theorem not_posInvOrZero_lt_of_lt {e a : Q}
    (hepos : lt zero e) (hea : lt e a) :
    ¬ lt (posInvOrZero e) (posInvOrZero a) := by
  have hnumE : 0 < e.num := num_pos_of_pos hepos
  have hapos : lt zero a := lt_trans hepos hea
  have hnumA : 0 < a.num := num_pos_of_pos hapos
  unfold posInvOrZero
  rw [dif_pos hnumE, dif_pos hnumA]
  intro hlt
  unfold lt at hea hlt
  have hreverse : a.num * e.den < e.num * a.den := by
    calc
      a.num * e.den = e.den * a.num := by ring
      _ < a.den * e.num := hlt
      _ = e.num * a.den := by ring
  exact Int.lt_asymm hea hreverse

end Q

namespace CRat

/-- Positive reciprocal reverses strict lower bounds on quotient rationals. -/
theorem not_posInvOrZero_lt_of_lt (e a : CRat)
    (hepos : lt 0 e) (hea : lt e a) :
    ¬ lt (posInvOrZero e) (posInvOrZero a) := by
  induction e using Quotient.inductionOn with
  | h qe =>
      induction a using Quotient.inductionOn with
      | h qa =>
          exact Q.not_posInvOrZero_lt_of_lt hepos hea

end CRat
end BishopCRat

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar positive reciprocal is order-reversing under a strict positive lower
bound. -/
theorem scalar_posInv_le_of_lt (e a : Scalar)
    (hepos : COF.lt 0 e) (hea : COF.lt e a) :
    Le (scalarPositiveInverseSeed.inv a) (scalarPositiveInverseSeed.inv e) :=
  BishopCRat.CRat.not_posInvOrZero_lt_of_lt e a hepos hea

/-- The absolute value of a positive reciprocal is itself. -/
theorem scalar_abs_posInv_eq_self (a : Scalar) (ha : COF.lt 0 a) :
    COF.abs (scalarPositiveInverseSeed.inv a) =
      scalarPositiveInverseSeed.inv a :=
  scalarCOFOSeed.abs_of_nonneg
    (scalar_nonneg_of_pos (scalarPositiveInverseSeed.inv_pos a ha))

/-- Absolute-value version of reciprocal order reversal. -/
theorem scalar_abs_posInv_le_of_lt (e a : Scalar)
    (hepos : COF.lt 0 e) (hea : COF.lt e a) :
    Le (COF.abs (scalarPositiveInverseSeed.inv a))
      (COF.abs (scalarPositiveInverseSeed.inv e)) := by
  have hapos : COF.lt 0 a := scalarCOFOSeed.lt_trans hepos hea
  rw [scalar_abs_posInv_eq_self a hapos,
    scalar_abs_posInv_eq_self e hepos]
  exact scalar_posInv_le_of_lt e a hepos hea

/-- Tail reciprocal samples are uniformly bounded by the reciprocal of the
positive tail gauge. -/
theorem positiveTailInvVal_abs_le_lipschitzFactor
    (x : RegularSeq) (h : PosEventuallyData x) {n : Nat} (hn : h.N ≤ n) :
    Le (COF.abs (positiveTailInvVal x h n))
      (COF.abs (scalarPositiveInverseSeed.inv (eps h.k))) := by
  unfold positiveTailInvVal
  rw [if_pos hn]
  exact scalar_abs_posInv_le_of_lt (eps h.k) (x.val n)
    (eps_pos h.k) (h.tail_pos n hn)

/-- Bound-sensitive reciprocal samples inherit the same uniform bound. -/
theorem positiveTailInvValWithBound_abs_le_lipschitzFactor
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (n : Nat) :
    Le (COF.abs (positiveTailInvValWithBound A x h n))
      (COF.abs (scalarPositiveInverseSeed.inv (eps h.k))) :=
  positiveTailInvVal_abs_le_lipschitzFactor x h
    (reciprocalTailIndex_tail A x h n)

/-- The product of two bound-sensitive reciprocal samples is bounded by the
recorded reciprocal Lipschitz constant. -/
theorem positiveTailInvValWithBound_abs_mul_le_lipschitzBound
    (A : ScalarMulArchimedeanData) (x : RegularSeq)
    (h : PosEventuallyData x) (m n : Nat) :
    Le
      (COF.abs (positiveTailInvValWithBound A x h m) *
        COF.abs (positiveTailInvValWithBound A x h n))
      (COF.abs (positiveReciprocalLipschitzBound x h)) := by
  set L : Scalar := COF.abs (scalarPositiveInverseSeed.inv (eps h.k))
  have hm :
      Le (COF.abs (positiveTailInvValWithBound A x h m)) L := by
    simpa [L] using
      positiveTailInvValWithBound_abs_le_lipschitzFactor A x h m
  have hn :
      Le (COF.abs (positiveTailInvValWithBound A x h n)) L := by
    simpa [L] using
      positiveTailInvValWithBound_abs_le_lipschitzFactor A x h n
  have hstep1 :
      Le
        (COF.abs (positiveTailInvValWithBound A x h m) *
          COF.abs (positiveTailInvValWithBound A x h n))
        (COF.abs (positiveTailInvValWithBound A x h m) * L) :=
    scalar_mul_le_mul_left hn
      (scalar_abs_nonneg (positiveTailInvValWithBound A x h m))
  have hstep2 :
      Le (COF.abs (positiveTailInvValWithBound A x h m) * L) (L * L) :=
    scalar_mul_le_mul_right hm
      (by
        unfold L
        exact scalar_abs_nonneg (scalarPositiveInverseSeed.inv (eps h.k)))
  have hprod : Le
      (COF.abs (positiveTailInvValWithBound A x h m) *
        COF.abs (positiveTailInvValWithBound A x h n))
      (L * L) :=
    BishopC.le_trans hstep1 hstep2
  have hL :
      COF.abs (positiveReciprocalLipschitzBound x h) = L * L := by
    unfold positiveReciprocalLipschitzBound L
    rw [scalar_abs_mul
      (scalarPositiveInverseSeed.inv (eps h.k))
      (scalarPositiveInverseSeed.inv (eps h.k))]
  rwa [hL]





end BishopCReal

