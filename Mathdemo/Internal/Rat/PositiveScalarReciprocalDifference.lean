import Mathdemo.Internal.Real.PositiveRepresentativeTailReciprocal

/-!
# Positive scalar reciprocal difference

The representative reciprocal from `PositiveRepresentativeTailReciprocal` will be regular only after its
pointwise difference is reduced to the original regular representative
difference.  This file closes that scalar algebra step:

`inv a - inv b = inv a * inv b * (b - a)` for positive `CRat` scalars.

It intentionally stops before the analytic lower-bound estimate needed to turn
this identity into a full regularity proof for the reciprocal tail.
-/

namespace BishopCRat

open BishopC

namespace Q

/-- Difference identity for the total positive reciprocal at the raw rational
layer. -/
theorem posInvOrZero_sub_eq_mul_sub (a b : Q)
    (ha : lt zero a) (hb : lt zero b) :
    rel (add (posInvOrZero a) (neg (posInvOrZero b)))
      (mul (mul (posInvOrZero a) (posInvOrZero b)) (add b (neg a))) := by
  have hnuma : 0 < a.num := num_pos_of_pos ha
  have hnumb : 0 < b.num := num_pos_of_pos hb
  unfold posInvOrZero
  rw [dif_pos hnuma, dif_pos hnumb]
  unfold rel add neg mul
  ring

end Q

namespace CRat

/-- Difference identity for the total positive reciprocal on quotient
rationals. -/
theorem posInvOrZero_sub_eq_mul_sub (a b : CRat)
    (ha : lt 0 a) (hb : lt 0 b) :
    posInvOrZero a - posInvOrZero b =
      posInvOrZero a * posInvOrZero b * (b - a) := by
  induction a using Quotient.inductionOn with
  | h qa =>
      induction b using Quotient.inductionOn with
      | h qb =>
          exact Quotient.sound (Q.posInvOrZero_sub_eq_mul_sub qa qb ha hb)

end CRat
end BishopCRat

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar form of the positive reciprocal difference identity. -/
theorem scalar_posInv_sub_eq_mul_sub (a b : Scalar)
    (ha : COF.lt 0 a) (hb : COF.lt 0 b) :
    scalarPositiveInverseSeed.inv a - scalarPositiveInverseSeed.inv b =
      scalarPositiveInverseSeed.inv a * scalarPositiveInverseSeed.inv b * (b - a) :=
  BishopCRat.CRat.posInvOrZero_sub_eq_mul_sub a b ha hb

/-- Absolute-value form of the positive reciprocal difference identity. -/
theorem scalar_abs_posInv_sub_eq_mul_abs_sub (a b : Scalar)
    (ha : COF.lt 0 a) (hb : COF.lt 0 b) :
    COF.abs (scalarPositiveInverseSeed.inv a - scalarPositiveInverseSeed.inv b) =
      COF.abs (scalarPositiveInverseSeed.inv a) *
        COF.abs (scalarPositiveInverseSeed.inv b) * COF.abs (b - a) := by
  rw [scalar_posInv_sub_eq_mul_sub a b ha hb]
  rw [scalar_abs_mul
    (scalarPositiveInverseSeed.inv a * scalarPositiveInverseSeed.inv b) (b - a)]
  rw [scalar_abs_mul
    (scalarPositiveInverseSeed.inv a) (scalarPositiveInverseSeed.inv b)]

/-- Non-strict scalar estimate obtained directly from the exact identity. -/
theorem scalar_abs_posInv_sub_le_mul_abs_sub (a b : Scalar)
    (ha : COF.lt 0 a) (hb : COF.lt 0 b) :
    Le (COF.abs (scalarPositiveInverseSeed.inv a - scalarPositiveInverseSeed.inv b))
      (COF.abs (scalarPositiveInverseSeed.inv a) *
        COF.abs (scalarPositiveInverseSeed.inv b) * COF.abs (b - a)) := by
  rw [scalar_abs_posInv_sub_eq_mul_abs_sub a b ha hb]
  exact BishopC.le_refl
    (COF.abs (scalarPositiveInverseSeed.inv a) *
      COF.abs (scalarPositiveInverseSeed.inv b) * COF.abs (b - a))

/-- Data package for the scalar reciprocal-difference layer. -/
structure ScalarPositiveInverseDifferenceSeed : Type where
  sub_eq_mul_sub :
    ∀ a b : Scalar, COF.lt 0 a → COF.lt 0 b →
      scalarPositiveInverseSeed.inv a - scalarPositiveInverseSeed.inv b =
        scalarPositiveInverseSeed.inv a * scalarPositiveInverseSeed.inv b * (b - a)
  abs_sub_eq :
    ∀ a b : Scalar, COF.lt 0 a → COF.lt 0 b →
      COF.abs (scalarPositiveInverseSeed.inv a - scalarPositiveInverseSeed.inv b) =
        COF.abs (scalarPositiveInverseSeed.inv a) *
          COF.abs (scalarPositiveInverseSeed.inv b) * COF.abs (b - a)
  abs_sub_le :
    ∀ a b : Scalar, COF.lt 0 a → COF.lt 0 b →
      Le (COF.abs (scalarPositiveInverseSeed.inv a - scalarPositiveInverseSeed.inv b))
        (COF.abs (scalarPositiveInverseSeed.inv a) *
          COF.abs (scalarPositiveInverseSeed.inv b) * COF.abs (b - a))

def scalarPositiveInverseDifferenceSeed :
    ScalarPositiveInverseDifferenceSeed where
  sub_eq_mul_sub := scalar_posInv_sub_eq_mul_sub
  abs_sub_eq := scalar_abs_posInv_sub_eq_mul_abs_sub
  abs_sub_le := scalar_abs_posInv_sub_le_mul_abs_sub

/-- Frontier after the exact scalar reciprocal-difference identity is closed. -/
structure CRealQuotPositiveInverseDifferenceFrontier : Type where
  reciprocal_tail_uniform_bound : Prop
  reciprocal_tail_regular : Prop
  quotient_inv_definition : Prop
  quotient_inverse_laws : Prop

def cRealQuotPositiveInverseDifferenceFrontier :
    CRealQuotPositiveInverseDifferenceFrontier where
  reciprocal_tail_uniform_bound := True
  reciprocal_tail_regular := True
  quotient_inv_definition := True
  quotient_inverse_laws := True

end BishopCReal

