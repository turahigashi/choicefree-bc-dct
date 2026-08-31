import Mathdemo.Internal.Real.CRealRawSubtractionAlgebra

/-!
# CReal fixed-bound multiplication and negation

These are pointwise algebra facts for `mulValWithBound` at a fixed bound.  They
avoid the still-open global multiplication-respect and distributivity problems,
but give the eventual quotient ring assembly more audited raw material.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A negative left factor can be pulled out of fixed-bound multiplication. -/
theorem mul_neg_left_raw_fixed (K : Nat) (x y : RegularSeq) :
    relVal
      (mulValWithBound K (negVal x.val) y.val)
      (negVal (mulValWithBound K x.val y.val)) := by
  intro n
  unfold mulValWithBound negVal
  rw [show
      (-x.val (mulIndexFromBound K n) * y.val (mulIndexFromBound K n))
        - -(x.val (mulIndexFromBound K n) * y.val (mulIndexFromBound K n))
        = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- A negative right factor can be pulled out of fixed-bound multiplication. -/
theorem mul_neg_right_raw_fixed (K : Nat) (x y : RegularSeq) :
    relVal
      (mulValWithBound K x.val (negVal y.val))
      (negVal (mulValWithBound K x.val y.val)) := by
  intro n
  unfold mulValWithBound negVal
  rw [show
      (x.val (mulIndexFromBound K n) * -y.val (mulIndexFromBound K n))
        - -(x.val (mulIndexFromBound K n) * y.val (mulIndexFromBound K n))
        = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Two negative factors cancel in fixed-bound multiplication. -/
theorem mul_neg_neg_raw_fixed (K : Nat) (x y : RegularSeq) :
    relVal
      (mulValWithBound K (negVal x.val) (negVal y.val))
      (mulValWithBound K x.val y.val) := by
  intro n
  unfold mulValWithBound negVal
  rw [show
      (-x.val (mulIndexFromBound K n) * -y.val (mulIndexFromBound K n))
        - x.val (mulIndexFromBound K n) * y.val (mulIndexFromBound K n)
        = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF 0) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Audited fixed-bound multiplication/negation seed. -/
structure CRealFixedMulNegSeed : Type where
  mul_neg_left_raw_fixed : ∀ K : Nat, ∀ x y : RegularSeq,
    relVal
      (mulValWithBound K (negVal x.val) y.val)
      (negVal (mulValWithBound K x.val y.val))
  mul_neg_right_raw_fixed : ∀ K : Nat, ∀ x y : RegularSeq,
    relVal
      (mulValWithBound K x.val (negVal y.val))
      (negVal (mulValWithBound K x.val y.val))
  mul_neg_neg_raw_fixed : ∀ K : Nat, ∀ x y : RegularSeq,
    relVal
      (mulValWithBound K (negVal x.val) (negVal y.val))
      (mulValWithBound K x.val y.val)

def cRealFixedMulNegSeed : CRealFixedMulNegSeed where
  mul_neg_left_raw_fixed := mul_neg_left_raw_fixed
  mul_neg_right_raw_fixed := mul_neg_right_raw_fixed
  mul_neg_neg_raw_fixed := mul_neg_neg_raw_fixed

end BishopCReal

