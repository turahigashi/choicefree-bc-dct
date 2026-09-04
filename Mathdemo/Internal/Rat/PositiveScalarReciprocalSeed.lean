import Mathdemo.Internal.Real.QuotientEqualityDyadicSmallness
/-!
# Positive scalar reciprocal seed

`COFOAssemblyPositiveInverseData` isolates the quotient positive-inverse block.  This file closes
the scalar part needed by the eventual CReal reciprocal construction: a positive
`CRat` has a reciprocal, its product with the original scalar is `1`, and the
reciprocal is positive.

This does not yet construct the quotient-real inverse.  It supplies the
choice-free scalar reciprocal that the representative-level construction will
use.
-/

namespace BishopCRat

open BishopC

namespace Q

/-- A positive rational has a positive numerator. -/
theorem num_pos_of_pos {a : Q} (h : lt zero a) : 0 < a.num := by
  change 0 * a.den < a.num * 1 at h
  rwa [Int.zero_mul, Int.mul_one] at h





/-- Total positive reciprocal: positive rationals are inverted, other rationals
are sent to zero. -/
def posInvOrZero (a : Q) : Q :=
  if h : 0 < a.num then ⟨a.den, a.num, h⟩ else zero

/-- Rational equality transports numerator positivity forward. -/
theorem num_pos_of_rel {a b : Q} (hab : rel a b) (ha : 0 < a.num) :
    0 < b.num := by
  have hlt : lt zero a := by
    change 0 * a.den < a.num * 1
    rw [Int.zero_mul, Int.mul_one]
    exact ha
  have hb : lt zero b := (Q.lt_congr (Q.rel_refl Q.zero) hab).mp hlt
  change 0 * b.den < b.num * 1 at hb
  rwa [Int.zero_mul, Int.mul_one] at hb

/-- The total positive reciprocal respects rational equality. -/
theorem posInvOrZero_congr {a b : Q} (hab : rel a b) :
    rel (posInvOrZero a) (posInvOrZero b) := by
  unfold posInvOrZero
  by_cases ha : 0 < a.num
  · have hb : 0 < b.num := num_pos_of_rel hab ha
    rw [dif_pos ha, dif_pos hb]
    unfold rel
    calc
      a.den * b.num = b.num * a.den := by ring
      _ = a.num * b.den := by rw [← hab]
      _ = b.den * a.num := by ring
  · have hbnum : ¬ 0 < b.num := by
      intro hbn
      exact ha (num_pos_of_rel hab.symm hbn)
    rw [dif_neg ha, dif_neg hbnum]
    exact rel_refl zero

/-- Positive rationals cancel with the total positive reciprocal. -/
theorem mul_posInvOrZero_cancel (a : Q) (h : lt zero a) :
    rel (mul a (posInvOrZero a)) one := by
  have hnum : 0 < a.num := num_pos_of_pos h
  unfold posInvOrZero
  rw [dif_pos hnum]
  unfold rel mul one ofInt
  ring

/-- The total positive reciprocal is positive on positive inputs. -/
theorem posInvOrZero_pos (a : Q) (h : lt zero a) : lt zero (posInvOrZero a) := by
  have hnum : 0 < a.num := num_pos_of_pos h
  unfold posInvOrZero
  rw [dif_pos hnum]
  unfold lt zero ofInt
  rw [Int.zero_mul, Int.mul_one]
  exact a.den_pos

end Q

namespace CRat

/-- Total positive reciprocal on quotient rationals. -/
def posInvOrZero : CRat → CRat :=
  Quotient.lift (fun q => mk (Q.posInvOrZero q))
    (fun _ _ h => Quotient.sound (Q.posInvOrZero_congr h))

/-- A positive quotient rational times its total positive reciprocal is one. -/
theorem mul_posInvOrZero_cancel (x : CRat) (h : lt 0 x) :
    x * posInvOrZero x = 1 := by
  induction x using Quotient.inductionOn with
  | h q =>
      exact Quotient.sound (Q.mul_posInvOrZero_cancel q h)

/-- The total positive reciprocal of a positive quotient rational is positive. -/
theorem posInvOrZero_pos (x : CRat) (h : lt 0 x) : lt 0 (posInvOrZero x) := by
  induction x using Quotient.inductionOn with
  | h q =>
      exact Q.posInvOrZero_pos q h



end CRat
end BishopCRat

namespace BishopCReal

open BishopC
open BishopCRat

/-- Scalar reciprocal package exposed in the CReal namespace. -/
structure ScalarPositiveInverseSeed : Type where
  inv : Scalar → Scalar
  mul_inv_cancel :
    ∀ x : Scalar, COF.lt 0 x → x * inv x = 1
  inv_pos :
    ∀ x : Scalar, COF.lt 0 x → COF.lt 0 (inv x)

def scalarPositiveInverseSeed : ScalarPositiveInverseSeed where
  inv := BishopCRat.CRat.posInvOrZero
  mul_inv_cancel := BishopCRat.CRat.mul_posInvOrZero_cancel
  inv_pos := BishopCRat.CRat.posInvOrZero_pos



end BishopCReal

