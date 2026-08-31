import Mathdemo.Internal.Rat.PositiveScalarReciprocalSeed

/-!
# Positive representative tail reciprocal

`PositiveScalarReciprocalSeed` supplies the scalar total positive reciprocal.  This file uses a
`PosEventuallyData` witness for a regular representative to build the
pointwise reciprocal tail that an eventual quotient inverse will consume.

It intentionally stops before proving this tail reciprocal is a regular
sequence; that regularity estimate is the next inverse-frontier step.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- A positive-tail witness gives scalar positivity at every tail index. -/
theorem scalar_pos_of_posEventuallyData_tail
    (x : RegularSeq) (h : PosEventuallyData x) {n : Nat} (hn : h.N ≤ n) :
    COF.lt 0 (x.val n) :=
  scalarCOFOSeed.lt_trans (eps_pos h.k) (h.tail_pos n hn)

/-- Pointwise reciprocal on the positive tail, zero before the certified tail. -/
def positiveTailInvVal (x : RegularSeq) (h : PosEventuallyData x) (n : Nat) :
    Scalar :=
  if h.N ≤ n then
    scalarPositiveInverseSeed.inv (x.val n)
  else
    0


/-- On the certified tail, the original scalar times the tail reciprocal is
exactly one. -/
theorem positiveTail_mul_invVal_eq_one
    (x : RegularSeq) (h : PosEventuallyData x) {n : Nat} (hn : h.N ≤ n) :
    x.val n * positiveTailInvVal x h n = 1 := by
  unfold positiveTailInvVal
  rw [if_pos hn]
  exact scalarPositiveInverseSeed.mul_inv_cancel (x.val n)
    (scalar_pos_of_posEventuallyData_tail x h hn)





end BishopCReal

