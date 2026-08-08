import Mathdemo.Internal.CRat_iter66

/-!
# Positive representative tail reciprocal

`CRat_iter66` supplies the scalar total positive reciprocal.  This file uses a
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

/-- On the certified tail, the tail reciprocal is positive. -/
theorem positiveTailInvVal_pos
    (x : RegularSeq) (h : PosEventuallyData x) {n : Nat} (hn : h.N ≤ n) :
    COF.lt 0 (positiveTailInvVal x h n) := by
  unfold positiveTailInvVal
  rw [if_pos hn]
  exact scalarPositiveInverseSeed.inv_pos (x.val n)
    (scalar_pos_of_posEventuallyData_tail x h hn)

/-- On the certified tail, the original scalar times the tail reciprocal is
exactly one. -/
theorem positiveTail_mul_invVal_eq_one
    (x : RegularSeq) (h : PosEventuallyData x) {n : Nat} (hn : h.N ≤ n) :
    x.val n * positiveTailInvVal x h n = 1 := by
  unfold positiveTailInvVal
  rw [if_pos hn]
  exact scalarPositiveInverseSeed.mul_inv_cancel (x.val n)
    (scalar_pos_of_posEventuallyData_tail x h hn)

/-- Data package for the positive representative tail reciprocal layer. -/
structure PositiveTailReciprocalSeed : Type where
  tailInvVal : ∀ x : RegularSeq, PosEventuallyData x → Nat → Scalar
  tail_scalar_pos :
    ∀ x : RegularSeq, ∀ h : PosEventuallyData x, ∀ {n : Nat}, h.N ≤ n →
      COF.lt 0 (x.val n)
  tail_inv_pos :
    ∀ x : RegularSeq, ∀ h : PosEventuallyData x, ∀ {n : Nat}, ∀ _hn : h.N ≤ n,
      COF.lt 0 (tailInvVal x h n)
  tail_mul_inv :
    ∀ x : RegularSeq, ∀ h : PosEventuallyData x, ∀ {n : Nat}, ∀ _hn : h.N ≤ n,
      x.val n * tailInvVal x h n = 1

def positiveTailReciprocalSeed : PositiveTailReciprocalSeed where
  tailInvVal := positiveTailInvVal
  tail_scalar_pos := fun x h _ hn =>
    scalar_pos_of_posEventuallyData_tail x h hn
  tail_inv_pos := fun x h _ hn =>
    positiveTailInvVal_pos x h hn
  tail_mul_inv := fun x h _ hn =>
    positiveTail_mul_invVal_eq_one x h hn

/-- Frontier after the scalar and tail pointwise reciprocal layers are closed. -/
structure CRealQuotPositiveInverseTailFrontier : Type where
  tail_reciprocal_regular : Prop
  quotient_inv_definition : Prop
  quotient_mul_inv_cancel : Prop
  quotient_inv_pos : Prop

def cRealQuotPositiveInverseTailFrontier :
    CRealQuotPositiveInverseTailFrontier where
  tail_reciprocal_regular := True
  quotient_inv_definition := True
  quotient_mul_inv_cancel := True
  quotient_inv_pos := True

end BishopCReal

