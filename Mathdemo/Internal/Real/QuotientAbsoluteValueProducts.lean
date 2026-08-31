import Mathdemo.Internal.Real.QuotientTriangleInequalityField

/-!
# Quotient absolute value of products

`QuotientTriangleInequalityField` closed the triangle inequality field.  This file closes the next
local `COFO` field:

* `|x * y| = |x| * |y|`.

The concrete quotient multiplication samples each product at a pairwise bound.
The proof therefore moves both sides to one common multiplication bound, applies
the scalar identity `|a*b| = |a|*|b|` pointwise, and transports back to the
concrete bounded representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Common-bound representative form of `|x*y| = |x|*|y|`. -/
theorem abs_mul_common_bound_eventually_with
    (A : ScalarMulArchimedeanData) (x y : RegularSeq) {C : Nat}
    (hxC : standardBoundWith A x <= C)
    (hyC : standardBoundWith A y <= C)
    (haxC : standardBoundWith A (absSeq x) <= C)
    (hayC : standardBoundWith A (absSeq y) <= C) :
    relEventually
      (absSeq (mulSeqAtBoundWith A C x y hxC hyC))
      (mulSeqAtBoundWith A C (absSeq x) (absSeq y) haxC hayC) := by
  apply rel_to_relEventually
  intro n
  change Le
    (COF.abs
      (COF.abs (x.val (mulIndexFromBound C n) * y.val (mulIndexFromBound C n)) -
        (COF.abs (x.val (mulIndexFromBound C n)) *
          COF.abs (y.val (mulIndexFromBound C n)))))
    (tol n)
  rw [scalar_abs_mul]
  rw [show COF.abs (x.val (mulIndexFromBound C n)) *
        COF.abs (y.val (mulIndexFromBound C n)) -
        (COF.abs (x.val (mulIndexFromBound C n)) *
          COF.abs (y.val (mulIndexFromBound C n))) = (0 : Scalar) from by ring]
  change Le (BishopCRat.CRat.absF (0 : Scalar)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n

/-- Quotient-level absolute value distributes over concrete multiplication. -/
theorem abs_mulQuotConcreteWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    absQuot (mulQuotConcreteWith A x y) =
      mulQuotConcreteWith A (absQuot x) (absQuot y) := by
  refine Quotient.inductionOn x ?_
  intro xr
  refine Quotient.inductionOn y ?_
  intro yr
  change mkQuot (absSeq (mulSeqConcreteWith A xr yr)) =
    mkQuot (mulSeqConcreteWith A (absSeq xr) (absSeq yr))
  set K : Nat := mulBoundWith A xr yr with hKdef
  set L : Nat := mulBoundWith A (absSeq xr) (absSeq yr) with hLdef
  set C : Nat := Nat.max K L with hCdef
  have hKleC : K <= C := by
    rw [hCdef]
    exact Nat.le_max_left K L
  have hLleC : L <= C := by
    rw [hCdef]
    exact Nat.le_max_right K L
  have hxK : standardBoundWith A xr <= K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_left A xr yr
  have hyK : standardBoundWith A yr <= K := by
    rw [hKdef]
    exact standardBoundWith_le_mulBound_right A xr yr
  have haxL : standardBoundWith A (absSeq xr) <= L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_left A (absSeq xr) (absSeq yr)
  have hayL : standardBoundWith A (absSeq yr) <= L := by
    rw [hLdef]
    exact standardBoundWith_le_mulBound_right A (absSeq xr) (absSeq yr)
  have hxC : standardBoundWith A xr <= C := Nat.le_trans hxK hKleC
  have hyC : standardBoundWith A yr <= C := Nat.le_trans hyK hKleC
  have haxC : standardBoundWith A (absSeq xr) <= C := Nat.le_trans haxL hLleC
  have hayC : standardBoundWith A (absSeq yr) <= C := Nat.le_trans hayL hLleC
  apply Quotient.sound
  have hleft : relEventually (mulSeqConcreteWith A xr yr)
      (mulSeqAtBoundWith A C xr yr hxC hyC) :=
    mulSeqConcrete_to_common_bound_eventually_with A xr yr hxC hyC
  have hleft_abs : relEventually
      (absSeq (mulSeqConcreteWith A xr yr))
      (absSeq (mulSeqAtBoundWith A C xr yr hxC hyC)) :=
    absSeq_respects_eventually
      (mulSeqConcreteWith A xr yr)
      (mulSeqAtBoundWith A C xr yr hxC hyC)
      hleft
  have hmid : relEventually
      (absSeq (mulSeqAtBoundWith A C xr yr hxC hyC))
      (mulSeqAtBoundWith A C (absSeq xr) (absSeq yr) haxC hayC) :=
    abs_mul_common_bound_eventually_with A xr yr hxC hyC haxC hayC
  have hright : relEventually
      (mulSeqAtBoundWith A C (absSeq xr) (absSeq yr) haxC hayC)
      (mulSeqConcreteWith A (absSeq xr) (absSeq yr)) :=
    mulSeqCommon_to_concrete_bound_eventually_with
      A (absSeq xr) (absSeq yr) haxC hayC
  exact relEventually_trans _ _ _
    (relEventually_trans _ _ _ hleft_abs hmid) hright






end BishopCReal

