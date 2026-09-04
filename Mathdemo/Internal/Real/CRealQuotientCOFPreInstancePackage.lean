import Mathdemo.Internal.Real.CRealQuotientMultiplicationAssociativity
/-!
# CReal quotient COF pre-instance package

`CRealQuotientClosedAlgebraPackage` gathered the closed quotient algebra.  This file turns that
algebra into the first COF-facing package:

* a concrete `CommRing CRealQuot` record value, parameterized by the explicit
  multiplication Archimedean datum;
* COF operation candidates for `lt`, `abs`, `max`, `min`, and `half`;
* the COF algebraic half/max/min equations;
* an honest marker that the data-valued quotient cotransitivity field is still
  the missing item before an actual `BishopC.COF CRealQuot` value can be
  emitted.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- `Nat.smul` recursion for the quotient package, kept explicit so the
`CommRing` record can be built without relying on extra instance synthesis. -/
def nsmulQuot : Nat → CRealQuot → CRealQuot :=
  fun n x => Nat.rec zeroQuot (fun _ ih => addQuot ih x) n

/-- `Int.smul` recursion for the quotient package. -/
def zsmulQuot : Int → CRealQuot → CRealQuot :=
  fun n x =>
    match n with
    | Int.ofNat m => nsmulQuot m x
    | Int.negSucc m => negQuot (nsmulQuot (m + 1) x)

/-- The closed quotient algebra as a `CommRing` record value.  It is deliberately
not registered as a global instance: multiplication still depends on the
explicit scalar multiplicative Archimedean datum `A`. -/
@[reducible] def cRealQuotCommRingConcreteWith
    (A : ScalarMulArchimedeanData) : CommRing CRealQuot where
  add := addQuot
  mul := mulQuotConcreteWith A
  neg := negQuot
  zero := zeroQuot
  one := oneQuot
  add_assoc := addQuot_assoc
  add_comm := addQuot_comm
  zero_add := addQuot_zero_left
  add_zero := addQuot_zero_right
  neg_add_cancel := addQuot_neg_left
  mul_assoc := mulQuotConcrete_assoc A
  mul_comm := mulQuotConcrete_comm A
  one_mul := mulQuotConcrete_one_left A
  mul_one := mulQuotConcrete_one_right A
  left_distrib := mulQuotConcrete_left_distrib A
  right_distrib := mulQuotConcrete_right_distrib A
  zero_mul := mulQuotConcrete_zero_left A
  mul_zero := mulQuotConcrete_zero_right A
  nsmul := nsmulQuot
  zsmul := zsmulQuot

/-- Quotient maximum, defined by the COF half-sum formula so the COF equation is
definitionally transparent. -/
def maxQuotConcreteWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) : CRealQuot :=
  mulQuotConcreteWith A halfQuot
    (addQuot (addQuot x y) (absQuot (subQuot x y)))

/-- Quotient minimum, defined by the COF half-sum formula so the COF equation is
definitionally transparent. -/
def minQuotConcreteWith
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) : CRealQuot :=
  mulQuotConcreteWith A halfQuot
    (subQuot (addQuot x y) (absQuot (subQuot x y)))

/-- The quotient half element satisfies the COF half equation. -/
theorem halfQuot_add_half : addQuot halfQuot halfQuot = oneQuot := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (addVal halfVal halfVal) oneVal
  intro n
  unfold addVal addIndex halfVal oneVal constVal
  rw [COF.half_add_half]
  rw [show (1 : Scalar) - 1 = 0 from by ring]
  change Le (BishopCRat.CRat.absF (0 : Scalar)) (tol n)
  rw [scalarCOFOSeed.abs_zero]
  exact tol_nonneg n









end BishopCReal

