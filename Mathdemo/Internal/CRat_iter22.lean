import Mathdemo.Internal.CRat_iter21

/-!
# CReal quotient additive operations

This file lifts the already-checked representation operations to the quotient
by eventual Bishop equality.  It still stops short of a `CommRing` instance:
the remaining ring laws should be proved as separate quotient-level theorems.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Quotient constructor for eventual Bishop reals. -/
def mkQuot (x : RegularSeq) : CRealQuot :=
  Quotient.mk eventualSetoid x

def constQuot (q : Scalar) : CRealQuot :=
  mkQuot (constSeq q)

def zeroQuot : CRealQuot := constQuot 0
def oneQuot : CRealQuot := constQuot 1
def halfQuot : CRealQuot := constQuot (COF.half : Scalar)

def negQuot : CRealQuot → CRealQuot :=
  Quotient.lift (fun x => mkQuot (negSeq x))
    (fun x y hxy => Quotient.sound (negSeq_respects_eventually x y hxy))

def addQuot : CRealQuot → CRealQuot → CRealQuot :=
  Quotient.lift₂ (fun x y => mkQuot (addSeq x y))
    (fun x x' y y' hxx hyy =>
      Quotient.sound (addSeq_respects_eventually x y x' y' hxx hyy))

def subQuot : CRealQuot → CRealQuot → CRealQuot :=
  Quotient.lift₂ (fun x y => mkQuot (subSeq x y))
    (fun x x' y y' hxx hyy =>
      Quotient.sound (subSeq_respects_eventually x y x' y' hxx hyy))

def absQuot : CRealQuot → CRealQuot :=
  Quotient.lift (fun x => mkQuot (absSeq x))
    (fun x y hxy => Quotient.sound (absSeq_respects_eventually x y hxy))

/-- Audited quotient-level additive operation seed. -/
structure CRealQuotAdditiveOpsSeed : Type where
  mkQuot : RegularSeq → CRealQuot
  constQuot : Scalar → CRealQuot
  zeroQuot : CRealQuot
  oneQuot : CRealQuot
  halfQuot : CRealQuot
  negQuot : CRealQuot → CRealQuot
  addQuot : CRealQuot → CRealQuot → CRealQuot
  subQuot : CRealQuot → CRealQuot → CRealQuot
  absQuot : CRealQuot → CRealQuot

def cRealQuotAdditiveOpsSeed : CRealQuotAdditiveOpsSeed where
  mkQuot := mkQuot
  constQuot := constQuot
  zeroQuot := zeroQuot
  oneQuot := oneQuot
  halfQuot := halfQuot
  negQuot := negQuot
  addQuot := addQuot
  subQuot := subQuot
  absQuot := absQuot

end BishopCReal

