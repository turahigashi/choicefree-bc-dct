import Mathdemo.Internal.Real.CRealMultiplicationBoundSeed

/-!
# CReal quotient multiplication under explicit closure data

The previous file exposed the scalar/bound obstruction honestly.  This file
continues the quotient construction conditionally: once multiplication
regularity and eventual respect are supplied, bounded multiplication lifts to
the eventual-equality quotient and the already-proved raw zero/one/comm laws
descend to quotient laws.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The remaining multiplication closure data needed after bounds are fixed. -/
structure CRealMulClosureData (A : ScalarMulArchimedeanData) : Type where
  mul_regular : ∀ x y : RegularSeq, RegularVal (boundedMulValWith A x y)
  mul_respects_eventually : ∀ x x' y y' : RegularSeq,
    relEventually x x' → relEventually y y' →
      relEventually
        { val := boundedMulValWith A x y, regular := mul_regular x y }
        { val := boundedMulValWith A x' y', regular := mul_regular x' y' }

/-- Bounded multiplication as a regular representative, conditional on closure data. -/
def mulSeqWith (A : ScalarMulArchimedeanData) (D : CRealMulClosureData A)
    (x y : RegularSeq) : RegularSeq where
  val := boundedMulValWith A x y
  regular := D.mul_regular x y

/-- Representative multiplication respects eventual equality. -/
theorem mulSeqWith_respects_eventually (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually (mulSeqWith A D x y) (mulSeqWith A D x' y') := by
  exact D.mul_respects_eventually x x' y y' hxx hyy

/-- Quotient multiplication, conditional on multiplication closure data. -/
def mulQuotWith (A : ScalarMulArchimedeanData) (D : CRealMulClosureData A) :
    CRealQuot → CRealQuot → CRealQuot :=
  Quotient.lift₂ (fun x y => mkQuot (mulSeqWith A D x y))
    (fun x x' y y' hxx hyy =>
      Quotient.sound (mulSeqWith_respects_eventually A D x y x' y' hxx hyy))

/-- Zero is a left zero for quotient multiplication. -/
theorem mulQuotWith_zero_left_mk (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : RegularSeq) :
    mulQuotWith A D zeroQuot (mkQuot x) = zeroQuot := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (boundedMulValWith A zeroSeq x) zeroVal
  exact bounded_mul_zero_left_raw_with A x

/-- Zero is a right zero for quotient multiplication. -/
theorem mulQuotWith_zero_right_mk (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : RegularSeq) :
    mulQuotWith A D (mkQuot x) zeroQuot = zeroQuot := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (boundedMulValWith A x zeroSeq) zeroVal
  exact bounded_mul_zero_right_raw_with A x

/-- One is a left identity for quotient multiplication. -/
theorem mulQuotWith_one_left_mk (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : RegularSeq) :
    mulQuotWith A D oneQuot (mkQuot x) = mkQuot x := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (boundedMulValWith A oneSeq x) x.val
  exact bounded_mul_one_left_raw_with A x

/-- One is a right identity for quotient multiplication. -/
theorem mulQuotWith_one_right_mk (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : RegularSeq) :
    mulQuotWith A D (mkQuot x) oneQuot = mkQuot x := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (boundedMulValWith A x oneSeq) x.val
  exact bounded_mul_one_right_raw_with A x

/-- Quotient multiplication is commutative. -/
theorem mulQuotWith_comm_mk (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x y : RegularSeq) :
    mulQuotWith A D (mkQuot x) (mkQuot y) =
      mulQuotWith A D (mkQuot y) (mkQuot x) := by
  apply Quotient.sound
  apply rel_to_relEventually
  change relVal (boundedMulValWith A x y) (boundedMulValWith A y x)
  exact bounded_mul_comm_raw_with A x y

theorem mulQuotWith_zero_left (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : CRealQuot) :
    mulQuotWith A D zeroQuot x = zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact mulQuotWith_zero_left_mk A D x'

theorem mulQuotWith_zero_right (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : CRealQuot) :
    mulQuotWith A D x zeroQuot = zeroQuot := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact mulQuotWith_zero_right_mk A D x'

theorem mulQuotWith_one_left (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : CRealQuot) :
    mulQuotWith A D oneQuot x = x := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact mulQuotWith_one_left_mk A D x'

theorem mulQuotWith_one_right (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x : CRealQuot) :
    mulQuotWith A D x oneQuot = x := by
  refine Quotient.inductionOn x ?_
  intro x'
  exact mulQuotWith_one_right_mk A D x'

theorem mulQuotWith_comm (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) (x y : CRealQuot) :
    mulQuotWith A D x y = mulQuotWith A D y x := by
  refine Quotient.inductionOn x ?_
  intro x'
  refine Quotient.inductionOn y ?_
  intro y'
  exact mulQuotWith_comm_mk A D x' y'

/-- Audited conditional quotient multiplication seed. -/
structure CRealQuotMulOpsSeed : Type where
  scalarData : ScalarMulArchimedeanData
  closureData : CRealMulClosureData scalarData
  mulSeq : RegularSeq → RegularSeq → RegularSeq
  mulQuot : CRealQuot → CRealQuot → CRealQuot
  mul_respects : ∀ x x' y y' : RegularSeq,
    relEventually x x' → relEventually y y' → relEventually (mulSeq x y) (mulSeq x' y')
  zero_left : ∀ x : CRealQuot, mulQuot zeroQuot x = zeroQuot
  zero_right : ∀ x : CRealQuot, mulQuot x zeroQuot = zeroQuot
  one_left : ∀ x : CRealQuot, mulQuot oneQuot x = x
  one_right : ∀ x : CRealQuot, mulQuot x oneQuot = x
  comm : ∀ x y : CRealQuot, mulQuot x y = mulQuot y x

def cRealQuotMulOpsSeedWith (A : ScalarMulArchimedeanData)
    (D : CRealMulClosureData A) : CRealQuotMulOpsSeed where
  scalarData := A
  closureData := D
  mulSeq := mulSeqWith A D
  mulQuot := mulQuotWith A D
  mul_respects := mulSeqWith_respects_eventually A D
  zero_left := mulQuotWith_zero_left A D
  zero_right := mulQuotWith_zero_right A D
  one_left := mulQuotWith_one_left A D
  one_right := mulQuotWith_one_right A D
  comm := mulQuotWith_comm A D

end BishopCReal

