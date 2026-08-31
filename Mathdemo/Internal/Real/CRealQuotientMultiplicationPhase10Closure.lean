import Mathdemo.Internal.Real.CRealBoundedMultiplicationEventualRespect

/-!
# CReal quotient multiplication from the Phase 10 closure

`CRealQuotientMultiplicationExplicitClosureData` exposed quotient multiplication conditionally on
`CRealMulClosureData`.  `CRealBoundedMultiplicationEventualRespect` constructs that closure data from the
explicit scalar multiplicative Archimedean datum.  This file connects the two:
bounded multiplication is now available as a concrete quotient operation
relative to `ScalarMulArchimedeanData`.
-/

namespace BishopCReal

open BishopC
open BishopCRat


/-- Concrete multiplication closure data from the explicit scalar datum. -/
def cRealMulClosureConcreteWith
    (A : ScalarMulArchimedeanData) : CRealMulClosureData A :=
  cRealMulClosureDataWith A

/-- Concrete bounded multiplication on regular representatives. -/
def mulSeqConcreteWith (A : ScalarMulArchimedeanData) :
    RegularSeq → RegularSeq → RegularSeq :=
  mulSeqWith A (cRealMulClosureConcreteWith A)

/-- Concrete quotient multiplication relative to explicit scalar data. -/
def mulQuotConcreteWith (A : ScalarMulArchimedeanData) :
    CRealQuot → CRealQuot → CRealQuot :=
  mulQuotWith A (cRealMulClosureConcreteWith A)

/-- Representative multiplication respects eventual equality in the concrete
Phase 11-A package. -/
theorem mulSeqConcrete_respects_eventually (A : ScalarMulArchimedeanData)
    (x x' y y' : RegularSeq)
    (hxx : relEventually x x') (hyy : relEventually y y') :
    relEventually
      (mulSeqConcreteWith A x y)
      (mulSeqConcreteWith A x' y') := by
  exact mulSeqWith_respects_eventually A (cRealMulClosureConcreteWith A)
    x x' y y' hxx hyy

theorem mulQuotConcrete_zero_left
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    mulQuotConcreteWith A zeroQuot x = zeroQuot := by
  exact mulQuotWith_zero_left A (cRealMulClosureConcreteWith A) x

theorem mulQuotConcrete_zero_right
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    mulQuotConcreteWith A x zeroQuot = zeroQuot := by
  exact mulQuotWith_zero_right A (cRealMulClosureConcreteWith A) x

theorem mulQuotConcrete_one_left
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    mulQuotConcreteWith A oneQuot x = x := by
  exact mulQuotWith_one_left A (cRealMulClosureConcreteWith A) x

theorem mulQuotConcrete_one_right
    (A : ScalarMulArchimedeanData) (x : CRealQuot) :
    mulQuotConcreteWith A x oneQuot = x := by
  exact mulQuotWith_one_right A (cRealMulClosureConcreteWith A) x

theorem mulQuotConcrete_comm
    (A : ScalarMulArchimedeanData) (x y : CRealQuot) :
    mulQuotConcreteWith A x y = mulQuotConcreteWith A y x := by
  exact mulQuotWith_comm A (cRealMulClosureConcreteWith A) x y




end BishopCReal

