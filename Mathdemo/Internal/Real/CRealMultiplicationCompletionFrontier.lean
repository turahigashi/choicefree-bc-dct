import Mathdemo.Internal.Real.CRealQuotientMultiplicationExplicitClosureData

/-!
# CReal multiplication completion frontier

`CRealQuotientMultiplicationExplicitClosureData` proves that bounded representative multiplication descends to the
eventual-equality quotient once the remaining closure data are supplied.  This
file records the exact remaining obligations for turning that conditional seed
into the multiplicative part of the eventual `COFOC CReal` instance.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- The proof obligations that make the conditional multiplication of
`CRealQuotientMultiplicationExplicitClosureData` available as a concrete quotient operation.

The first field is the scalar dyadic bound currently missing from
`BishopCRat.CRat.COFOSeed`; the next two fields are the representative-level
closure and quotient-respect facts for bounded multiplication. -/
structure CRealMulCompletionObligations : Type where
  scalarData : ScalarMulArchimedeanData
  mul_regular : ∀ x y : RegularSeq, RegularVal (boundedMulValWith scalarData x y)
  mul_respects_eventually : ∀ x x' y y' : RegularSeq,
    relEventually x x' → relEventually y y' →
      relEventually
        { val := boundedMulValWith scalarData x y, regular := mul_regular x y }
        { val := boundedMulValWith scalarData x' y', regular := mul_regular x' y' }

/-- The closure data of `CRealQuotientMultiplicationExplicitClosureData` recovered from the completion obligations. -/
def CRealMulCompletionObligations.toClosureData
    (O : CRealMulCompletionObligations) : CRealMulClosureData O.scalarData where
  mul_regular := O.mul_regular
  mul_respects_eventually := O.mul_respects_eventually

/-- The bound seed recovered from the scalar part of the completion obligations. -/
def CRealMulCompletionObligations.toBoundSeed
    (O : CRealMulCompletionObligations) : CRealMulBoundSeed :=
  cRealMulBoundSeedWith O.scalarData

/-- The quotient multiplication seed recovered from the completion obligations. -/
def CRealMulCompletionObligations.toQuotMulOpsSeed
    (O : CRealMulCompletionObligations) : CRealQuotMulOpsSeed :=
  cRealQuotMulOpsSeedWith O.scalarData O.toClosureData

/-- Remaining ring laws after quotient multiplication exists.  These are kept
separate because zero/one/comm already descend in `CRealQuotientMultiplicationExplicitClosureData`, while
associativity and distributivity require more substantial bound bookkeeping. -/
structure CRealQuotMulRingLawData (O : CRealMulCompletionObligations) : Type where
  mul_assoc : ∀ x y z : CRealQuot,
    mulQuotWith O.scalarData O.toClosureData
      (mulQuotWith O.scalarData O.toClosureData x y) z =
    mulQuotWith O.scalarData O.toClosureData x
      (mulQuotWith O.scalarData O.toClosureData y z)
  left_distrib : ∀ x y z : CRealQuot,
    mulQuotWith O.scalarData O.toClosureData x (addQuot y z) =
      addQuot
        (mulQuotWith O.scalarData O.toClosureData x y)
        (mulQuotWith O.scalarData O.toClosureData x z)
  right_distrib : ∀ x y z : CRealQuot,
    mulQuotWith O.scalarData O.toClosureData (addQuot x y) z =
      addQuot
        (mulQuotWith O.scalarData O.toClosureData x z)
        (mulQuotWith O.scalarData O.toClosureData y z)

/-- The exact Phase 9-11 frontier: completion obligations plus the remaining
ring laws needed before quotient multiplication can feed a concrete ring/COFO
instance. -/
structure CRealMulFinalFrontier : Type where
  obligations : CRealMulCompletionObligations
  ringLaws : CRealQuotMulRingLawData obligations

def CRealMulFinalFrontier.toQuotMulOpsSeed
    (F : CRealMulFinalFrontier) : CRealQuotMulOpsSeed :=
  F.obligations.toQuotMulOpsSeed

theorem CRealMulFinalFrontier.mul_zero_left
    (F : CRealMulFinalFrontier) (x : CRealQuot) :
    (F.toQuotMulOpsSeed).mulQuot zeroQuot x = zeroQuot :=
  (F.toQuotMulOpsSeed).zero_left x

theorem CRealMulFinalFrontier.mul_zero_right
    (F : CRealMulFinalFrontier) (x : CRealQuot) :
    (F.toQuotMulOpsSeed).mulQuot x zeroQuot = zeroQuot :=
  (F.toQuotMulOpsSeed).zero_right x

theorem CRealMulFinalFrontier.mul_one_left
    (F : CRealMulFinalFrontier) (x : CRealQuot) :
    (F.toQuotMulOpsSeed).mulQuot oneQuot x = x :=
  (F.toQuotMulOpsSeed).one_left x

theorem CRealMulFinalFrontier.mul_one_right
    (F : CRealMulFinalFrontier) (x : CRealQuot) :
    (F.toQuotMulOpsSeed).mulQuot x oneQuot = x :=
  (F.toQuotMulOpsSeed).one_right x

theorem CRealMulFinalFrontier.mul_comm
    (F : CRealMulFinalFrontier) (x y : CRealQuot) :
    (F.toQuotMulOpsSeed).mulQuot x y =
      (F.toQuotMulOpsSeed).mulQuot y x :=
  (F.toQuotMulOpsSeed).comm x y

end BishopCReal

