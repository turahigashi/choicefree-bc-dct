import Mathdemo.Internal.Real.BishopSourceHintAuditRemainingCReal

/-!
# RegularSeq data-interface fork for Bishop-style CReal

`BishopSourceHintAuditRemainingCReal` classified the remaining assumptions in the opaque quotient
route.  The source-guided fork is to expose the Bishop real carrier as regular
sequences with Bishop equality and Type-valued positive evidence.  This file
packages that fork as a data interface.

This is intentionally not a `CommRing RegularSeq` or `BishopC.COFOC
RegularSeq`: those typeclasses use Lean's structural equality, while Bishop's
real equality is the relation `rel`.  The interface below records the correct
setoid-style carrier shape and the already constructed positive-data inverse
and diagonal completeness layers.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Sequence-level max, using the same half-sum formula as the quotient COF
encoding but staying on regular representatives. -/
def maxSeqWith (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : RegularSeq :=
  mulSeqConcreteWith A halfSeq
    (addSeq (addSeq x y) (absSeq (subSeq x y)))

/-- Sequence-level min, using the same half-sum formula as the quotient COF
encoding but staying on regular representatives. -/
def minSeqWith (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) : RegularSeq :=
  mulSeqConcreteWith A halfSeq
    (subSeq (addSeq x y) (absSeq (subSeq x y)))







end BishopCReal

set_option linter.style.longLine false

