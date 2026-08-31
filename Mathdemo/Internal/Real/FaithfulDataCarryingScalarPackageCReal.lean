import Mathdemo.Internal.Real.PositiveDataInverseConsumerTotalInverse

/-!
# Faithful data-carrying scalar package for the CReal quotient route

`NondecidableQuotientCOFOCRouteSelectorData` gives a live `BishopC.COFOC CRealQuot` only after a total
positive-inverse selector is supplied.  `PositiveDataInverseConsumerTotalInverse` separated the
constructive part of Bishop's reciprocal construction from that total selector:
the inverse laws only consume explicit positive data.

This file packages the source-faithful route:

* data-valued quotient order;
* positive-data inverse laws, with no total inverse selection;
* representative-level sequential completeness by the diagonal construction.

It intentionally does not claim a new live `BishopC.COFOC` instance.  The last
bridge to the previous interface still requires either a total inverse
totalization, or a refactoring of the scalar interface so that inverse is
data-indexed as in Bishop's construction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

/-- Representative-level sequential completeness, independent of the old
`COFO.inv : R -> R` total field and independent of opaque quotient
representative extraction. -/
structure CRealRepSequenceCompleteLayer : Type 1 where
  limit : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → RegularSeq
  lmod : ∀ (w : Nat → RegularSeq), CRealRepSequenceCauchyData w → Nat → Nat
  close_to_limit :
    ∀ (w : Nat → RegularSeq) (hc : CRealRepSequenceCauchyData w),
      ∀ k n : Nat, lmod w hc k ≤ n →
        RepCloseAtGauge (k + 1) (w n) (limit w hc)

/-- The already closed diagonal construction supplies the representation-level
completeness layer. -/
def cRealRepSequenceCompleteLayer :
    CRealRepSequenceCompleteLayer where
  limit := cRealRepDiagonalLimitCloseData.limit
  lmod := cRealRepDiagonalLimitCloseData.lmod
  close_to_limit := cRealRepDiagonalLimitCloseData.close_to_limit






end BishopCReal

set_option linter.style.longLine false

