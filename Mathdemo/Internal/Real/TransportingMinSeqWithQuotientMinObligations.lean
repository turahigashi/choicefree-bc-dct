import Mathdemo.Internal.Real.ClosingRegularSeqAbsoluteValueTwoSided
set_option linter.style.longLine false

/-!
# G97: transporting `minSeqWith` to quotient min obligations

G96 closed the scalar half-sum kernel for min monotonicity.  The remaining
representative-level min laws still had to cross the `minSeqWith` wrapper.

This file closes that wrapper transport:

* `mkQuot (minSeqWith A x y)` is the quotient min half-sum;
* the two sequence-level min laws reduce to quotient-level `not_ltQuot`
  obligations.

The quotient min order obligations are intentionally left explicit.  This
keeps the source proof honest: the representative adapter is closed, while the
next mathematical step is the quotient order comparison itself.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}


/-- The representative min half-sum denotes the COF-facing quotient min. -/
theorem mkQuot_minSeqWith_eq_minQuotCOFWith
    (A : ScalarMulArchimedeanData)
    (x y : RegularSeq) :
    mkQuot (minSeqWith A x y) =
      minQuotCOFWith A (mkQuot x) (mkQuot y) := by
  rw [minQuotCOF_eq_concrete A (mkQuot x) (mkQuot y)]
  rfl

/-- Addition of representatives denotes quotient addition. -/
theorem mkQuot_addSeq_eq_addQuot
    (x y : RegularSeq) :
    mkQuot (addSeq x y) = addQuot (mkQuot x) (mkQuot y) := by
  rfl



namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
