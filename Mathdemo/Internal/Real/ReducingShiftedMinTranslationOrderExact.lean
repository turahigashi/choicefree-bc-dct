import Mathdemo.Internal.Real.ClosingRightMonotonicityMinSeqWith

set_option linter.style.longLine false

/-!
# G115: reducing shifted-min translation order to exact representative equality

G114 left line 743 with one translation input stated as a non-strict order.
The source half-sum identity is actually an equality:

`min(x+d,c) = min(x,c-d)+d`.

This file factors the remaining order input through an exact
`relEventually` translation identity.  The identity itself remains the
frontier, but the order wrapper is no longer a primitive field.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Eventual equality implies the represented non-strict order. -/
theorem regularSeqLe_of_relEventually
    {x y : RegularSeq}
    (hxy : relEventually x y) :
    RegularSeqLe x y := by
  have hsub0 :
      relEventually (subSeq y x) (subSeq x x) :=
    subSeq_respects_eventually
      y x
      x x
      (relEventually_symm x y hxy)
      (relEventually_refl x)
  have hsub1 :
      relEventually (subSeq x x) zeroSeq :=
    subSeq_self_eventually_law x
  have hsub :
      relEventually (subSeq y x) zeroSeq :=
    relEventually_trans
      (subSeq y x)
      (subSeq x x)
      zeroSeq
      hsub0
      hsub1
  exact
    regularSeqNonneg_of_eventual
      hsub
      not_posEventually_zero

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
