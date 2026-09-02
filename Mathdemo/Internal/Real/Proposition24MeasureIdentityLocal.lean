import Mathdemo.Internal.Real.LocalNonnegativeSubseriesDataChapter2

set_option linter.style.longLine false

/-!
# G149: Proposition 2.4 measure identity from local nonnegative data

G148 assembled the integrable representatives for `A ∧ B` and `A ∨ B` from
local nonnegative-subseries certificates and the closed scalar-recovery data.
This file adds the remaining measure identity

`mu(A) + mu(B) = mu(A ∨ B) + mu(A ∧ B)`

using only the carried integral-agreement data for addition/subtraction and the
already closed RegularSeq algebra laws.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Right cancellation for the source subtraction display: `(x - y) + y = x`
over Bishop eventual equality. -/
theorem addSeq_sub_right_cancel_eventually
    (x y : RegularSeq) :
    relEventually (addSeq (subSeq x y) y) x := by
  have hsub :
      relEventually (subSeq x y) (addSeq x (negSeq y)) :=
    subSeq_eq_add_neg_eventually x y
  have h0 :
      relEventually
        (addSeq (subSeq x y) y)
        (addSeq (addSeq x (negSeq y)) y) :=
    addSeq_respects_eventually
      (subSeq x y) (addSeq x (negSeq y))
      y y hsub (relEventually_refl y)
  have h1 :
      relEventually
        (addSeq (addSeq x (negSeq y)) y)
        (addSeq x (addSeq (negSeq y) y)) :=
    addSeq_assoc_eventually x (negSeq y) y
  have hcancel :
      relEventually (addSeq (negSeq y) y) zeroSeq :=
    addSeq_neg_left_eventually y
  have h2 :
      relEventually
        (addSeq x (addSeq (negSeq y) y))
        (addSeq x zeroSeq) :=
    addSeq_respects_eventually
      x x
      (addSeq (negSeq y) y) zeroSeq
      (relEventually_refl x) hcancel
  have h3 :
      relEventually (addSeq x zeroSeq) x :=
    addSeq_zero_right_eventually x
  exact
    relEventually_trans
      (addSeq (subSeq x y) y)
      (addSeq (addSeq x (negSeq y)) y)
      x
      h0
      (relEventually_trans
        (addSeq (addSeq x (negSeq y)) y)
        (addSeq x (addSeq (negSeq y) y))
        x
        h1
        (relEventually_trans
          (addSeq x (addSeq (negSeq y) y))
          (addSeq x zeroSeq)
          x
          h2 h3))

namespace BishopRegularSeqChapter2
namespace Prop24MeasureIdentityFromLocalNonnegative

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition
open Prop24LocalNonnegativeSubseries

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}






end Prop24MeasureIdentityFromLocalNonnegative
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.Prop24LocalNonnegativeSubseries
open BishopRegularSeqChapter2.Prop24MeasureIdentityFromLocalNonnegative





end BishopCReal
