import Mathdemo.Internal.Real.ScalarIncrementBoundsTheorem46

set_option linter.style.longLine false

/-!
# G225: attaching the scalar Theorem 4.6 laws to carried mid sources

G224 closed the pure scalar increment bounds.  This file connects those scalar
facts to the actual Definition-1.6 representatives carried by
`Prop412DataCarryingMeasurable`.

The only extra support used below is the full domain of the auxiliary
characteristic-function representative required by the source proof of
`χ_A ≤ χ_(A∨B)`.  It is obtained directly from the corresponding
`IntegrableSet1` witness.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge





















end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46



end BishopCReal
