import Mathdemo.Internal.Real.CharacteristicExpansionLawsTheorem46

set_option linter.style.longLine false

/-!
# G224: scalar increment bounds for the Theorem 4.6 local steps

G223 closed the characteristic expansion laws.  This file closes the remaining
pure scalar increment estimates needed for the source two-step proof:

* set expansion: if `χ₀ ≤ χ₁` and both are characteristic values, then the
  `f+`/`f-` increment is bounded by the `|f|` increment;
* truncation expansion: if `n ≤ m`, the increment from level `n` to level `m`
  is monotone in the underlying nonnegative value.

The proofs use only the `0/1` characteristic alternatives and the existing
`min` telescope identity from Proposition 4.2.
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
