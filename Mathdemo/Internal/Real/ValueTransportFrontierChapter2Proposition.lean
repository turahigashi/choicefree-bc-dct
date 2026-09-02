import Mathdemo.Internal.Real.RegularSeqTruthTableKernelChapter2

set_option linter.style.longLine false

/-!
# G136: value-transport frontier for Chapter 2 Proposition 2.4

G135 closed the RegularSeq `0/1` truth-table arithmetic.  This file connects
that arithmetic to the Chapter 2 `valid` field in a Bishop-faithful way:

* the source set-membership case split is proved directly from `BSet.and` and
  `BSet.or`;
* the remaining analytic obligations are named as data:
  extracting the two component absolute-summability witnesses from the formula
  representative and transporting the formula representative's `valueAt` to
  the RegularSeq expression `min2Seq` or `or2Seq`.

No representative is selected from a quotient, and no `Prop`-to-data selector
is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace CharacteristicValueTransport

open CharacteristicFormula
open CharacteristicTruthTable

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}














end CharacteristicValueTransport
end BishopRegularSeqChapter2





end BishopCReal
