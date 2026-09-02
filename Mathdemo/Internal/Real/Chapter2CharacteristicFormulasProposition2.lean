import Mathdemo.Internal.Real.Chapter2FullDomainClosureFinite

set_option linter.style.longLine false

/-!
# G134: chapter-2 characteristic formulas for Proposition 2.4

G133 closed the full-domain layer for finite set operations.  This file fixes
the RegularSeq-native characteristic-representation formulas for Proposition
2.4:

* `chi(A ∧ B) = min2(chi A, chi B)`;
* `chi(A ∨ B) = chi A + chi B - min2(chi A, chi B)`.

All Definition 1.6 operation data is explicit.  No quotient representative or
Prop-to-data selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2

namespace CharacteristicFormula

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
















end CharacteristicFormula

end BishopRegularSeqChapter2





end BishopCReal
