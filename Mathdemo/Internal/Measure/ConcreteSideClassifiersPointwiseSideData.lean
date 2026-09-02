import Mathdemo.Internal.Measure.CleanSideClassifiedRows

set_option linter.style.longLine false

/-!
# G308: concrete side classifiers from pointwise side data

G307 left the finite-support work behind the abstract `RowSideClassifier`.
This node constructs the row side classifier for the clean Proposition-2.10
increment/drop families from explicit Type-coded side data for the source
sets `A_i` at the point `x`.

This deliberately does not extract a witness from raw membership in
`BSet.bigOr A` or `BSet.bigAnd A`.  For the union-inside and
intersection-outside cases, the required hit index is source data that must be
kept explicitly in later nodes.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise side data for source rows -/







/-! ## 2. Side algebra for finite constructors -/







/-! ## 3. Clean Proposition-2.10 row side classifiers -/





/-! ## 4. Point-data packages for the remaining finite-support step -/









namespace BigOrPointSideData



end BigOrPointSideData

namespace BigOrPointOutsideData



end BigOrPointOutsideData

namespace BigAndPointInsideData



end BigAndPointInsideData

namespace BigAndPointOutsideData



end BigAndPointOutsideData

/-! ## 5. Audit -/




end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route



end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal

