import Mathdemo.Internal.Measure.PointLevelCleanDefinedAtExplicitRowwise

set_option linter.style.longLine false

/-!
# G313: source rows are raw subtractions, clean rows are `min2` subtractions

The G311 bridge cannot be treated as a definitional equality.  Printing the
source definitions shows that `prop_2_10_F/G` use raw representative
subtraction.  In contrast, the clean increment/drop rows are built through
`IntegrableSet1_sub`, whose representative is `hA.rep.sub (hA.rep.min2 hB.rep)`.

This node records that mismatch as concrete row-shape theorems.  It is an
important diagnostic for Chapter 4: the clean route solves the pointwise
flattening problem, while the original source representative needs a separate
transport argument or the downstream theorem must route through the clean
representative.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Source rows: raw representative subtraction -/









/-! ## 2. Clean rows: set-difference representatives with `min2` -/









/-! ## 3. The remaining bridge is a real transport problem -/




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
