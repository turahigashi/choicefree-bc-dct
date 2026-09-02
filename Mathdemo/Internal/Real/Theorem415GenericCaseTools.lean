import Mathdemo.Internal.Real.Theorem415LayerTelescopeData
import Mathdemo.Internal.Sec4.CaseRowTools

set_option linter.style.longLine false

/-!
# G249: theorem 4.15 from generic case tools

G248 connected theorem 4.15 to layer telescope data.  This file adds the
parallel route that is closer to the definitional reading of measurable sets:
the set-side cover/difference dichotomy is not supplied per `B`; it is built by
`sec4_coverDichotomyData` from the validness fields of the integrable sets
`coverSet f k ∧ B` and their difference layers.

Thus the public input is only function-side `χ_A·f` case tools for the
abs-error representatives.  The measurable-set side is obtained from the
definitions already present in chapter 4.
-/

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
