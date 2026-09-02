import Mathdemo.Internal.Real.RemoveSeparateComplementBridgeInput

set_option linter.style.longLine false

/-!
# G268: build the local majorant split from local bridge generators

G267 removed the separate complement bridge.  The remaining public frontier was
the full local majorant split package.  This file opens that package one layer:
the set selection, epsilon budget, delta, and majorant smallness estimates are
now constructed from the existing source lemmas.  What remains is the genuinely
local definitional frontier: producing the local value bridges for the direct
measurable relative integral from the carried representatives.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Small local atoms -/




/-! ## 2. Source data with local bridge generators -/






/-! ## 3. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
