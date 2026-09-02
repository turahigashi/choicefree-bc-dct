import Mathdemo.Internal.Real.CloseCoverDifferenceDichotomyInput
import Mathdemo.Internal.Sec4.RemainingAtomsAssembly

set_option linter.style.longLine false

/-!
# G278: lower theorem 4.15 to the final prop-4.2 remaining atoms

G277 left one public frontier: a generic `Sec4ChiFCaseToolsData` provider.
The b2b22 development plugs the completed row-to-flat construction into the
case-tools route.  After that, the only remaining inputs are the three
`prop_4_2_lambda_k` atoms identified in `Sec4Prop42RemainingAtomTools`.

This node exposes theorem 4.15 through exactly those atoms, removing the
case-tools provider as a public assumption.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Remaining prop-4.2 atoms imply the G269 local provider -/






/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
