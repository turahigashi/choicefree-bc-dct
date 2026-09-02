import Mathdemo.Internal.Real.SourceLevelTheorem415DownOneStepFiniteCover

set_option linter.style.longLine false

/-!
# G261: source-level theorem 4.15 from the corrected abs-row package

G260 lowered the source-level theorem-4.15 route to the one-step finite-cover
abs assembly `Sec4CoverChiFStepAbs`, and showed that source-level
`Sec4ChiFCaseToolsData` builds that assembly without any `B`-dependent
selector input.

This file lowers the remaining function-side case-tool input to the corrected
abs-row package already proved in b2b20:

`Sec4ChiFCaseAbsPackTools -> Sec4ChiFCaseToolsData -> Sec4CoverChiFStepAbs`.

Thus the public theorem-4.15 route no longer asks for the abstract case tools.
It asks for the row/outer absolute-convergence package for each absolute-error
representative.  That package is still data-carrying, but its components are
the explicit row-to-flat bridge and the positive/negative row abs pack
constructors, not a hidden choice principle.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Abs-row packages directly produce the one-step cover assembly -/




/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
