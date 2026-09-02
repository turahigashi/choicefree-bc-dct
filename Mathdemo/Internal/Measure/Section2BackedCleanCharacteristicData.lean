import Mathdemo.Internal.Measure.SourceRowsRawSubtractionsCleanRows

set_option linter.style.longLine false

/-!
# Stage A2: Section-2 backed clean characteristic data

This node re-exports the clean characteristic layer through the additive
Section-2 primitives introduced in `BishopSec2_L1`.  Difference, intersection,
and union no longer carry a per-call `out` witness.  They are obtained from the
single Section-2 clean Boolean operation surface `CleanBooleanSec2Ops`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Clean characteristic aliases and adapters -/



namespace CleanCharData





















end CleanCharData

/-! ## 2. Unconditional clean Boolean wrappers over Section 2 -/















/-! ## 3. Stage-A2 audit -/




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
