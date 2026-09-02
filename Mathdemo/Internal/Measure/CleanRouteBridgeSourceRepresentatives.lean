import Mathdemo.Internal.Measure.AssembleCleanClassifiedRowWitnessesPoint

set_option linter.style.longLine false

/-!
# G311: clean-route bridge back to the source representatives

G310 closes the clean point-data route up to Definition-2.3 pointwise
definedness for the clean representatives.  The remaining source-level issue is
not a row-to-flat problem anymore: it is the bridge from the clean increment/drop
representatives back to the original telescoping representatives used by
Proposition 2.10.

This node isolates that bridge.  It does not identify the clean and source
representatives by fiat.  Instead it states the exact transport data needed to
convert the clean route into the existing `Prop210B/CSourceRepSideWitness`
surface.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Clean-to-source bridge records -/





/-! ## 2. Route witnesses from clean point data to source side data -/



namespace Prop210BCleanRouteToSourceWitness



end Prop210BCleanRouteToSourceWitness



namespace Prop210CCleanRouteToSourceWitness



end Prop210CCleanRouteToSourceWitness

/-! ## 3. Combined surface -/



namespace Prop210CleanRouteToSourceSurface



end Prop210CleanRouteToSourceSurface

/-! ## 4. Audit -/




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
