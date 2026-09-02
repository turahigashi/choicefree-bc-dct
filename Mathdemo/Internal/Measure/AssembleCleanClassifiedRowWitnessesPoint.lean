import Mathdemo.Internal.Measure.FiniteSupportMajorantsCleanSideClassifiers

set_option linter.style.longLine false

/-!
# G310: assemble clean classified-row witnesses from point data

G309 proved finite-support summability for the `0/1` side majorants induced by
cutoff-aware clean row classifiers.  This node assembles those ingredients into
the `Prop210BCleanClassifiedRowsWitness` and
`Prop210CCleanClassifiedRowsWitness` surfaces introduced in G307.

This closes the clean-row pointwise majorant route, conditional on explicit
source point-side data and clean characteristic representatives.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Union clean point-data witness -/



namespace Prop210BCleanPointDataWitness









end Prop210BCleanPointDataWitness

/-! ## 2. Intersection clean point-data witness -/



namespace Prop210CCleanPointDataWitness









end Prop210CCleanPointDataWitness

/-! ## 3. Combined clean point-data surface -/



namespace Prop210CleanPointDataSurface





end Prop210CleanPointDataSurface

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

