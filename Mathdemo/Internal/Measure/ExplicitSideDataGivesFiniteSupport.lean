import Mathdemo.Internal.Measure.SourceRowsRawSubtractionsCleanRows

set_option linter.style.longLine false

/-!
# G315: explicit side data gives finite-support clean majorants

This node stays on the rep-carrying route rooted at `SourceRowsRawSubtractionsCleanRows`.

It records the part of the clean-characteristic route that is already available
from G308--G312: explicit rowwise side data plus an explicit final-side case
gives the finite-support pointwise flattenability needed by `rowToFlat`.

It deliberately does not claim an unconditional construction of
`CleanCharacteristicRep` for the clean set-difference rows.  The current public
API gives the clean rows as `IntegrableSet1_sub`/`min2` representatives, but it
does not expose the representative-level zero bound

```
  RepAbsBound row x 0
```

on the negative side.  That bound is exactly the remaining clean-row frontier.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Final side data without extracting witnesses from membership -/





namespace UnionSideData





end UnionSideData

namespace InterSideData





end InterSideData

/-! ## 2. Public wrappers named for the Prop.2.10 route -/









/-! ## 3. Audit -/




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
