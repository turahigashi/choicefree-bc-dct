import Mathdemo.Internal.Real.PosEventuallyWitnessSelectorFrontier

/-!
# COFOC assembly from global reps and a PosEventually selector

`PosEventuallyWitnessSelectorFrontier` exposed the remaining positivity bridge as a selector for the
`k, N` witnesses inside `PosEventually`.  This file threads that selector
through the localized positive-order-data branch from `LocalizingOrderDataExtractionPositiveInverse` through
`COFOCAssemblyAfterPositiveOrderData`.

The result is an audit package, not a new construction of the selector or of
strict-order decidability: in the current decidable-order branch, global
representatives plus a `PosEventually` selector are enough to supply the
positive `ltQuotData` consumed by the positive inverse and hence the existing
`COFOC` assembly route.
-/

namespace BishopCReal

open BishopC
open BishopCRat








end BishopCReal

set_option linter.style.longLine false

