import Mathdemo.Internal.Measure.Section4DataCarryingRemainderAudit

set_option linter.style.longLine false

/-!
# Stage A12: data-carried measurability frontier for 4.6/4.7

This additive node keeps the previous `PFunR`/`IsMeasurable` stub out of the route.
It records Bishop 4.6 measurability as Type-carried cutoff representatives over
`DataPFunR`.

The full bound-only 4.6 statement is still a frontier in the current library:
`thm_4_13_monotone_convergence_faithful` requires a `TendstoHalf` witness for
the cutoff integrals, while the 4.6 hypothesis supplies only an upper bound.
This file therefore exposes the exact MCT kernel and the extra data still
needed to turn the bound-only statement into the final theorem.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}




















end BishopC
