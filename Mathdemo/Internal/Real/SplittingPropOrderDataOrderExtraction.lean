import Mathdemo.Internal.Real.RepresentedPositiveShiftsNotGenuineWeakening

/-!
# Splitting Prop-order to data-order extraction

`RepresentedPositiveShiftsNotGenuineWeakening` showed that represented positive shifts are equivalent to a
global representative selector once positive `ltQuotData` is assumed.  The
other remaining extraction problem is the Prop-to-Type bridge from `ltQuot` to
`ltQuotData`.

This file splits that bridge into two explicit ingredients:

* representatives for the compared quotient elements;
* a representative-level extraction from `PosEventually : Prop` to
  `PosEventuallyData : Type`.

The second ingredient is the true Prop-to-data positivity frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat







end BishopCReal

set_option linter.style.longLine false

