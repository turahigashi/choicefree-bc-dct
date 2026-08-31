import Mathdemo.Internal.Real.SplittingPositiveInverseDataTotalInverse

/-!
# Data-valued quotient COF order layer

`SplittingPositiveInverseDataTotalInverse` separated the positive inverse laws from total inverse
selection.  The remaining strict-order-decidability dependency now lives in the
order interface: the live `BishopC.COF` class stores `lt` as a `Prop`, but also
asks for a Type-valued cotransitivity split.

This file records the alternative order encoding explicitly.  If the quotient
order is carried as data, cotransitivity and add-left transport are already
constructive under representative supply.  The Prop-to-data bridge is needed
only when converting this data-valued order layer back to the live `COF`
interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat









end BishopCReal

set_option linter.style.longLine false

