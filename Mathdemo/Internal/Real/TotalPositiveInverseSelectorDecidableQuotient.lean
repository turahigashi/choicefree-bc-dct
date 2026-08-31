import Mathdemo.Internal.Real.PositiveQuotientInverseExplicitOrderData

/-!
# Total positive-inverse selector under decidable quotient order

`PositiveQuotientInverseExplicitOrderData` defines the inverse of a positive quotient element when explicit
order data is supplied.  A live `COFO.inv` field is total, so this file isolates
one honest way to obtain a total selector: assume the quotient strict order is
decidable and keep the existing `ltQuot → ltQuotData` extraction parameter.

This is still a conditional selector, not the final Bishop-real inverse laws.
The cancellation and positivity laws require separate quotient estimates.
-/

namespace BishopCReal

open BishopC
open BishopCRat









end BishopCReal

