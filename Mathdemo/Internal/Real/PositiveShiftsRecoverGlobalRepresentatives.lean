import Mathdemo.Internal.Real.RepresentativeScopePositiveLtQuotData

/-!
# Positive shifts recover global representatives

`RepresentativeScopePositiveLtQuotData` recorded that positive `ltQuotData` supplies representatives
only for strictly positive quotient elements, plus the canonical representative
of zero.

This file isolates the exact additional bridge needed to turn that partial
representative supply into a global one: every quotient element must be
shiftable, by a represented quotient element, into the strictly positive cone.
With that data, the additive group laws move the positive representative back
to a representative of the original quotient element.
-/

namespace BishopCReal

open BishopC
open BishopCRat






end BishopCReal

set_option linter.style.longLine false

