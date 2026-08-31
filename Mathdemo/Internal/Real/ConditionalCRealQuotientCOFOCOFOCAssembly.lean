import Mathdemo.Internal.Real.CRealQuotientCOFDecidableOrderAlternative

/-!
# Conditional CReal quotient COFO/COFOC assembly

`ConditionalCRealQuotientCOFRecord` and `CRealQuotientCOFDecidableOrderAlternative` give two conditional ways to obtain a live
`BishopC.COF CRealQuot` record.  This file does not pretend to solve the
remaining analytic obligations.  Instead, it turns the post-COF frontier into
explicit field data:

* `CRealQuotCOFOFieldData cof` is exactly the extra data needed to extend a
  chosen quotient `COF` record to `COFO`;
* `CRealQuotCOFOCFieldData cofo` is exactly the sequential completeness data
  needed to extend that `COFO` record to `COFOC`.

This keeps the proof state honest: the quotient COF forks are now separated
from the stronger order, inverse, Archimedean, and completeness obligations.
-/

namespace BishopCReal

open BishopC
open BishopCRat













end BishopCReal

