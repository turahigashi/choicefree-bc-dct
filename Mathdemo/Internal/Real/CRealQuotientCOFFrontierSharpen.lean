import Mathdemo.Internal.Real.ConditionalCRealQuotientCOFRecord

set_option linter.unusedVariables false

/-!
# CReal quotient COF frontier sharpen

`ConditionalCRealQuotientCOFRecord` exposes two remaining inputs before the conditional quotient
`COF` package can become unconditional:

* representative extraction for quotient elements;
* conversion from the current Prop-valued quotient order to the data-valued
  quotient order.

An attempted direct closure of the first item by
`Quotient.inductionOn : (x : CRealQuot) → CRealQuotRepWitness x` is rejected by
Lean as an invalid motive: this would eliminate a quotient into a Type-valued
dependent witness carrying an equality to a chosen representative.  Thus this
file records the sharpened frontier without pretending that representative
extraction has been closed.
-/

namespace BishopCReal

open BishopC
open BishopCRat







end BishopCReal

