import Mathdemo.Internal.Real.RepresentativeDiagonalLimitCloseData

/-!
# Representative-free decidable-order COFO assembly

`RepresentativeDiagonalLimitCloseData` closed the representative-carrying diagonal limit closure data.
This file returns to the non-completeness `COFO` layer and removes the global
representative selector from that assembly path.

The price is explicit: this branch still assumes decidability of quotient
strict order, and the positive inverse still consumes `ltQuotData` for positive
inputs.  The point closed here is narrower: all non-completeness `COFO` fields
can be packaged for the decidable-order `COF` without a global
`rep : forall x, CRealQuotRepWitness x`.
-/

namespace BishopCReal

open BishopC
open BishopCRat
















end BishopCReal

