import Mathdemo.Internal.Real.ExplicitAdapterBoundaryPreviousQuotientCOFOC

/-!
# Final source-shaped RegularSeq COFOC surface

`ExplicitAdapterBoundaryPreviousQuotientCOFOC` isolated the previous quotient route as an explicit adapter
boundary.  This file gives the constructive CReal route a single surface
object: the carrier is `RegularSeq`, equality is Bishop equality, strict order
and positivity are data-carrying, and inverse is indexed by positive data.

This is intentionally not a live `BishopC.COFOC RegularSeq` instance.  The old
typeclass uses Lean's structural equality and a total inverse field, while the
source-shaped real interface uses the implementation setoid and data-indexed
reciprocal.
-/

namespace BishopCReal

open BishopC
open BishopCRat





end BishopCReal

set_option linter.style.longLine false

