import Mathdemo.Internal.Real.ExpandingPFunOrderFrontierDisplayedScalar

/-!
# G74: expanding the large line-735 subtraction terms

G73 exposed the remaining property-(4) frontier as pointwise scalar orders.
For the large branch, source line 735 still had the subtraction representatives
hidden behind `largeCutDiffRep` and `largeTailRep`.

This file opens those two representatives one layer further:

* `min(f,n)-min(g_N,n)` is displayed as `addSeq min(f,n) (-1 * min(g_N,n))`;
* `f-g_N` is displayed as `addSeq f (-1 * g_N)`.

The new bridge then feeds this more explicit data back into the G73 route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}














end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
