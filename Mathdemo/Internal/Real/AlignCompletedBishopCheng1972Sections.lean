import Mathdemo.Internal.Real.BishopFaithfulMeasureSkeletonRegularSeqReals

/-!
# G30: align completed Bishop-Cheng (1972) sections 1--4 with the Bishop-faithful route

Bishop-Cheng (1972) sections 1--4 are treated here as the completed
formalization scope.  This file does not reopen that work.  It records how the
completed files relate to the regular-sequence route:

* existing section-1--4 Lean artifacts over `[COFOC R]` are retained as
  relative formalization theorems;
* the Bishop-real concrete route is not the previous quotient/structural-equality
  route;
* future Bishop-real interpretation should target the RegularSeq-valued
  partial-function and integration skeletons introduced in `BishopFaithfulRegularSeqValuedInterface` and
  `BishopFaithfulMeasureSkeletonRegularSeqReals`.
-/

namespace BishopCReal

open BishopC
open BishopCRat












end BishopCReal

set_option linter.style.longLine false
