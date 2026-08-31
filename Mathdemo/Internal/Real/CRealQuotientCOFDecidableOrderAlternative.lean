import Mathdemo.Internal.Real.CRealQuotientCOFFrontierSharpen

/-!
# CReal quotient COF via a decidable-order alternative

`CRealQuotientCOFFrontierSharpen` sharpened the two extraction frontiers for the quotient route.
There is a second, logically distinct way to satisfy the live
`BishopC.COF.lt_cotrans_data` field: if the quotient strict order itself is
decidable, the existing Prop-valued cotransitivity

```
ltQuot a b → ltQuot a c ∨ ltQuot c b
```

can be converted into the Type-valued split by deciding the left branch.

This file packages that alternative.  It is not claimed as the Bishop-real
solution: decidability of strict order is much stronger than Bishop-style
apartness data.  The point is to isolate the exact fork:

* either provide Type-level order/representative data, as in `ConditionalCRealQuotientCOFRecord`; or
* provide a decidable strict order, as in this conditional package.
-/

namespace BishopCReal

open BishopC
open BishopCRat








end BishopCReal

