import Mathdemo.Internal.Real.NondecidableQuotientCOFOCRouteSelectorData

/-!
# Positive-data inverse consumer without total inverse selection

`NondecidableQuotientCOFOCRouteSelectorData` removed strict-order decidability from the live quotient
`COFOC` route, but it still needed
`CRealQuotPositiveInverseTotalizationData A` because `BishopC.COFO` asks for a
total field

```
inv : CRealQuot -> CRealQuot
```

Bishop's constructive real inverse is not a total computational operation in
that sense: the reciprocal is constructed from positive/apartness data.  This
file therefore records the faithful consumer interface for the quotient
positive inverse: cancellation and positivity are available from
`ltQuotData zeroQuot x`, and from Prop-level positivity only after the
Prop-to-data bridge has supplied such a witness.

No inverse totalization datum is used below.
-/

namespace BishopCReal

open BishopC
open BishopCRat







end BishopCReal

set_option linter.style.longLine false

