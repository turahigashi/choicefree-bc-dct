import Mathdemo.Internal.Real.DecidableTotalizationBranchPreviousQuotientRoute
import Mathdemo.Internal.BishopSec5_Measure

/-!
# G25: bridge from CRealQuot COFOC to the existing measure-theory interface

The constructive measure-theory files are written over an abstract scalar
`R` with `[BishopC.COFOC R]`.  Therefore the compatibility target for the
constructed Bishop real is the quotient presentation `CRealQuot` equipped with
`BishopC.COFOC CRealQuot`.

This file does not change the measure-theory development.  It records that,
once the quotient `COFOC` value is supplied by either explicit adapters or the
decidable-totalization branch, the existing `BishopD.MeasureSpace` and
`BishopD.SimpleFunction` interfaces can be specialized to `CRealQuot`.
-/

namespace BishopCReal

open BishopC
open BishopCRat











end BishopCReal

set_option linter.style.longLine false

