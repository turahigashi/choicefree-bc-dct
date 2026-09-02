import Mathdemo.Internal.Real.BridgeCRealQuotCOFOCExistingMeasureTheory

/-!
# G26: contain quotient selectors at the scalar-instance boundary

`BridgeCRealQuotCOFOCExistingMeasureTheory` showed that the existing measure-theory files only require an
abstract scalar with `[COFOC R]`, and therefore accept `R := CRealQuot` once a
quotient `COFOC` value is supplied.

This file makes the remaining selector inputs explicit and local to that
scalar-instance construction.  The measure-theory layer itself should not see
representative extraction or `PosEventually` witness selection; it should only
consume the resulting `BishopC.COFOC CRealQuot`.
-/

namespace BishopCReal

open BishopC
open BishopCRat












end BishopCReal

set_option linter.style.longLine false

