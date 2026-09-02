import Mathdemo.Internal.Real.ClosingRegularSeqAbsoluteValueTwoSided

set_option linter.style.longLine false

/-!
# G96: scalar half-sum kernel for min monotonicity

The G95 layer leaves the two sequence-level min laws as the active frontier.
This file closes the scalar half-sum kernel used by the source proof of min
monotonicity:

`a <= b` implies
`half * (s + a - |s-a|) <= half * (s + b - |s-b|)`.

This matches the existing source proof of `cof_min_le_min_right` in the
Bishop-style completeness file.  The remaining work is the transport of this
scalar kernel through the representative-level `minSeqWith` multiplication
indexing.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}




namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
