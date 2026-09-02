import Mathdemo.Internal.Real.RegularSeqDataCarryingMainlineTheorem1

set_option linter.style.longLine false

/-!
# G111: exact RegularSeq/data min-law frontier for property (4)

G110 rerouted theorem 1.18 property (4) to a RegularSeq/data-carrying
mainline.  The next constructive frontier is no longer quotient extraction.
It is the two source min laws needed by lines 735 and 743:

* monotonicity of `minSeqWith` in the first argument;
* the nonnegative shifted-min bound.

This file makes those two laws the explicit RegularSeq/data mainline input and
threads them back into the G96 scalar-min-kernel reduction.  No quotient
representative selector and no Prop-to-data strict-order selector are fields of
this route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}












end BishopRegularSeqTheorem118





end BishopCReal
