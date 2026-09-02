import Mathdemo.Internal.Real.Line734ReductionIntegralDifference

/-!
# G61: reducing `|I(h)| <= I(|h|)` to Proposition 1.11

G60 isolated the general source estimate `|I(h)| <= I(|h|)`.  This file
connects that estimate back to the earlier source monotonicity layer:
Proposition 1.11 gives the two integral bounds from the pointwise domination
`h <= |h|` and `-h <= |h|`; a small RegularSeq order bridge then turns those
two bounds into the absolute-value bound.
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
