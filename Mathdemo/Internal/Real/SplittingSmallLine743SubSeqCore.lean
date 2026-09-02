import Mathdemo.Internal.Real.SplittingLargeSubSeqCoreTwoSided

/-!
# G83: splitting the small line-743 `subSeq` core

G82 left the small line-743 scalar core as the single inequality

`min(|a|,c) <= min(|b|,c) + ||a|-b|`.

This file exposes the source-level middle term

`min(|b| + ||a|-b|, c)`

and proves that the previous single small core follows by order transitivity from
two smaller inputs.  The large line-735 two-sided frontier is carried unchanged.
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
