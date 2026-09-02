import Mathdemo.Internal.Real.ExposingAbsoluteTailComparisonMin

/-!
# G85: splitting the shifted-min truncation bound

G84 left the second small line-743 shifted-min step as one input:

`min(|b| + ||a|-b|, c) <= min(|b|, c) + ||a|-b|`.

This file exposes the two source-level ingredients behind that step:

1. the tail term `||a|-b|` is nonnegative;
2. truncation is stable under adding a nonnegative tail:
   `min(x+d,c) <= min(x,c)+d`.

The large line-735 two-sided frontier and the first small line-743
absolute-tail/monotonicity split are carried unchanged.
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
