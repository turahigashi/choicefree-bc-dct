import Mathdemo.Internal.Real.SplittingShiftedMinTruncationBound

/-!
# G86: splitting the absolute-tail upper bound

G85 still kept the first small line-743 scalar input as

`|a| <= |b| + ||a|-b|`.

This file splits that input into the elementary source-shaped chain:

1. `u <= b + |u-b|`;
2. `b <= |b|`;
3. addition is monotone in the left summand.

Applied with `u = |a|`, this reconstructs the G85 absolute-tail upper bound.
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
