import Mathdemo.Internal.Real.SplittingSmallLine743SubSeqCore

/-!
# G84: exposing the absolute-tail comparison under `min`

G83 split the small line-743 core through

`min(|b| + ||a|-b|, c)`.

This file splits the first half of that chain again.  The input

`min(|a|,c) <= min(|b| + ||a|-b|, c)`

is now obtained from a bare absolute-tail comparison

`|a| <= |b| + ||a|-b|`

and a left-monotonicity law for `minSeqWith`.  The second shifted-min
truncation bound remains the next small frontier.
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
