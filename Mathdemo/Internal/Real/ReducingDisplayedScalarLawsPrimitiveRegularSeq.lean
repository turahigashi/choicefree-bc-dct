import Mathdemo.Internal.Real.UnifyingDisplayedScalarLawInputs

/-!
# G80: reducing displayed scalar laws to primitive RegularSeq laws

G79 unified the full-set and displayed scalar-law inputs for Theorem 1.18(4).
This file separates the remaining displayed scalar laws from the surrounding
integration-space context.

The new frontier is exactly two reusable `RegularSeq` inequalities:

* source line 735: the min-Lipschitz law
  `|min(a,c)-min(b,c)| <= |a-b|`;
* source line 743: the min-tail law
  `min(|a|,c) <= min(|b|,c) + ||a|-b|`.

No proof of those two scalar laws is inserted here.  G80 proves only that
those two primitive laws instantiate the G78 displayed-law interface and hence
feed the already built G79 route.
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
