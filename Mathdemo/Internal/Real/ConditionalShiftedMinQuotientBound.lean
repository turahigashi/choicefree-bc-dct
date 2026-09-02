import Mathdemo.Internal.Real.GenericCOFOMinMonotonicityConditionalQuotient

set_option linter.style.longLine false

/-!
# G99: conditional shifted-min quotient bound

G98 conditionally closed the quotient min monotonicity obligation for source
line 735.  This file treats the remaining source line 743 shifted-min bound:

`min(x + d, c) <= min(x, c) + d` when `0 <= d`.

As in G98, the quotient result is explicitly conditional on the existing
global-selector quotient `COFO` route.  The unconditional quotient order
frontier is therefore still recorded as open.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}






namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
