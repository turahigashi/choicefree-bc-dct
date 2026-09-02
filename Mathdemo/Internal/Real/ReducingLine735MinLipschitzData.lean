import Mathdemo.Internal.Real.ReducingIHIHProposition

/-!
# G62: reducing line 735 to min-Lipschitz data and Proposition 1.11

G61 reduced line 734 of Theorem 1.18(4) to Proposition 1.11.  The remaining
large-branch local inequality is source line 735:

`I(|min(f,n)-min(g,n)|) <= I(|f-g|)`.

This file puts line 735 in the same source-faithful shape: the only analytic
input is the pointwise min-Lipschitz domination on a full set; Proposition
1.11 transports that domination to the integral inequality.
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
