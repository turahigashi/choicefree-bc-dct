import Mathdemo.Internal.Real.ExpandingLargeLine735MinTerms

/-!
# G77: replacing tail representatives by displayed PFun approximants

G76 displayed the large line-735 min terms, while the right tail still used
`approximant_rep N`.  G75 left the same representative-level trace in the
small absolute tail.

This file replaces those tail representatives by their displayed old-space
PFun approximants.  After this layer, the remaining pointwise source
inequalities are expressed entirely in terms of `f`, `|f|`, and the displayed
Corollary 1.17 approximants `g_N`.
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
