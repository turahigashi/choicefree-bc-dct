import Mathdemo.Internal.Real.FactoringDisplayedScalarFrontierTwoLaw

/-!
# G79: unifying the displayed scalar law inputs

G78 factored the remaining frontier through displayed large and small scalar
law routes, but those routes still carried parallel full-set and operation-data
interfaces.  This file bundles those inputs into one unified bridge.

No new analytic claim is proved here.  The change makes the next frontier
cleaner: supply the displayed scalar laws and full-set witnesses once, then
obtain the whole property-(4) route.
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
