import Mathdemo.Internal.Real.UnbundleTheorem415S2Provider

set_option linter.style.longLine false

/-!
# G246: theorem 4.15 from local full-set value bridges

G245 exposed the bundled S2 provider into five lower components.  Inspecting
those components shows that the previous `charDomain` field is still the dangerous
shape: it asks for a global map from membership in `A.S1`/`A.S2` to pointwise
absolute-convergence witnesses for the characteristic representative.

This file routes theorem 4.15 through the local full-set interface directly.
The public input is not a global membership-to-witness selector; it is only the
local value bridge for the theorem-4.15 error sequence.  The bridge itself is
the remaining lower construction target, but the 4.15 theorem no longer needs
the global `Sec4GeneralIBSourceS2StandardOuterProvider` or its `charDomain`
component.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route














end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
