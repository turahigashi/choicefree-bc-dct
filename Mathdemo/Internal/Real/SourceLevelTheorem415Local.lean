import Mathdemo.Internal.Real.RestoreSourceLevelConvergenceMeasureStatement

set_option linter.style.longLine false

/-!
# G257: source-level theorem 4.15 through local full-set bridges

G256 restored the theorem-4.15 statement shape but still used the global
domain-residual provider as the route for Proposition 4.2 row machinery.
For the previous `IntegrableSet1` API that provider is the dangerous shape: it asks
for global membership-to-domain witnesses for characteristic representatives.

This file keeps the source-level convergence-in-measure statement from G256,
but replaces the provider route by local full-set value bridges.  The remaining
frontier is therefore local and data-carrying, not a global selector.
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
