import Mathdemo.Internal.Real.ReplaceArbitraryRowResidualsSourceShaped

set_option linter.style.longLine false

/-!
# G265: theorem 4.15 through the local split surface

G264 is useful as a diagnostic for the remaining Proposition 4.2 row
components, but its public fields are still not the exact data consumed by the
printed proof of theorem 4.15.

The source proof uses lemma 4.14 through two local ingredients:

* complement bridges for `I_{-C}`;
* the uniform split estimate produced after the majorant set `A` is chosen.

This file exposes that smaller surface directly.  It keeps the theorem-4.15
statement data (`g`, domination, and convergence in measure), but the `I_B`
frontier is no longer an all-measurable-set bridge.  It is the local
split/complement package already used by the completed kernel.

This does not introduce a choice principle.  It narrows the remaining
definition-unfolding responsibility to the two source-shaped local bridge
frontiers.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing theorem 4.15 on the local split surface -/




/-! ## 2. Compatibility from the older all-bridge surface -/



/-! ## 3. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
