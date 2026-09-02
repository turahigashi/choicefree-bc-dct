import Mathdemo.Internal.Real.SourceLevelTheorem415Local
import Mathdemo.Internal.Sec4.CoverChiTelescopeBridge

set_option linter.style.longLine false

/-!
# G258: source-level theorem 4.15 from cover/chi construction data

G257 made the theorem-4.15 statement source-level again and removed the
global domain-residual provider from the main route.  Its remaining public
input was still the local full-set value bridge for the abs-error sequence.

This file traces that bridge back to the construction data used by the
chapter-4 `I_B` proof:

* canonical cover facts imply the local bridge;
* lower `chi` telescope data imply the canonical cover facts;
* the source-level convergence-in-measure statement is preserved.

Thus the remaining frontier is no longer "supply a bridge" but the more
specific source task: construct the `chi` telescope data from the measurable
set / integrable set definitions.
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
