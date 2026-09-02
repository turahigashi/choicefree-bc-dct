import Mathdemo.Internal.Real.Theorem415GenericCaseTools
import Mathdemo.Internal.Sec4.AbsOuterPack

set_option linter.style.longLine false

/-!
# G250: theorem 4.15 from corrected abs-outer pack tools

G249 routed theorem 4.15 through function-side case tools.  The chapter-4
development has a corrected, lower interface for those tools:
`Sec4ChiFCaseAbsPackTools`.  This interface uses the abs-outer row sum required
by `seriesSumRep_L1` flat absolute convergence, avoiding the earlier
signed-outer design bug.

This file exposes the theorem-4.15 endpoint from that corrected abs-outer
package.  It keeps the set-side data definitional: cover/difference dichotomy
is still built from `IntegrableSet1.valid` downstream.
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
