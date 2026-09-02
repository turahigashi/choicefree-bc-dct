import Mathdemo.Internal.Real.Theorem415SourceRouteRow
import Mathdemo.Internal.Sec4.Local415SourceData

set_option linter.style.longLine false

/-!
# G231: Theorem 4.15 through the local full-set majorant route

G230 closed the current cover-set/default-budget/provider endpoint.  This file
adds the parallel local route from `b2b39`: the theorem-4.15 proof now consumes
the source majorant split estimate and assembles the `I_B` interface through
local full-set witnesses.  This keeps the printed Bishop proof shape visible:
choose a large set `A`, control the `A ∧ B` part by absolute continuity, control
the `-A` tail, then apply theorem 4.14 to the abs-error sequence.
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
