import Mathdemo.Internal.Real.ConvergenceDataRoutedCanonicalTwoN

set_option linter.style.longLine false

/-!
# G196: separating epsilon schedules from local source witnesses

G195 still packaged two different obligations in one per-dyadic auxiliary datum:
local representative witnesses and the arithmetic choice of a small epsilon.
This file separates them.

The result is a narrower frontier: once an epsilon schedule for the canonical
`n+n` cap and the local good-set witnesses are provided as data, the G195
construction data is generated automatically.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge












end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge





end BishopCReal
