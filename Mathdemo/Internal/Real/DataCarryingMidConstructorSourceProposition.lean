import Mathdemo.Internal.Real.ArchimedeanConstructionMeasureEpsilonSchedule

set_option linter.style.longLine false

/-!
# G201: data-carrying mid constructor source for Proposition 4.12

G200 closed the Archimedean epsilon schedule.  The remaining source-faithful
frontier is the actual `mid(-n, chi_A h, n)` constructor.

The previous `BishopSec4_Convergence.IsMeasurable` interface is Prop/existential and
the helper `prop_4_4_min_chi_f` extracts representatives with
`choice witness selector`.  This file therefore does not use that path.  Instead it
names the Bishop-style source datum: the representative and the local witnesses
needed to read its pointwise value are carried from the start.  From that datum
we construct the existing full-support shape used by the G200 Prop. 4.12 bridge.
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
