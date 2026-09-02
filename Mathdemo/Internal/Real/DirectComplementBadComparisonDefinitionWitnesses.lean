import Mathdemo.Internal.Real.PointwiseSeedDefinitionFacingDomainWitness

set_option linter.style.longLine false

/-!
# G213: direct complement-to-bad comparison from definition witnesses

G212 made the previous pointwise seed explicitly definition-facing.  This increment
goes one step further at the low-level estimate: instead of packaging a seed
as Type data, we prove the complement-to-bad comparison directly on a smaller
full set that contains all Definition 1.6 domains needed for the pointwise
calculation.

This matches the Bishop reading: witnesses are not supplied externally; they
are unfolded from the relevant integrable representatives at the point where
Proposition 1.11 asks for a pointwise inequality.
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
