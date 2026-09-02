import Mathdemo.Internal.Real.OutsideZeroConcreteAbsoluteDifferenceRepresentative

set_option linter.style.longLine false

/-!
# G185: data-carrying bad-set bound budget for Proposition 4.12

G184 derived the outside-`A` zero fact for the concrete absolute-difference
representative from support-carrying mid representatives.  This file isolates
the remaining bad-set estimate as explicit data and proves the source-shaped
strict full-integral estimate once that data and the smallness of `A - E` are
available.

This is intentionally not a hidden choice step: the source's pointwise
`≤ n` estimate on the bad set is now a named datum.
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
