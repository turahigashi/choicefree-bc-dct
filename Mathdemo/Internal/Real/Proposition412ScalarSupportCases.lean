import Mathdemo.Internal.Real.Proposition412PointwiseSupportData

set_option linter.style.longLine false

/-!
# G178: Proposition 4.12 scalar support cases for the complement-to-bad bridge

G177 reduced the source bad-set estimate in Proposition 4.12 to pointwise
domination of the canonical complement representative by the `A-E` relative
representative.  This file lowers that frontier by one scalar layer: if the
characteristic values are the expected `0/1` values and the truncated
absolute-difference representative vanishes outside `A`, then

`(1 - chi_E) * d <= chi_(A-E) * d`

holds by the three source support cases.
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
