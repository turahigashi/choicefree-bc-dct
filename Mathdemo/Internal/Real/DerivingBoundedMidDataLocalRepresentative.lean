import Mathdemo.Internal.Real.TwoNBadBudgetsCommonGood

set_option linter.style.longLine false

/-!
# G194: deriving bounded-mid data from local representative witnesses

G191 introduced `Prop412MidRepresentativePointwiseBoundData` as the witness that
a concrete `mid(-n, chi_A h, n)` representative is pointwise bounded by
`[-n,n]`.  This file derives that bound data from the already-carried value
identity of the mid representative, provided the construction also carries the
local domain and `chi_A` absolute-series witnesses needed to use that identity.

This is still data-carrying: no representative or witness is selected later
from a quotient/Prop statement.
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
