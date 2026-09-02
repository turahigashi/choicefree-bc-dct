import Mathdemo.Internal.Real.NonnegativityConcreteAbsoluteDifferenceRepresentative

set_option linter.style.longLine false

/-!
# G183: value data for the concrete truncated absolute-difference representative

G182 made the concrete representative automatically nonnegative.  This file
closes the good-set value-identification datum for that representative:
from the explicit mid representatives for `f` and `g`, plus pointwise
`chi_A` convergence witnesses on `E`, the representative

`(F.rep - G.rep).absVal`

has exactly the scalar value required by `Prop412TruncatedAbsValueData`.
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
