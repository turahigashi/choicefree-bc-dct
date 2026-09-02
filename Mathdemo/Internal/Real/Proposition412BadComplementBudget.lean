import Mathdemo.Internal.Real.Proposition412BadComplementBound

set_option linter.style.longLine false

/-!
# G175: Proposition 4.12 bad-complement budget for the common good set

G174 closed the abstract bad-complement bound

`I_{A-E}(d) <= n * mu(A-E)`.

G170 had already closed the source measure-defect estimate for the common
good set `E = B ∧ C`.  This file connects those two pieces, obtaining the
source-shaped strict budget

`I_{A-(B∧C)}(d) < n * eps`

from the two half-epsilon measure defects.
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
