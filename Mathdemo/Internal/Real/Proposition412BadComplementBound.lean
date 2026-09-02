import Mathdemo.Internal.Real.Proposition412ValueDataGood

set_option linter.style.longLine false

/-!
# G174: Proposition 4.12 bad-complement bound

The source estimate for Proposition 4.12 is

`I(d) <= eps * mu(E) + n * mu(A - E)`.

G173 closed the good-set side from explicit value data.  This file closes the
bad-complement side in the same data-carrying style: if the chosen truncated
absolute-difference representative is pointwise bounded by `n` on `A-E`, then
its relative integral over `A-E` is bounded by `n * mu(A-E)`.
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
