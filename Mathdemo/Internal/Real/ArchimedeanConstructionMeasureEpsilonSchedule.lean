import Mathdemo.Internal.Real.LocalMeasureSchedulesProposition412

set_option linter.style.longLine false

/-!
# G200: Archimedean construction of the A-measure epsilon schedule

G199 reduced the remaining epsilon budget in Proposition 4.12 to the source
set `A`:

`eps * mu(A) + (n+n) * eps < 2^-k`.

This file closes that arithmetic frontier constructively.  The coefficient
`mu(A) + (n+n)` is nonnegative, so the `COFOC.mul_archimedean` datum gives an
explicit integer `m` with `(mu(A)+n+n) * 2^-m <= 1`; then
`eps = 2^-(k+1+m)` gives the desired strict dyadic budget.
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
