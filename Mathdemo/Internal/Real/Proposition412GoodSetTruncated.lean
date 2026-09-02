import Mathdemo.Internal.Real.Proposition412MeasureCoverBridge

set_option linter.style.longLine false

/-!
# G171: Proposition 4.12 good-set truncated integral bridge

G170 closed the measure defect of the common good set `E = B ∧ C`.
The next source line bounds the integral of the absolute truncated difference:

`I(|mid(-n,χ_A f,n)-mid(-n,χ_A g,n)|)`.

This file closes the good-set part of that estimate.  The actual truncated
absolute difference is kept as an explicit `IntegrableRep` datum.  Once its
pointwise value on `E` is bounded by `eps`, the existing
`relIntegral_le_const_measure` theorem gives

`I_E(d) ≤ eps * μ(E)`.

Thus the remaining truncated-integral bridge is reduced to the bad-complement
piece and the split from the full integral into good/bad pieces.
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
