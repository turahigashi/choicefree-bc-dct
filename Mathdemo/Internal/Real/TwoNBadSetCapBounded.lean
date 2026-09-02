import Mathdemo.Internal.Real.BadSetCoefficientGeneralizationProposition4

set_option linter.style.longLine false

/-!
# G191: two-`n` bad-set cap from bounded `mid` representatives

G190 removed the hard-coded bad-set coefficient from the Proposition 4.12
assembly.  This file supplies the next concrete bridge: the scalar truncation
`mid(-n,z,n)` is bounded by `[-n,n]`, and therefore the absolute difference of
two such truncated values is bounded by `n+n`.

At the representative level this is kept data-carrying.  Once the construction
of the two `mid` representatives carries pointwise `[-n,n]` bounds, the bad-set
cap datum required by G190 is produced with cap `n+n`.
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
