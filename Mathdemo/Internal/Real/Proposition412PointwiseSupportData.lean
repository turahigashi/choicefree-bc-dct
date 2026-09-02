import Mathdemo.Internal.Real.Proposition412ComplementBadSplit

set_option linter.style.longLine false

/-!
# G177: Proposition 4.12 pointwise support data to complement-to-bad data

G176 isolated the support frontier needed to replace the canonical complement
term `I_{-E}(d)` by the source bad-set term `I_{A-E}(d)`.

This file lowers that frontier one level: it is enough to provide pointwise
domination of the complement representative by the `A-E` relative-integral
representative on their common full domain.  Proposition 1.11 then turns that
pointwise domination into the integral inequality required by G176.
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
