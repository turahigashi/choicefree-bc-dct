import Mathdemo.Internal.Real.ArbitrarySmallEstimatesImplyTruncatedIntegral

set_option linter.style.longLine false

/-!
# G187: source budgets generate the arbitrary-small data in Proposition 4.12

G186 used an explicit "arbitrarily small integral" datum.  This file lowers
that datum to the source-shaped objects used in G185: for each dyadic target,
one supplies a good set, pointwise closeness on that good set, a bad-set budget,
and the arithmetic inequality putting the resulting bound below the target.

This keeps the proof data-carrying while making clear what still remains to be
derived from the original measure-convergence hypotheses.
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
