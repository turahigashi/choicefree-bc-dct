import Mathdemo.Internal.Real.Chapter4RouteReachesTheorem4

set_option linter.style.longLine false

/-!
# G229: Theorem 4.15 through the source cover-set route

G228 connected the already verified theorem-4.15 endpoint, but still consumed
the bundled `Lemma415IBUniformFrontierData`.  This file moves one step closer to
the printed proof: the uniform relative-integral control is obtained from the
source cover-set/tail construction for the dominating function `g`.

The remaining work is not hidden.  To obtain the plain textbook statement, the
fields of `Theorem415CoverSetSourceData` still have to be derived from the
definitions of integrable functions, convergence in measure, and the pointwise
domination hypothesis.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route









end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
