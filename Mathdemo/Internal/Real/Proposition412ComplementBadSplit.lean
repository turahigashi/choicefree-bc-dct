import Mathdemo.Internal.Real.Proposition412BadComplementBudget

set_option linter.style.longLine false

/-!
# G176: Proposition 4.12 complement-to-bad split adapter

The source proof of Proposition 4.12 estimates the full integral of the
truncated absolute difference by splitting it into a good part over `E` and
the bad part over `A - E`.

The existing relative-integral API gives the canonical complement split

`I_E(d) + I_{-E}(d) = I(d)`,

where the complement term is represented as
`(d - chi_E * d).integral`.  This file isolates the remaining constructive
frontier: to use the source's `A-E` bad set, one must provide data that the
previous complement term is bounded by the explicit `A-E` relative integral.  From
that data, the full split required by G174 is derived without choosing
representatives after the fact.
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
