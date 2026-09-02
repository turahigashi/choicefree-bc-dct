import Mathdemo.Internal.Real.SourceBudgetsGenerateArbitrarySmallData

set_option linter.style.longLine false

/-!
# G188: common-good source data produce dyadic source budgets

G187 reduced the arbitrary-small equality step to per-dyadic source budgets.
This file connects those budgets to the already formalized Proposition 4.12
common-good pair: the `B,C,N` data obtained from convergence in measure.

The remaining source frontiers are therefore explicit:

* provide the common-good data for every dyadic target without extracting it
  from a `Prop`-valued existential by choice;
* prove or correct the bad-set `<= n` bound.
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
