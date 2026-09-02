import Mathdemo.Internal.Real.DownstreamTwoNatRoutePointwiseSeeds

set_option linter.style.longLine false

/-!
# G215: source-level Prop.4.12 wrapper on the no-seed route

G214 removed the pointwise-seed requirement from the downstream two-nat proof.
This increment connects that route back to the source-level data used for
Prop.4.12: constructor sources for the truncated representatives and the
definition-facing characteristic-function witnesses for integrable sets.
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

namespace Prop412AssumptionDischarge

open Proposition412
open Proposition412.TruncatedIntegralBridge
open SourceComplete412



end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge
open BishopRegularSeqChapter4.Prop412AssumptionDischarge







end BishopCReal
