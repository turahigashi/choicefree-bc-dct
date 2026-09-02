import Mathdemo.Internal.Real.DownstreamProp412BridgeGood

set_option linter.style.longLine false

/-!
# G212: pointwise seed from definition-facing domain witness data

G211 removed the downstream all-`B,C` provider.  The remaining coarse source
was the pointwise seed itself.  This increment refines that source: the common
domain is used only as the point where the comparison is made, while the
absolute-convergence witnesses required by Proposition 4.12 are carried as
definition/constructor data.  In particular, this file does not extract a
`SeriesSum` witness from `IntegrableRep.domain`'s `Nonempty` component.
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
