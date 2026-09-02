import Mathdemo.Internal.Real.BacktrackingIntegrableSetsCharacteristicFunctionWitnesses

set_option linter.style.longLine false

/-!
# G211: downstream Prop.4.12 bridge with good-pair-scoped witnesses

G210 made the `chi_A` witness source definitional.  This increment removes the
next mismatch: the downstream truncated-integral bridge no longer has to ask
for local witnesses for every arbitrary pair `B,C`.  The source proof only
needs witnesses for the good pair returned by convergence, and
`Prop412CommonGoodPair` already contains the subset information
`B¹ ⊆ A¹`, `C¹ ⊆ A¹`.
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
