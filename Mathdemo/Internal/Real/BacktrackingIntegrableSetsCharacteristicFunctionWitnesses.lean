import Mathdemo.Internal.Real.SourceProofFriendlyRealSetInterface

set_option linter.style.longLine false

/-!
# G210: backtracking integrable sets to characteristic-function witnesses

This increment implements the selected definitional backtracking direction:

`A` is an integrable set, so its characteristic function is an integrable
function; an integrable function carries the Definition 1.6 representative
data; Proposition 4.12 should use that carried data, not a later choice of a
representative.

The previous `BishopC.IntegrableSet1` already contains the Definition 1.6
representative as `hA.rep`, but it does not expose the source-forward
membership-to-pointwise-absolute-convergence direction.  We therefore name the
missing direction as part of the definition-facing set layer, and connect it to
the G209 Prop.4.12 source interface.  For the newer RegularSeq Chapter 2 layer,
the same direction follows directly from `domain_eq` plus the Definition 1.6
value law's `abs_from_domain` field.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Prop412AssumptionDischarge

open Proposition412
open Proposition412.TruncatedIntegralBridge
open SourceComplete412







end Prop412AssumptionDischarge
end BishopRegularSeqChapter4

namespace BishopRegularSeqChapter2

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqChapter2

open BishopRegularSeqChapter4.Prop412AssumptionDischarge







end BishopCReal
