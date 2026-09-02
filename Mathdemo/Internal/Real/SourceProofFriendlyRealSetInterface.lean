import Mathdemo.Internal.Real.SplittingRemainingLocalWitnessLawProposition

set_option linter.style.longLine false

/-!
# G209: source-proof friendly real/set interface for Proposition 4.12

The issue after G208 is whether a class of reals should be used that lets the
Bishop--Cheng source proof be formalized closer to the way it is written.

This file records the answer at the formal interface level.  A scalar `COFOC`
class alone is not the main issue.  The source proof also treats integrable
sets as characteristic representatives whose values can be read at points of
the set.  The previous `IntegrableSet1.valid` direction is weaker for Lean: it says
that if an absolute-convergence witness is already available, then membership
and characteristic values follow.  The source-style direction needed in
Prop.4.12 is the forward datum from membership to the representative's
absolute-convergence witness.

G209 therefore names this source-level data and shows that the first G208
obligation, `chi_A` absolute convergence on the common good set, follows from
it and the good-pair subset information in Definition 4.11.
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

open BishopRegularSeqChapter4.Prop412AssumptionDischarge





end BishopCReal
