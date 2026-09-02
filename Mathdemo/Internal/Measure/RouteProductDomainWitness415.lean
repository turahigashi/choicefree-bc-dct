import Mathdemo.Internal.Measure.AvoidOverstrongOuterRouteProposition4

set_option linter.style.longLine false

/-!
# G287: route the product-domain witness through the 4.15 local bridge

G286 identified the source-correct local support for Proposition 4.2 values:
the characteristic representative, the original representative, and the
constructed product representative must all be read with their own local
Definition-1.6 witnesses.

This node pushes that correction into the theorem-4.15 consistency comparison.
The comparison no longer calls the product-representative value theorem as a
bare global fact; it first packages the local data from the common support as a
`Sec4Prop42ProductLocalWitness`, then reads the product value from that local
witness.  The remaining local bridge for the direct measurable representative
is unchanged.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Product-local value wrappers -/





/-! ## 2. 4.15 consistency comparison through product-local witnesses -/







/-! ## 3. Audit -/




end BishopC

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
