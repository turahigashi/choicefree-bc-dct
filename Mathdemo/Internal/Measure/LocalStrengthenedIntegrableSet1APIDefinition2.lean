import Mathdemo.Internal.Measure.RouteProductDomainWitness415

set_option linter.style.longLine false

/-!
# G288: local strengthened `IntegrableSet1` API for Definition 2.3 data

G287 still consumed the global compatibility surface
`IntegrableSet1Def23Surface`.  Source Definition 2.3 says more locally: an
integrable complemented set is carried by its own characteristic-function
representative, defined on `A.S1 union A.S2` and equal to `1` on `A.S1`, `0`
on `A.S2`.

This node introduces the local strengthened API that the later broad refactor
should migrate into `IntegrableSet1` itself.  The theorem-4.15 consistency
bridge can now be stated from one strengthened integrable set `C`, rather than
from a global external surface for all current `IntegrableSet1` values.

This is a staging step, not a claim that all Chapter-2 constructors have already
been migrated to the strengthened API.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local Definition-2.3 strengthened integrable set -/



namespace IntegrableSet1WithDef23



end IntegrableSet1WithDef23

/-! ## 2. Product-local witnesses from one strengthened set -/





/-! ## 3. Product value identification from one strengthened set -/





/-! ## 4. 4.15 consistency comparison from one strengthened set -/







/-! ## 5. Audit -/




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
