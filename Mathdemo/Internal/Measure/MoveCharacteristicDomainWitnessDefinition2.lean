import Mathdemo.Internal.Real.RouteRowSeedResidualSurfaceLocal
import Mathdemo.Internal.Sec4.SourceDomainWitness

set_option linter.style.longLine false

/-!
# G281: move the characteristic-domain witness back to Definition 2.3 data

G280 kept the theorem-4.15 route on the source-level local full-set path, but
the row-seed residual surface still carried the positive-side characteristic
absolute-convergence field as an external input.

This node factors that field through the source definition of an integrable
set: an integrable complemented set is one whose characteristic function is an
integrable function on `A.S1 union A.S2`.  Since the current base
`IntegrableSet1` structure has not yet been globally refactored, the source
data is expressed as an explicit compatibility surface over existing
`IntegrableSet1` values.  Downstream theorem-4.15 no longer asks directly for
`chi_abs_on_s1_of_fabs`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Definition-2.3 surface over the current `IntegrableSet1` -/







/-! ## 2. Row-seed provider with the characteristic field discharged -/





end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 3. Theorem 4.15 routed through Definition-2.3 residual data -/






/-! ## 4. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
