import Mathdemo.Internal.Measure.LocalStrengthenedIntegrableSet1APIDefinition2

set_option linter.style.longLine false

/-!
# G289: forward domain and absolute-convergence transport for constructor migration

G288 fixed the target local API for Definition 2.3 data.  The next broad task
is migrating the Chapter-2 constructors, starting with the source equation
`chi_{A vee B} = chi_A + chi_B - chi_{A wedge B}`.

This node adds only the generic transport lemmas needed for that migration:
if the input representatives have local domain / absolute convergence at a
point, then the composite representatives built by `add`, `neg`, `sub`,
`smul`, `absVal`, and `min2` have the corresponding local data.  No new
analytic assumption or choice principle is introduced.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Forward domain transport -/













/-! ## 2. Forward absolute-convergence transport -/











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
