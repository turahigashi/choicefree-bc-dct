import Mathdemo.Internal.Measure.UseDefinition23DataSource

set_option linter.style.longLine false

/-!
# G283: recover Proposition-4.2 local rows from Definition 2.3

G282 exposed a useful diagnostic: the previous global `RowsOnS2` surface is too
strong if it is read as a map from `x in A.S2` alone to row witnesses for an
arbitrary integrable representative `f`.  The rows also need the local
Definition-1.6 witness for `f`.

This node records the source-faithful local direction.  Definition 2.3 supplies
the characteristic-function side of the local witness; the integrable
representative supplies the `f` side on its own full domain.  The standard
Proposition-4.2 lambda rows are then constructed from those two pieces.

This does not add a choice principle.  It prevents the later proof from hiding
one by asking for global membership-to-witness maps.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local witnesses from Definition 2.3 plus the `f` domain -/





/-! ## 2. Standard rows on the local full support -/





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
