import Mathdemo.Internal.Measure.BoundedRowAPICleanProposition2

set_option linter.style.longLine false

/-!
# G307: clean side-classified rows

G306 fixed the bounded-row target.  This node adds the generic constructor that
will produce those bounded rows from clean characteristic representatives plus
Type-coded side classification.  The induced majorant is the `0/1` side
majorant: `1` on rows where `x` is on the positive side of the clean increment,
`0` on rows where it is on the negative side.

The remaining Proposition-2.10 task is now specifically to construct the
side-classification data and prove its `0/1` majorant is summable, which is the
finite-support/eventual-zero part of the source proof.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Generic clean classified rows -/







namespace CleanSideClassifiedRows



end CleanSideClassifiedRows

/-! ## 2. Proposition-2.10 clean classified-row surfaces -/



namespace Prop210BCleanClassifiedRowsWitness



end Prop210BCleanClassifiedRowsWitness



namespace Prop210CCleanClassifiedRowsWitness



end Prop210CCleanClassifiedRowsWitness

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
