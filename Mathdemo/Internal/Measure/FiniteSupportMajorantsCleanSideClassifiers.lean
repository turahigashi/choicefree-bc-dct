import Mathdemo.Internal.Measure.ConcreteSideClassifiersPointwiseSideData

set_option linter.style.longLine false

/-!
# G309: finite-support majorants for clean side classifiers

G308 constructed row side classifiers from explicit source-row side data.  This
node adds cutoff-aware versions for the four Proposition-2.10 final sides and
proves that the induced `0/1` row majorants are summable by eventual zero.

The key point is that the inside union and outside intersection cases use an
explicit hit index; they do not extract that index from a raw existential
membership proof.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Finite support summability -/





/-! ## 2. Eventually-negative row facts -/











/-! ## 3. Cutoff-aware classifiers and majorant sums -/

namespace BigOrPointSideData







end BigOrPointSideData

namespace BigOrPointOutsideData







end BigOrPointOutsideData

namespace BigAndPointInsideData







end BigAndPointInsideData

namespace BigAndPointOutsideData







end BigAndPointOutsideData

/-! ## 4. Audit -/




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
