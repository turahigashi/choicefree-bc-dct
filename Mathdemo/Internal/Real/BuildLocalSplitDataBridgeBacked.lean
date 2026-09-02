import Mathdemo.Internal.Real.Theorem415LocalSplitSurface

set_option linter.style.longLine false

/-!
# G266: build local split data from bridge-backed majorant estimates

G265 exposed theorem 4.15 at the exact local split/complement surface consumed
by lemma 4.14.  This file opens the `local split` field one layer further.

The source proof of theorem 4.15 proves the split estimate by comparing
`|f_n - f|` with a non-negative majorant and then estimating the two pieces
over `A ∧ B` and `-A`.  The construction below formalizes that step using
local full-set bridges directly, rather than going back through the older
row-seed/global-bridge interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Bridge-backed local majorant split data -/



/-! ## 2. Theorem 4.15 wrapper using bridge-backed majorant split data -/




/-! ## 3. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
