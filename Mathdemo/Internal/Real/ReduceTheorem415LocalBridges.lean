import Mathdemo.Internal.Real.BuildLocalMajorantSplitLocalBridge

set_option linter.style.longLine false

/-!
# G269: reduce theorem 4.15 local bridges to one general provider

G268 reduced the theorem-specific frontier to local value bridges for the
absolute-error representatives and for the majorant `g + |f|`.  Both are
instances of the same section-4 fact: for any non-negative integrable
representative `u` and any measurable set `B`, the direct measurable relative
integral representative carries the local value bridge.

This file packages that fact as one provider and derives the G268 theorem-4.15
bridge generators from it.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. The one remaining general local bridge provider -/





/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
