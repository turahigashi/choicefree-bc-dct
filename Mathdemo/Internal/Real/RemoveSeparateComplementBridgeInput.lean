import Mathdemo.Internal.Real.BuildLocalSplitDataBridgeBacked

set_option linter.style.longLine false

/-!
# G267: remove the separate complement-bridge input

G266 still displayed two theorem-4.15 local frontiers:

* complement bridges for `I_{-C}`;
* bridge-backed local majorant split data.

But the second package already contains local bridges for the absolute-error
representatives for every measurable set.  Instantiating it once at the fixed
positive radius `halfPow 0` is enough to recover the complement bridges needed
by lemma 4.14.  This file therefore removes the complement bridge as an
independent public input.

The remaining top-level frontier is now a single one: construct the
bridge-backed local majorant split package from the measurable/integrable-set
definitions and the source majorant estimates.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing data with no separate complement input -/





/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
