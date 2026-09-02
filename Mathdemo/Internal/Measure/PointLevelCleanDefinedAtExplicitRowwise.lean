import Mathdemo.Internal.Measure.CleanRouteBridgeSourceRepresentatives

set_option linter.style.longLine false

/-!
# G312: point-level clean `definedAt` from explicit rowwise side data

The key constructive distinction is that bare membership in the final
countable union/intersection is not the same as rowwise side data for every
source set `A_i`.  G308--G310 used explicit Type-coded point data, but the
global witness records still had fields indexed by final-side membership.

This node exposes the safer point-level API directly: given explicit rowwise
side data (and the relevant hit/all-side data), build `PointwiseFlattenable`
and `RepDefinedAt` for the clean Proposition-2.10 representative at that point.
No final membership is used to extract row data.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise definedness of a characteristic representative from a side -/



/-! ## 2. Union point-level API -/

namespace BigOrPointSideData







end BigOrPointSideData

namespace BigOrPointOutsideData







end BigOrPointOutsideData

/-! ## 3. Intersection point-level API -/

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
