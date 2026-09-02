import Mathdemo.Internal.Measure.Section2BackedCleanCharacteristicData
import Mathdemo.Internal.Measure.ExplicitSideDataGivesFiniteSupport

set_option linter.style.longLine false

/-!
# Stage A3: Section-2 clean Prop.2.10 rows and the remaining old-row bridge

Stage A2 supplies unconditional nonnegative clean characteristic data for the
finite union-increment and intersection-drop rows.  This node keeps that route
separate from the older `prop_2_10_F_clean` / `prop_2_10_G_clean` representatives:
the Section-2 clean rows have their own representatives, while the previous rows are
the existing `IntegrableSet1_sub` representatives.

The finite-support row-side argument is discharged here for the Section-2 clean
rows from explicit rowwise side data.  No witness is extracted from final
membership in a countable union or intersection.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Section-2 clean row representatives -/









namespace CleanCharData



end CleanCharData

/-! ## 2. Clean-side classifiers over the Section-2 row-set names -/

namespace BigOrPointSideData











end BigOrPointSideData

namespace BigOrPointOutsideData











end BigOrPointOutsideData

namespace BigAndPointInsideData











end BigAndPointInsideData

namespace BigAndPointOutsideData











end BigAndPointOutsideData

/-! ## 3. Side-data wrappers and Section-2 clean final representatives -/

namespace UnionSideData



end UnionSideData

namespace InterSideData



end InterSideData









/-! ## 4. Exact bridge needed to fill the previous iter409 `clean_rows` field -/







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
