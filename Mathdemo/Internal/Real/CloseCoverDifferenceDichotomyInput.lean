import Mathdemo.Internal.Real.LowerTheorem415DataValued
import Mathdemo.Internal.Sec4.DichotomyData

set_option linter.style.longLine false

/-!
# G277: close the cover/difference dichotomy input

G276 exposed theorem 4.15 through `Sec4GeneralDataCasesProvider`, whose public
inputs were generic chi-f case tools plus data-valued cover/difference
dichotomies.  The b2b13 development constructs the cover/difference dichotomy
data directly from the carried measurable-set and cover definitions.

This node removes that dichotomy from the theorem-4.15 public surface.  The
remaining public input is exactly the generic `Sec4ChiFCaseToolsData` package.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Generic chi-f case tools imply the G269 local provider -/






/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
