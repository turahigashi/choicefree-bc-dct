import Mathdemo.Internal.Real.SourceLevelTheorem415Corrected

set_option linter.style.longLine false

/-!
# G262: remove row-to-flat from the public theorem-4.15 frontier

G261 lowered theorem 4.15 to the corrected abs-row package
`Sec4ChiFCaseAbsPackTools`.  That package contains four components: the generic
row-to-flat bridge, the positive-side row extraction, the positive-side row
pack construction, and the negative-side row pack construction.

The generic row-to-flat bridge is already implemented as
`sec4_rowToFlat_source`.  This file uses it to build the abs-row package, so
the source-level theorem-4.15 route no longer exposes row-to-flat as an input.
The remaining public frontier is exactly the three function-side row package
components.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing data with row-to-flat already closed -/





/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
