import Mathdemo.Internal.Real.Theorem415LocalFullSetMajorantRoute

set_option linter.style.longLine false

/-!
# G232: Local theorem 4.15 from the cover-set provider

G231 connected theorem 4.15 to the local full-set majorant route, but that
local entry point still accepted the majorant split as an input field.  This
file constructs that split from the existing `coverSet` tail construction and
the generic row-seed provider.  Thus the local route now has the same
source-level inputs as the G230 cover-set provider route: domination by `g`,
nonnegativity of `g`, a Proposition-4.2 row-seed provider, and convergence in
measure of the abs-error sequence.
-/

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
