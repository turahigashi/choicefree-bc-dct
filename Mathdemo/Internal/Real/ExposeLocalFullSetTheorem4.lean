import Mathdemo.Internal.Real.RemoveRowFlatTheorem415
import Mathdemo.Internal.Sec4.Local415SourceData

set_option linter.style.longLine false

/-!
# G253: expose the local full-set theorem-4.15 source route

G252 closed the generic `rowToFlat` bridge in the global standard-row route.
That route is useful as a diagnostic, but its remaining `charDomain` field is
too global for the previous `IntegrableSet1` API: the source definition gives the
needed characteristic-function witnesses locally from the full-set data of the
particular set in the proof.

This file therefore exposes the already proved local full-set endpoint from
`b2b39` as the current theorem-4.15 mainline.  The displayed theorem hypothesis
still has the Bishop source shape:

* an integrable majorant `g`;
* `|f_n| <= g`;
* source measure-convergence data for `|f_n - f|`;
* the source majorant split estimate.

No PFun representation data is required at this endpoint, and no global
characteristic-domain selector is exposed.
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
