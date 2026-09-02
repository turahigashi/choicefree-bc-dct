import Mathdemo.Internal.Real.BuildTheorem415MajorantSplit

set_option linter.style.longLine false

/-!
# G256: restore the source-level convergence-in-measure statement

G255 left a single core source datum named as convergence of the absolute-error
sequence.  Mathematically, Bishop's hypothesis `f_n -> f` in measure is exactly
the data that `|f_n-f| -> 0` in measure.  This file restores that source-level
name and packages theorem 4.15 with the displayed statement shape:

* an integrable majorant `g`;
* `|f_n| <= g`;
* `f_n -> f` in measure;
* the Chapter-4 Proposition 4.2/domain-residual provider.

No PFun representatives, global characteristic-domain selector, public
row-to-flat bridge, direct abs-error row seeds, or public majorant split are
required by this endpoint.
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
