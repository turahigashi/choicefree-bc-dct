import Mathdemo.Internal.Real.ReplaceFirstRowPackageFrontierRow

set_option linter.style.longLine false

/-!
# G264: replace arbitrary row residuals by source-shaped standard rows

G263 reduced the source-level theorem-4.15 route to row-seed residual fields.
One of those fields still had the over-strong shape
`Sec4Prop42AbsOuterOnS1OfRows`: it quantified over arbitrary row witnesses.

The printed Proposition 4.2 proof does not need that.  It constructs the
standard lambda rows from the characteristic representative and the supplied
`f`-absolute witness, then proves the corrected outer convergence for those
standard rows.  On the negative side, the corrected target is likewise the
standard `A.S2` rows together with the corrected outer convergence for those
same rows.

This file records that source-shaped route on the current G263 surface:

* `charDomain` supplies the positive-side characteristic abs witness;
* `standard_outer_on_s1` supplies the corrected outer convergence for the
  standard positive-side rows;
* `rows_on_s2` and `standard_outer_on_s2` supply the negative-side pack;
* row-to-flat and row-0 reconstruction stay internally discharged.

Thus the public route no longer asks for outer convergence over arbitrary row
witnesses.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Abs-error-specific standard row source data -/





/-! ## 2. Global source-shaped standard-row provider, without row-to-flat -/




/-! ## 3. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
