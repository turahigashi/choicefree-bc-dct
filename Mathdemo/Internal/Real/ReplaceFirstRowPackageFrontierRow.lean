import Mathdemo.Internal.Real.RemoveRowFlatPublicTheorem4

set_option linter.style.longLine false

/-!
# G263: replace the first row-package frontier by the row-0 reconstruction

G262 left three public row-package components for each theorem-4.15 absolute
error term.  The first one, reconstruction of `f` absolute convergence from
lambda-row absolute convergence on `A.S1`, is already closed generically by
the row-0-right argument from b2b27.

This file uses that result on the source-level theorem-4.15 route.  The
remaining frontier is now the three residual row-seed fields:

* characteristic absolute convergence on `A.S1`;
* corrected outer convergence for the standard positive-side rows;
* corrected negative-side row package.

The first row-package field is no longer public.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing data using row-seed residual fields -/





/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
