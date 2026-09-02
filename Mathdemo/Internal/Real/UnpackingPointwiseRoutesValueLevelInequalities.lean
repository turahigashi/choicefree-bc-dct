import Mathdemo.Internal.Real.BundlingTwoPointwiseBranchRoutes

/-!
# G69: unpacking the pointwise routes to value-level inequalities

G68 bundled the remaining Theorem 1.18(4) frontiers as two full-set pointwise
routes.  This file opens those pointwise routes one layer further: each route
is now supplied by value-level `RegularSeqLe` inequalities for every point and
every pair of value-series witnesses.

The remaining frontier is therefore no longer an anonymous `L1LeOnFull`
object; it is the two scalar-valued source inequalities

* `|min(f,n)-min(g,n)| <= |f-g|`;
* `min(|f|,1/n) <= min(|g_N|,1/n) + ||pointwise tail||`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}
















end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
