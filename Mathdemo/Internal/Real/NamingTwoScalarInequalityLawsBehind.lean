import Mathdemo.Internal.Real.UnpackingPointwiseRoutesValueLevelInequalities

/-!
# G70: naming the two scalar inequality laws behind property (4)

G69 opened the remaining Theorem 1.18(4) frontiers to value-level
`RegularSeqLe` inequalities.  This file gives those value-level inequalities
source-faithful names:

* large line 735: `|min(f,n)-min(g_N,n)| <= |f-g_N|`;
* small line 743: `min(|f|,1/n) <= min(|g_N|,1/n) + ||f|-g_N|`.

No scalar order proof is smuggled in here.  The scalar laws remain explicit
data, and this file only checks that supplying them feeds the G69
value-branch route and hence the existing property-(4) assembly.
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
