import Mathdemo.Internal.Real.ReducingValueIdentificationPFunLevelPointwise

/-!
# G73: expanding the PFun-order frontier to displayed scalar expressions

G72 reduced the remaining property-(4) frontier to PFun-level pointwise order.
This file unfolds the outer PFun operations so that the remaining orders are
closer to the displayed source expressions:

* large line 735 becomes an order between
  `absSeq (min(f,n)-min(g_N,n))` and `absSeq (f-g_N)` at the PFun level;
* small line 743 becomes an order between
  `minSeqWith (absSeq f) (eps n)` and the PFun-level sum of the previous small
  truncation and the absolute tail.
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
