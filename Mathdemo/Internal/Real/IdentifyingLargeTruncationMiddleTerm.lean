import Mathdemo.Internal.Real.OrderChainingTheorem1184

/-!
# G59: identifying the large truncation middle term

G58 reduced the large Theorem 1.18(4) estimate to two non-strict inequalities
with an abstract middle term.  The source middle term on lines 734--735 is
`I(|min(f,n)-min(g,n)|)`.  This file identifies that middle term in the
RegularSeq `L1` presentation by embedding the old-space truncation `min(g,n)`
into `L1`, forming the difference, and taking its source norm.
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
