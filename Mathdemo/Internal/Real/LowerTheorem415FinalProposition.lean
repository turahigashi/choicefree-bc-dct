import Mathdemo.Internal.Real.LowerTheorem415LayerTelescopes
import Mathdemo.Internal.Sec4.Row1Switch

set_option linter.style.longLine false

/-!
# G274: lower theorem 4.15 to the final Proposition-4.2 primitive

G273 connected theorem 4.15 to the b2b6 `Sec4ChiFInternalTools` provider.
The b2b9 row-1 switch already proves that those three internal tools follow
from a single remaining primitive, `Sec4Prop42FinalTools`, i.e. the finite
cover `chi * f` abs witness.

This file exposes that lower route on the theorem-4.15 surface:

`Sec4Prop42FinalTools`
  -> `Sec4ChiFInternalTools`
  -> `Sec4GenIBValueBridge`
  -> `Sec4GenIBLocalValueBridge`
  -> theorem 4.15.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. General final Proposition-4.2 tools imply the G269 local provider -/






/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
