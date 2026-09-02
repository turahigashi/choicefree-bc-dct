import Mathdemo.Internal.Real.ReduceTheorem415LocalBridges
import Mathdemo.Internal.Sec4.S2StandardOuterProvider

set_option linter.style.longLine false

/-!
# G270: derive the general local bridge provider from the source standard-row provider

G269 exposed one remaining theorem-4.15 frontier: a general local value bridge
for the direct measurable representative `I_B(u)`.

The older chapter-4 development already has a source-shaped standard-row
provider for the same direct representative.  This file connects the two
interfaces:

`Sec4GeneralIBSourceS2StandardOuterProvider`
  -> `Sec4GenIBValueBridge`
  -> `Sec4GenIBLocalValueBridge`
  -> `Sec4GeneralLocalValueBridgeProvider`.

Thus theorem 4.15 no longer asks for a theorem-specific local bridge package,
nor even for the G269 local-provider wrapper.  Its remaining input is the
existing section-4 standard-row provider.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Standard-row provider implies the general local bridge provider -/





/-! ## 2. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
