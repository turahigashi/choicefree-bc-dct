import Mathdemo.Internal.Real.DataValuedArchimedeanLayerCarriedRegularSeq

/-!
# Explicit adapter boundary for the previous quotient COFOC route

The RegularSeq route now carries the source-shaped data directly.  This file
records the remaining previous `BishopC.COFOC CRealQuot` route as an adapter
boundary rather than a hidden target:

* quotient representative extraction;
* conversion from Prop-valued quotient order to data-valued order;
* totalization of the positive-data inverse into the previous total inverse field.

No new construction is claimed here.  The previous live `COFOC` record is recovered
only when those adapters are supplied explicitly.
-/

namespace BishopCReal

open BishopC
open BishopCRat












end BishopCReal

set_option linter.style.longLine false

