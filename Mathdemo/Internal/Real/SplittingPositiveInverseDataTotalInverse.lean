import Mathdemo.Internal.Real.COFOCAssemblyGlobalRepsPosEventuallySelector

/-!
# Splitting positive inverse data from total inverse selection

`COFOCAssemblyGlobalRepsPosEventuallySelector` normalized the current route to `COFOC` as depending on strict
order decidability, global representatives, and a `PosEventually` selector.
This file attacks the strict-order-decidability dependency at the positive
inverse layer.

The proof-indexed positive inverse already has cancellation and positivity when
given explicit `ltQuotData zeroQuot x`.  Decidability is only one way to turn
that partial/data-indexed inverse into the total `inv : CRealQuot → CRealQuot`
field required by `COFO`.  We isolate that totalization step as its own datum.
-/

namespace BishopCReal

open BishopC
open BishopCRat










end BishopCReal

set_option linter.style.longLine false

