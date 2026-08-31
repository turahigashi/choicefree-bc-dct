import Mathdemo.Internal.Real.SplittingPropOrderDataOrderExtraction

/-!
# PosEventually witness selector frontier

`SplittingPropOrderDataOrderExtraction` reduced Prop-valued quotient order extraction to two separate
ingredients:

* a representative selector for quotient elements;
* a representative-level bridge from `PosEventually : Prop` to
  `PosEventuallyData : Type`.

The scalar rational order is decidable, but this does not by itself select the
`k, N` hidden behind the infinite tail condition in `PosEventually`.  This file
therefore records the exact Type-valued selector that is still needed and wires
that selector back into the `SplittingPropOrderDataOrderExtraction` route.
-/

namespace BishopCReal

open BishopC
open BishopCRat










end BishopCReal

set_option linter.style.longLine false

