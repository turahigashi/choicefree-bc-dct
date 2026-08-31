import Mathdemo.Internal.Real.CauchySequenceRepresentativesImplyGlobalRepresentatives

/-!
# Localizing order-data extraction to positive inverse inputs

`RepresentativeFreeDecidableOrderCOFOAssembly` removed the global representative selector from the live
decidable-order quotient `COFO`, but its positive inverse field still accepted
a general extraction principle

`forall {a b}, ltQuot a b -> ltQuotData a b`.

The inverse branch only ever applies that principle to inequalities of the
form `ltQuot zeroQuot x`.  This file makes that dependence explicit.  It does
not construct the positive-data extractor, and it does not remove strict-order
decidability; it narrows the remaining order-data frontier to the exact shape
used by `COFO.inv`, `mul_inv_cancel`, and `inv_pos`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

















end BishopCReal

