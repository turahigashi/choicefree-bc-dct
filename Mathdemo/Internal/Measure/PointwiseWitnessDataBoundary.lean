import Mathdemo.Internal.Measure.ImportCompatibilityNode

set_option linter.style.longLine false

/-!
# Stage A9: pointwise witness data boundary

This additive node records the hard boundary found after `ImportCompatibilityNode`.
An `IntegrableRep` carries `absConv`, the integral-side absolute convergence
of `S.I (BFunR.absf (fn n))`.  The pointwise absolute convergence witness at a
fixed `x` is not a field of `IntegrableRep`; in the existing plain domain it is
only stored behind `Nonempty` in `Prop`.

The definitions below show the positive data statement: if the pointwise
SeriesSum witness is supplied as Type-data, the signed point value is obtained
directly.  They deliberately do not manufacture that witness from `absConv`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R] {S : IntSpaceRC X R}








end BishopC
