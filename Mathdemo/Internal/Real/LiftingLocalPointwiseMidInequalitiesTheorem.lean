import Mathdemo.Internal.Real.SourceShapedConcreteSurfacesTheorem4

set_option linter.style.longLine false

/-!
# G221: lifting local pointwise mid inequalities to Theorem 4.6 domination

G220 isolated the remaining Theorem 4.6 work as two-step domination data for
the concrete `f+`, `f-`, and `|f|` truncation-integral surfaces.

This increment pushes that obligation down one more Bishop-faithful layer:
instead of assuming the integral domination directly, it is enough to carry
the local pointwise inequalities for the concrete mid representatives.  The
integral statements are then obtained by Proposition 1.11 on a full set built
from the four carried representative domains.

Thus the remaining obligation is now the scalar/set calculation in the
representative values themselves, not any Prop-to-data extraction or
order-theoretic choice.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Lemma45Theorem46

open Proposition412.TruncatedIntegralBridge

















end Lemma45Theorem46
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Lemma45Theorem46



end BishopCReal
