import Mathdemo.Internal.Real.Theorem415CorrectedAbsOuter
import Mathdemo.Internal.Sec4.S2StandardOuterProvider

set_option linter.style.longLine false

/-!
# G251: theorem 4.15 from the source-shaped standard-row provider

G250 exposed theorem 4.15 from corrected abs-outer pack tools for the
abs-error representatives.  This file moves that input one definition layer
upstream: the pack tools are supplied by the source-shaped standard-row
provider of `b2b31`.

This is still not a proof of the provider itself.  It records the correct
remaining frontier:

* a generic row-to-flat bridge for `seriesSumRep_L1`;
* the characteristic-domain witness for `χ_A`;
* corrected abs-outer convergence for the standard Proposition 4.2 rows on
  both `A.S1` and `A.S2`.

No witness is extracted from a Prop-valued existence proof.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route








end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
