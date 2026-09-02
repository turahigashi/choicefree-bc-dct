import Mathdemo.Internal.Real.LocalTheorem415DomainResidual

set_option linter.style.longLine false

/-!
# G234: Local theorem 4.15 from source PFun convergence data

G233 still accepted `Lemma414ConvergeInMeasureToZeroData` for the abs-error
sequence.  This file removes that direct abs-error convergence input from the
local route.  Instead it consumes the source-shaped Type/Sigma convergence
data `fn -> f` at the PFun level, together with representation data connecting
the chosen PFun representatives to the integrable representatives.

This is still data-carrying: no witness is extracted from the Prop-valued
`ConvergeInMeasure`.
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
