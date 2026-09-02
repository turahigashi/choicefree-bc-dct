import Mathdemo.Internal.Real.Theorem415SourceRouteProposition

set_option linter.style.longLine false

/-!
# G238: theorem-4.15 row seeds factored through the Proposition 4.2 provider

G237 removed `domainResidualProvider` from theorem-4.15 source data but still
kept two theorem-specific row-seed fields: one for `|f_n - f|` and one for the
constructive majorant `g + |f|`.

This file factors both fields through the existing generic Proposition-4.2
row-seed provider.  The theorem-4.15 layer now asks only for the lower-layer
Proposition-4.2 provider; the two specialized row-seed families are projections
from that provider.
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

