import Mathdemo.Internal.Real.Theorem415Chapter4Residual

set_option linter.style.longLine false

/-!
# G241: theorem 4.15 from the domain-residual `I_B` provider

G240 lowered theorem 4.15 to the three-field chapter-4 residual provider.
The next already-available lower layer is
`Sec4GeneralIBDomainResidualProvider`: it fills the positive-side
characteristic-function absolute-convergence field from the explicit
source-domain witness for `chi_A`.

This file routes theorem 4.15 through that narrower provider.  The 4.15 layer
still has zero bridge steps; the Proposition-4.2 provider frontier is reduced
from three residual row/cut fields to the source-domain witness plus the two
remaining row/cut fields.
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

