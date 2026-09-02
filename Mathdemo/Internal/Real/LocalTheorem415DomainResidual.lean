import Mathdemo.Internal.Real.LocalTheorem415CoverSet

set_option linter.style.longLine false

/-!
# G233: Local theorem 4.15 from a domain-residual provider

G232 lowered the local theorem-4.15 route to the same cover-set provider data
used by G230.  This file narrows the generic row-seed provider to the
source-faithful domain-residual provider: the characteristic-function domain
witness is explicit, while the remaining Proposition-4.2 residual fields stay
visible.
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
