import Mathdemo.Internal.Real.ExposeLocalFullSetTheorem4
import Mathdemo.Internal.Sec4.SourceDomainWitness

set_option linter.style.longLine false

/-!
# G254: remove direct abs-error row seeds from the theorem-4.15 mainline

G253 exposed the local full-set route but still accepted row-seed tools for
each absolute-error function `|f_n-f|`.  Those row seeds are Proposition 4.2
machinery, not independent theorem-4.15 data.

This file replaces the per-`n` row-seed input by the existing
`Sec4GeneralIBDomainResidualProvider`.  The provider is still a visible Chapter
4 frontier, but it is now the general Proposition 4.2/domain-residual surface,
not an arbitrary sequence of theorem-specific witnesses.
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
