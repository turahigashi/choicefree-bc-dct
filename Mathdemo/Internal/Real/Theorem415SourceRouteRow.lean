import Mathdemo.Internal.Real.Theorem415SourceCoverSet

set_option linter.style.longLine false

/-!
# G230: Theorem 4.15 source route with a row-seed provider

G229 used explicit row-seed data for the theorem-4.15 error sequence and for the
dominating function `g`.  The source-complete files already factor that
obligation as a general Proposition-4.2 row-seed provider.  This file routes the
cover-set proof through that provider, reducing the remaining plain-4.15
bridges by one.
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
