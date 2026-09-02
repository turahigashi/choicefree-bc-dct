import Mathdemo.Internal.Real.Theorem415Chapter4General

set_option linter.style.longLine false

/-!
# G240: theorem 4.15 from the chapter-4 residual `I_B` provider

G239 uses the chapter-4 general row-seed provider.  That provider still exposes
one field that is already generically proved: the row-0-right reconstruction of
the original representative from the Proposition-4.2 rows.

The lower chapter-4 API `Sec4GeneralIBRowSeedResidualProvider` removes that
field and keeps only the three genuinely residual Proposition-4.2 row/cut
ingredients.  This file routes theorem 4.15 through that residual provider.
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

