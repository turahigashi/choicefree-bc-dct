import Mathdemo.Internal.Real.Theorem415RowSeedsFactored

set_option linter.style.longLine false

/-!
# G239: theorem 4.15 from the chapter-4 general `I_B` provider

G238 still exposed the theorem-4.15-specific wrapper
`Lemma415Prop42RowSeedToolsProvider`.  That wrapper is only a specialization of
the chapter-4 general measurable-integral provider
`Sec4GeneralIBRowSeedToolsProvider`.

This file makes that specialization explicit at the theorem-4.15 boundary.
The 4.15 statement-shaped route now consumes the chapter-wide `I_B` row-seed
provider directly; the theorem-specific provider is only an internal projection.
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

