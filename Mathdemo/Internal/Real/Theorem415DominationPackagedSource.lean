import Mathdemo.Internal.Real.Theorem415SeparateLimitDomination

set_option linter.style.longLine false

/-!
# G236: theorem-4.15 domination packaged as source-statement data

G235 preserved the source theorem statement by replacing the displayed `2g`
majorant with the constructive majorant `g + |f|`.  The remaining visible
`g_nonneg` input is not an extra mathematical assumption: in Bishop's statement
`|f_n| <= g`, the right-hand side is a non-negative dominating majorant.

This file packages that convention as statement-level data:

* `g` is the witness in "there exists an integrable function g";
* `domination` is the source assertion `forall n, |f_n| <= g`;
* the non-negativity needed by the cover-set machinery is projected from that
  domination package, not passed as a separate theorem-4.15 input.

No Prop-to-data selector is introduced.
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
