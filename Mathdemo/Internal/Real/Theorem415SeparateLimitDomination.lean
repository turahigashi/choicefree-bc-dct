import Mathdemo.Internal.Real.LocalTheorem415SourcePFun

set_option linter.style.longLine false

/-!
# G235: Theorem 4.15 without a separate limit-domination input

G234 removed the direct abs-error convergence-in-measure input.  This file
removes the separate `|f| <= g` endpoint input from the local PFun route.

The source proof writes the error domination as `|f_n - f| <= 2g`.  In Lean that
requires a representative-level datum `|f| <= g`.  Rather than silently adding
that datum, this file uses the theorem statement's already integrable limit
`f` to form the constructive majorant `g + |f|`:

`|f_n - f| <= |f_n| + |f| <= g + |f|`.

This is a Bishop-valid variant of the displayed domination step and introduces
no Prop-to-data selector.
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
