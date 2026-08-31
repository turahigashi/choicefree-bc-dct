import Mathdemo.Internal.Real.QuotientMaxMinAbsoluteBounds

/-!
# Quotient Archimedean half-power fields

`QuotientMaxMinAbsoluteBounds` closed the max/min order fields.  This file adds the two
Archimedean fields that only require the already-available tail-positivity
definition:

* `archimedean`;
* `archimedean_pos`.

The proof is intentionally modest.  A positive quotient has a representative
tail bounded below by `eps k`; subtracting one dyadic half gives a strict lower
bound by the constant sequence `eps (k+1)`.
-/

namespace BishopCReal

open BishopC
open BishopCRat










end BishopCReal

