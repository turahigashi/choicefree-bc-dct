import Mathdemo.Internal.Sec4.SourceAbsPackProvider

/-!
# Sec4 Phase2-D2b2b_beta-b2b30: source-shaped S2 abs-zero provider

`b2b29` narrowed the `A.S1` residual to the standard Proposition 4.2 lambda
rows, but it still had to assume the corrected `A.S2` abs-pack as one bundled
field.  This file splits that bundled negative-side field into the two pieces
that match the printed proof structure more closely:

* construct the standard Proposition 4.2 lambda rows on `A.S2`;
* prove that each of those row absolute sums is zero.

The second item is intentionally kept explicit.  The existing signed theorem
`sec4_lambdaRowZeroOnS2` proves only that the signed row value is zero.  After
the b2b20 correction, the required outer series is the series of row absolute
sums, and `RepNonneg` is only value-level nonnegativity, not termwise
nonnegativity of the representing sequence.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Corrected S2 row-zero frontier -/





/-! ## 2. Refined source-shaped provider -/



namespace Sec4GeneralIBSourceS2AbsZeroProvider





end Sec4GeneralIBSourceS2AbsZeroProvider







end BishopC
