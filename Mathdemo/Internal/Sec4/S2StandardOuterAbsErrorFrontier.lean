import Mathdemo.Internal.Sec4.S2StandardOuterBridge

/-!
# Sec4 Phase2-D2b2b_beta-b2b33: theorem-4.15 abs-error S2 standard-outer frontier

`b2b31` introduced the source-shaped `A.S2` target: the standard Proposition 4.2
rows, together with the corrected outer series of the absolute row sums for
those same rows.

This file specializes that target to the theorem-4.15 abs-error sequence
`u_n = |f_n - f|`.  The resulting frontier is weaker than the older split
frontier in the source-complete file: it does not ask for a corrected outer
witness for every separately supplied row witness, only for the standard rows
chosen by the frontier itself.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Abs-error-specific standard `A.S2` frontier -/



/-! ## 2. Bridges back to the existing theorem-4.15 endpoints -/







end BishopC
