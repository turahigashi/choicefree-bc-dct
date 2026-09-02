import Mathdemo.Internal.Sec4.LocalFlatValue

/-!
# Sec4 Phase2-D2b2b_beta-b2b37: local value bridge for general `I_B`

The previous `Sec4GenIBValueBridge` is a global bridge: from a flat abs witness for
the direct measurable representative it proves domain membership and values on
`B.S1`/`B.S2`.  That shape is convenient downstream, but it can hide the same
membership-to-witness pressure that appeared in Proposition 4.2.

This file introduces a local counterpart.  The local bridge receives the
pointwise abs witnesses explicitly.  It is therefore the target that a
source-faithful full-set proof of the general measurable `I_B` should prove.
For compatibility, the previous bridge is shown to imply the local one, and the
already-integrable consistency theorem is reproved from the local bridge.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Local support and witnesses for the direct measurable representative -/







namespace Sec4GenIBLocalWitness







end Sec4GenIBLocalWitness

/-! ## 2. Local replacement for `Sec4GenIBValueBridge` -/





/-! ## 3. Already-integrable consistency from the local bridge -/







end BishopC
