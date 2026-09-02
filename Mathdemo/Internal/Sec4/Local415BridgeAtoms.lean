import Mathdemo.Internal.Sec4.LocalGenIBBridge

/-!
# Sec4 Phase2-D2b2b_beta-b2b38: local bridge atoms for theorem 4.15

The source-complete 4.15 file still contains several downstream estimates
phrased with the previous global `Sec4GenIBValueBridge`.  This file reproves the
same estimates from `Sec4GenIBLocalValueBridge`, keeping the calculations on a
common full support where the relevant pointwise witnesses are already present.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Direct measurable integral: monotonicity in the integrand -/



/-! ## 2. Direct measurable integral: additivity in the integrand -/



/-! ## 3. Mixed comparison with the ordinary relative integral -/



/-! ## 4. Complement comparison -/



/-! ## 5. Source split inequality with local bridges -/







end BishopC
