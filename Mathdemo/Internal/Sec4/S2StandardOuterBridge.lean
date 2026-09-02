import Mathdemo.Internal.Sec4.DominatedConvergence415SourceComplete

/-!
# Sec4 Phase2-D2b2b_beta-b2b32: bridges into the S2 standard-outer provider

`b2b31` exposed the source-shaped negative-side residual:

* the standard Proposition 4.2 rows on `A.S2`;
* the corrected outer series of the absolute row sums for those same rows.

This file adds only compatibility bridges.  It does not claim to prove the
printed Proposition 4.2 `A.S2` construction from first principles.  Instead it
shows how the new `b2b31` provider is obtained from older, stronger interfaces:
the bundled corrected `pack_on_s2` package, or the generic `Rows + Outer` tools
already present in the theorem-4.15 source-complete layer.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Split an existing corrected `A.S2` package -/







/-! ## 2. Provider-level bridges -/

namespace Sec4GeneralIBSourceS2StandardOuterProvider





end Sec4GeneralIBSourceS2StandardOuterProvider

/-! ## 3. Theorem 4.15 endpoint through the generic S2 tools -/



end BishopC
