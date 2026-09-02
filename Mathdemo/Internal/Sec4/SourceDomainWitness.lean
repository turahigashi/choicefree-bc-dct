import Mathdemo.Internal.Sec4.RowSeedResidual

/-!
# Sec4 Phase2-D2b2bβ-b2b28: source-faithful domain witnesses

The three residual row-seed fields isolated in `b2b27` are not merely missing
algebra.  With the current `IntegrableSet1` API, membership `x ∈ A.S1` or
`x ∈ A.S2` does not carry the pointwise domain witness for the characteristic
representative `hA.rep`.

In the source proof, `χ_A` is a partial function whose domain is
`A¹ ∪ A²`; therefore using `χ_A(x)` on `A¹`/`A²` implicitly carries this
domain information.  This file makes that source-side datum explicit instead
of smuggling it in as an unproved global assumption.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

















end BishopC
