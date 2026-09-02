import Mathdemo.Internal.Real.DataCarryingBadSetBoundBudget

set_option linter.style.longLine false

/-!
# G186: arbitrary-small estimates imply the truncated-integral equality

G185 gives the source-shaped strict estimate for the concrete nonnegative
representative

`d = |mid(-n, chi_A f, n) - mid(-n, chi_A g, n)|`.

This file closes the data-carrying final step of Proposition 4.12: if this
integral is smaller than every dyadic tolerance, then it is zero, hence the
`L1` seminorm of the difference between the two mid representatives is zero,
and the existing choice-free `IntegrableRep.integral_eq_of_normL1_sub_zero`
gives equality of the two truncated integrals.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge











end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge





end BishopCReal
