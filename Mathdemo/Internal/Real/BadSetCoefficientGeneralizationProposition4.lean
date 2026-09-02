import Mathdemo.Internal.Real.DataCarryingConvergenceSuppliesCommonGood

set_option linter.style.longLine false

/-!
# G190: bad-set coefficient generalization for Proposition 4.12

The source writes the bad-set contribution as `n * mu(A-E)`.  For a signed
truncation `mid(-n, -, n)`, the canonical safe coefficient may be a separately
proved bound such as `2n`.  The final uniqueness argument only needs a positive
coefficient that is controlled by the epsilon budget.

This file therefore generalizes the bad-set line from the hard-coded natural
`n` coefficient to an arbitrary carried positive `badCap : R`.
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
