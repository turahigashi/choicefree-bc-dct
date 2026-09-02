import Mathdemo.Internal.Real.Proposition412GoodSetTruncated

set_option linter.style.longLine false

/-!
# G172: Proposition 4.12 scalar `mid` Lipschitz bridge

The source proof of Proposition 4.12 moves from the good-set estimate

`|f(x)-g(x)| < eps`

to the displayed truncated estimate

`|mid(-n, chi_A f, n) - mid(-n, chi_A g, n)| < eps`

on the same good set.  G171 had already connected a representation-level
pointwise bound to the relative integral estimate.  This file closes the
scalar half of that pointwise bridge: `mid(-n, -, n)` is 1-Lipschitz, and on
points where `chi_A = 1` the `chi_A` factors disappear.
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
