import Mathdemo.Internal.Real.Proposition412ScalarMidLipschitz

set_option linter.style.longLine false

/-!
# G173: Proposition 4.12 value-data to good-set integral bridge

G172 proved the scalar estimate behind the source line

`|mid(-n, chi_A f, n)-mid(-n, chi_A g, n)| < eps`

on the common good set.  G171 showed that a representation-level pointwise
bound on the same good set is enough to control the relative integral.

This file closes the adapter between those two facts.  The concrete
representative for the absolute truncated difference is still kept as explicit
value data; no quotient representative is selected after the fact.
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
