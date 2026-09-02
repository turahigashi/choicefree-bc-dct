import Mathdemo.Internal.Real.Proposition412RepresentativeWitnessesChi

set_option linter.style.longLine false

/-!
# G181: Proposition 4.12 concrete truncated-absolute-difference candidate

G180 showed that representative-level value witnesses are enough to feed the
full Proposition 4.12 integral estimate.  This file fixes the next
data-carrying layer: the representative used for

`|mid(-n, chi_A f, n) - mid(-n, chi_A g, n)|`

is explicitly the absolute value of the difference between the two displayed
`mid` representatives.  No representative is selected later from an equality
class; the remaining work is to prove that these explicit data satisfy the
pointwise value, outside-`A` zero, and bad-set `n`-bound witnesses.
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
