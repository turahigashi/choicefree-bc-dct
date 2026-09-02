import Mathdemo.Internal.Real.TwoNBadSetCapBounded

set_option linter.style.longLine false

/-!
# G192: common-good source data routed through arbitrary bad caps

G188 connected the common-good `B,C,N` data to the older source-budget interface
whose bad-set coefficient was hard-coded as `n`.  G190 introduced the corrected
arbitrary-cap interface.  This file repeats the common-good bridge for that
interface, so downstream Prop. 4.12 work no longer has to pass through the
source's suspicious `n * mu(A-E)` line.
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
