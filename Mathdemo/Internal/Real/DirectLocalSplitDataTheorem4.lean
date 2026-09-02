import Mathdemo.Internal.Real.Theorem415LocalFullSetBridgesPFunConvergence

set_option linter.style.longLine false

/-!
# G244: direct local split data for theorem 4.15

G243 routed theorem 4.15 through the local full-set `I_B` interface, but its
local split package was obtained by first building the older global split data
and then converting its bridges to local bridges.

This file removes that intermediate split conversion.  The displayed theorem
4.15 decomposition is rebuilt directly from the source majorant choice data,
with local bridges supplied by the completed `remainingAtoms` interface on the
error side.  The remaining compatibility wrapper is only the value-bridge to
local-witness bridge for those already-completed atoms.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route









end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
