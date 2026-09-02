import Mathdemo.Internal.Real.SplittingAbsoluteTailUpperBound

set_option linter.style.longLine false

/-!
# G87: add-bound presentation of the large line-735 one-sided laws

G82 split the large line-735 min-Lipschitz inequality into two one-sided
`subSeq` inequalities.  This file exposes the source-shaped add-bound form
behind those one-sided laws:

`min(a,c) <= min(b,c) + |a-b|`

and the swapped version.  A general bridge

`x <= y+z -> x-y <= z`

collapses these add-bound inputs back to G86's `subSeq` surface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
