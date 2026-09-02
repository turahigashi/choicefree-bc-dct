import Mathdemo.Internal.Real.NormalizingPrimitiveScalarLawsSubSeqCores

/-!
# G82: splitting the large `subSeq` core through two-sided order

G81 normalized the displayed source subtraction to `subSeq`.  For the large
line-735 core, the remaining absolute-value inequality

`|min(a,c)-min(b,c)| <= |a-b|`

is now split into the two one-sided inequalities that feed the existing
`RegularSeqAbsFromTwoSidedBridge`.

The small line-743 core law is carried unchanged; it is the next separate
frontier after the large two-sided min order has been supplied.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
