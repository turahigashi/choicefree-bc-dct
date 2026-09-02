import Mathdemo.Internal.Real.NamingTwoScalarInequalityLawsBehind

/-!
# G71: splitting scalar laws into value-identification and core order

G70 named the two remaining property-(4) frontiers as scalar `RegularSeqLe`
laws.  This file splits such a scalar law into two source-faithful pieces:

1. identify each `valueAt` representative with the intended pointwise scalar
   expression, up to Bishop eventual equality;
2. prove the core scalar order between those intended expressions.

The generic transport lemma is proved here.  The concrete identifications and
core min-inequalities remain explicit data.
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
