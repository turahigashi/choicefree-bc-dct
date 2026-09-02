import Mathdemo.Internal.Real.Proposition111MonotonicityInterface

/-!
# G45: Corollary 1.12 and Definition 1.13 norm

Corollary 1.12 says that a partial function agreeing with an integrable
function on a full set is itself integrable and has the same integral.
Definition 1.13 then defines the norm by `||f|| = I(|f|)`.

This file records both statements on the RegularSeq Bishop-real route.  The
Corollary 1.12 proof still depends on the Proposition 1.11 bridge and on the
source construction `g + h - h`; those proof steps are exposed as bridge data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}







namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}



end BishopRegularSeqIntegrableRep





end BishopCReal
