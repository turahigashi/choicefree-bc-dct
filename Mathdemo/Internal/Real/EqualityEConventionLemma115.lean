import Mathdemo.Internal.Real.Proposition114ZeroNormEquality

/-!
# G47: equality a.e. convention and Lemma 1.15 compression data

After Proposition 1.14 the source changes the working equality/order on
`F(X)` to mean equality/order on some full set.  Lemma 1.15 then compresses an
arbitrary representation of an integrable function by replacing an initial
block with its finite sum.

This file records both moves on the Bishop RegularSeq route.  The cutoff `N`,
the compressed representation, and the final strict estimate are explicit
data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}








namespace BishopRegularSeqPFun

variable {X : Type}



end BishopRegularSeqPFun



namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}





end BishopRegularSeqIntegrableRep





end BishopCReal
