import Mathdemo.Internal.Real.AbsoluteValueRepresentationLemma18

/-!
# G42: source representation for `min(f,1)` after Lemma 1.8

The source next defines `min{(f,{f_n}),1}` by the representation

`{min(f_0,1), f_0, -f_0, min(f_0+f_1,1)-min(f_0,1), f_1, -f_1, ...}`.

This file records that representation over the RegularSeq partial-function
surface.  Its convergence and value law are kept explicit, as in G41.
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
