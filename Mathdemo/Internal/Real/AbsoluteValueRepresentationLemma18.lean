import Mathdemo.Internal.Real.SourceOperationsL1AfterDefinition1

/-!
# G41: absolute-value representation and Lemma 1.8 boundary

After Definition 1.6 the source defines `|(f,{f_n})|` by the representation

`{|f_0|, f_0, -f_0, |f_0+f_1|-|f_0|, f_1, -f_1, ...}`.

This file records that source representation over RegularSeq partial
functions.  The analytic identification with `|f|` and the Lemma 1.8 limit are
kept as explicit data.
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
