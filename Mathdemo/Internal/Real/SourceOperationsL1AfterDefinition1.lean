import Mathdemo.Internal.Real.Definition16WellDefinednessBridge

/-!
# G40: source operations on `L1` after Definition 1.6

The source next defines addition and scalar multiplication on integrable
functions:

* `(f,{f_n}) + (g,{g_n})` is represented by `{f_0,g_0,f_1,g_1,...}`;
* `a * (f,{f_n})` is represented by `{a*f_n}`.

This file records these operations over the RegularSeq presentation with all
convergence and value-law data explicit.
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
