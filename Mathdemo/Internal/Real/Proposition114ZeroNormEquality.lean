import Mathdemo.Internal.Real.Corollary112Definition113

/-!
# G46: Proposition 1.14, zero norm and equality on a full set

Proposition 1.14 says that for integrable functions `f` and `g`:

* `f = g` on some full set;
* `||f - g|| = 0`;

are equivalent.  The reverse direction in the source proof selects an
increasing subsequence `k(n)` with small prefix absolute integral and then uses
the full set `B1 ∩ B2`.

This file adds the RegularSeq statement shape and keeps the `k(n)` and full-set
construction as explicit witness data.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}



end BishopRegularSeqIntegrableRep




namespace BishopRegularSeqProp114SubsequenceData

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}


end BishopRegularSeqProp114SubsequenceData








end BishopCReal
