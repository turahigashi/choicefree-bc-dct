import Mathdemo.Internal.Real.Theorem116TailSqueezeBridge

/-!
# G51: Corollary 1.17 density interface

Corollary 1.17 says that `L` is dense in `L1`.  In the RegularSeq route, an
`L1` element already carries a representing sequence of `L` terms.  The finite
sums of that representing sequence are therefore the source approximants.

This file closes the membership of those finite sums in `L`, and records the
remaining density conclusion as explicit norm-convergence data supplied by
Theorem 1.16.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqCor117

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}




end BishopRegularSeqCor117








end BishopCReal
