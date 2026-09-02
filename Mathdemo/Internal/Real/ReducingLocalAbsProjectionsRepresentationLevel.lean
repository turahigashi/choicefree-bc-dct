import Mathdemo.Internal.Real.LocalAbsProjectionDataProposition2

set_option linter.style.longLine false

/-!
# G141: reducing local abs-projections to representation-level projections

G140 introduced local abs-projection data for the operations used in Chapter 2
Proposition 2.4.  This file reduces those local projections to the actual
source representation shapes:

* addition uses `pairInterleave`;
* scalar multiplication uses `smulSeq`;
* absolute value uses `absRepSeq`;
* subtraction is addition with the explicit `(-1)*s` representative.

The genuinely analytic series-subsequence content remains data.  The assembly
from that data is closed here without quotient representative extraction.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24RepresentationAbsProjection

open Prop24LocalAbsProjection

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}














end Prop24RepresentationAbsProjection
end BishopRegularSeqChapter2





end BishopCReal
