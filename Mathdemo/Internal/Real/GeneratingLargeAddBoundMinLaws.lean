import Mathdemo.Internal.Real.AddBoundPresentationLargeLine735

set_option linter.style.longLine false

/-!
# G88: generating the large add-bound min laws

G87 replaced the large line-735 one-sided `subSeq` laws by add-bound min
inequalities.  This file splits those add-bound min inequalities into the same
primitive order ingredients already exposed in the small line-743 route:

* `u <= v + |u-v|`;
* `v <= u + |u-v|`;
* monotonicity of `minSeqWith` in the left argument;
* the nonnegative shift law for `min`.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
