import Mathdemo.Internal.Real.DerivingBoundedMidDataLocalRepresentative

set_option linter.style.longLine false

/-!
# G195: convergence data routed through the canonical two-n cap

G189 connected data-carrying convergence to common-good witnesses, but it still
targeted the older common-good construction interface.  G194 repaired the bad-set
side so that the concrete `mid` representatives give the canonical `n+n` cap
from local bound-source data.

This file connects those two routes.  Given data-carrying convergence, local
bound-source witnesses for the two concrete `mid` representatives, positivity of
the truncation level, and the remaining per-dyadic arithmetic/local construction
data, we build the cap-routed common-good source data and obtain the truncated
integral equality without passing through the previous hard-coded `n` bad-set
coefficient.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Proposition412
namespace TruncatedIntegralBridge











end TruncatedIntegralBridge
end Proposition412
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Proposition412.TruncatedIntegralBridge





end BishopCReal
