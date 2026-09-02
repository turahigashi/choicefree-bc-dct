import Mathdemo.Internal.Real.FullSupportMidRepresentativesProposition4

set_option linter.style.longLine false

/-!
# G198: measure-cap epsilon schedules for Proposition 4.12

G196 introduced the canonical `n+n` epsilon schedule required by the corrected
bad-set estimate in Proposition 4.12.  G197 routed the final equality through
full-support mid representatives.

This file factors the epsilon-schedule obligation through a uniform
measure-cap datum: if the returned common-good set always satisfies
`eps * mu(B ∧ C) <= eps * M` and the cap budget
`eps * M + (n+n) * eps < 2^-k` is available, then the G196 schedule follows.
This is still data-carrying; it is not claiming that the cap and epsilon have
already been constructed from a Prop-only convergence statement.
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
