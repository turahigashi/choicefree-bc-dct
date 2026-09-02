import Mathdemo.Internal.Real.SeparatingEpsilonSchedulesLocalSourceWitnesses

set_option linter.style.longLine false

/-!
# G197: full-support mid representatives for Proposition 4.12

G196 separated epsilon schedules from local good-set witnesses.  The remaining
mid-representative obligation is that the actual constructor for
`mid(-n, chi_A h, n)` should return not only the representative and support
identity, but also the local source witnesses needed to derive the `[-n,n]`
pointwise bounds.

This file names that combined data shape and routes the G196 final equality
through it.
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
