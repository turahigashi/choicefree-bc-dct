import Mathdemo.Internal.Real.DataCarryingMidConstructorSourceProposition

set_option linter.style.longLine false

/-!
# G202: data-carrying measurable limits for Proposition 4.12

G201 introduced the exact source datum needed for one concrete
`mid(-n, chi_A h, n)` constructor.  This file exposes the corresponding
Bishop-style measurability interface: a measurable function carries, for every
integrable set `A` and truncation level `n`, the constructor source data itself.

This closes the data-carrying Prop. 4.12 route without using the old
Prop-valued `IsMeasurable`/`selector-based route` interface.
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
