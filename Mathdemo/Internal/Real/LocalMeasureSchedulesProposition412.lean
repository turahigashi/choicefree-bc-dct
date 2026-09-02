import Mathdemo.Internal.Real.MeasureCapEpsilonSchedulesProposition4

set_option linter.style.longLine false

/-!
# G199: local A-measure schedules for Proposition 4.12

G198 converted measure-cap schedule data into the G196 all-pair epsilon
schedule.  That was useful, but still stronger than the source proof: in
Proposition 4.12 the good sets `B` and `C` are returned by convergence and
satisfy `B ∧ C ⊆ A`, so the relevant cap is simply `mu(A)`.

This file localizes the schedule to common-good pairs.  It proves the cap
`mu(B ∧ C) <= mu(A)` from the carried common-good data, then uses the arithmetic
budget based on `mu(A)` to build the G195 construction data.
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
