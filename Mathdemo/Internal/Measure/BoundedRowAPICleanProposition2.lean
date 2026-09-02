import Mathdemo.Internal.Measure.PublicRowFlatTheoremCleanProposition

set_option linter.style.longLine false

/-!
# G306: bounded-row API for clean Proposition-2.10 majorants

G305 introduced the clean increment/drop rows.  The next mathematical datum is
not merely that each clean row is pointwise defined, but that its representative
absolute sum is bounded by a summable majorant.  This node packages that
bounded-row datum and gives direct adapters back to `PointwiseFlattenable` and
to the clean Proposition-2.10 representatives.

The actual finite-support majorants for union/intersection sides are still a
separate source-construction task.  This file makes the target shape precise.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise absolute bounds -/







namespace PointwiseRowAbsBounded



end PointwiseRowAbsBounded

/-! ## 2. Clean Proposition-2.10 bounded-row witnesses -/



namespace Prop210BCleanPointwiseMajorantWitness





end Prop210BCleanPointwiseMajorantWitness



namespace Prop210CCleanPointwiseMajorantWitness





end Prop210CCleanPointwiseMajorantWitness

/-! ## 3. Audit -/




end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route



end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
