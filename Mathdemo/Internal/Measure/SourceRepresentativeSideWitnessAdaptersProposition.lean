import Mathdemo.Internal.Measure.CountableProposition210OutputSurface

set_option linter.style.longLine false

/-!
# G300: source-representative side-witness adapters for Proposition 2.10

G299 made the final countable output surface explicit.  This node tightens the
remaining frontier by aligning the G298/G299 output witnesses with the actual
source representatives used in the Chapter-2 proof:

* for Proposition 2.10(b), the `φ`/increment series representative
  `prop_2_10_rep`;
* for Proposition 2.10(c), the dual `ψ`/drop series representative
  `prop_2_10_c_rep`.

The adapters here do not construct the missing sidewise domain and absolute
convergence witnesses.  They state that supplying those witnesses for the
source representative is exactly enough to supply the G299 output surface.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Definitional alignment with the source representatives -/







/-! ## 2. Source-representative side witnesses -/





namespace Prop210BSourceRepSideWitness



end Prop210BSourceRepSideWitness

namespace Prop210CSourceRepSideWitness



end Prop210CSourceRepSideWitness

/-! ## 3. Surface over source representatives -/



namespace Prop210SourceRepSideWitnessSurface



end Prop210SourceRepSideWitnessSurface

/-! ## 4. Audit -/




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
