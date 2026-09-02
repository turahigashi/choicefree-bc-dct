import Mathdemo.Internal.Measure.PointwiseFlatteningAPISeriesSumRepL1

set_option linter.style.longLine false

/-!
# G302: reducing Proposition 2.10 side witnesses to split pointwise data

G301 exposed the correct pointwise bridge for `seriesSumRep_L1`: the bridge is
not value-level eventual zero, but pointwise flattenability of the two internal
families `G_m F` and `tail_m F`.

This node connects that bridge back to Proposition 2.10.  It defines
intermediate witness records whose remaining analytic content is exactly the
split pointwise data required by G301, plus the still-separate domain witnesses
for the final representative rows.

No final Proposition-2.10 witness is constructed here.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Union side: reduce `prop_2_10_rep` to G301 split data -/



namespace Prop210BSourceSplitPointwiseWitness



end Prop210BSourceSplitPointwiseWitness

/-! ## 2. Intersection side: reduce `prop_2_10_c_rep` to G301 split data -/



namespace Prop210CSourceSplitPointwiseWitness



end Prop210CSourceSplitPointwiseWitness

/-! ## 3. Split-data surface -/



namespace Prop210SourceSplitPointwiseSurface



end Prop210SourceSplitPointwiseSurface

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
