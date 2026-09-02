import Mathdemo.Internal.Measure.RowSplitPointwiseDataSeriesSumRepL1

set_option linter.style.longLine false

/-!
# G304: from original row flattenability to split majorants

G303 made the `seriesSumRep_L1` split explicit.  This node proves the generic
estimates that make that split usable:

* the finite-prefix row `G_m F i` has pointwise absolute sum bounded by the
  pointwise absolute sum of the original row `F i`;
* the tail row `tail_m F i` has pointwise absolute sum bounded by the same
  original row absolute sum.

Consequently, ordinary `PointwiseFlattenable F x` already supplies the split
majorants required by G303.  The remaining Proposition-2.10 problem is now
localized to proving `PointwiseFlattenable` for the original source families
`prop_2_10_F` and `prop_2_10_G`.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Finite-prefix and tail estimates -/



namespace RepDefinedAt





end RepDefinedAt

/-! ## 2. Build split majorants from ordinary pointwise flattenability -/

namespace SeriesSumRepL1SplitMajorants



end SeriesSumRepL1SplitMajorants

/-! ## 3. Proposition-2.10 witnesses reduced to ordinary pointwise flattenability -/



namespace Prop210BSourcePointwiseFlattenableWitness



end Prop210BSourcePointwiseFlattenableWitness



namespace Prop210CSourcePointwiseFlattenableWitness



end Prop210CSourcePointwiseFlattenableWitness

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
