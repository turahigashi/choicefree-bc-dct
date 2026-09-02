import Mathdemo.Internal.Measure.SourceRepresentativeSideWitnessAdaptersProposition

set_option linter.style.longLine false

/-!
# G301: pointwise flattening API for `seriesSumRep_L1`

G300 fixed the exact source representatives whose side witnesses are still
missing.  The next obstacle is not value-level eventual-zero behavior, but
pointwise absolute convergence of the flattened representatives produced by
`seriesSumRep_L1`.

This node adds a public pointwise API:

* `RepDefinedAt r x` abbreviates the Definition-2.3 pointwise absolute
  convergence condition for a representative;
* `PointwiseFlattenable F x` records rowwise absolute convergence plus a
  summable majorant for the row absolute sums;
* `seriesIntegrable_definedAt_of_pointwiseFlattenable` is the forward
  row-to-cellAt bridge;
* `SeriesSumRepL1PointwiseData` supplies the two pieces that the actual
  `seriesSumRep_L1` definition uses, namely `G_m F` and `tail_m F`.

No Proposition-2.10 side witness is constructed in this node.  It only
exposes the correct bridge theorem needed before attempting that construction.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Public pointwise representative API -/




namespace RepDefinedAt









end RepDefinedAt

/-! ## 2. Rowwise pointwise flattening data -/



namespace PointwiseFlattenable



end PointwiseFlattenable

/-! ## 3. Forward bridge for `seriesIntegrable` and `seriesSumRep_L1` -/



set_option maxHeartbeats 800000 in
-- Universe elaboration for the two split-family fields exceeds the default limit.




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
