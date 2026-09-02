import Mathdemo.Internal.Measure.FromOriginalRowFlattenabilitySplitMajorants

set_option linter.style.longLine false

/-!
# G305: public row-to-flat theorem and clean Proposition-2.10 rows

G304 proved that ordinary `PointwiseFlattenable F x` supplies the split
majorants required by the actual `seriesSumRep_L1` implementation.  This node
exposes that result under the direct public theorem that downstream code wants,
and starts the clean Proposition-2.10 route:

* `seriesSumRep_L1_definedAt_of_pointwiseFlattenable` is the row-to-flat bridge;
* `prop_2_10_F_clean` uses the increment sets
  `B_0, B_{n+1} \ B_n`;
* `prop_2_10_G_clean` uses the drop sets
  `A_0 \ A_0, C_n \ C_{n+1}`;
* clean final representatives are made available separately from the original
  difference representatives.

This does not claim that the clean representatives have already been identified
with the original `prop_2_10_rep` / `prop_2_10_c_rep`.  It deliberately splits
the remaining work into (1) clean-row pointwise majorants and (2) source
equivalence with the original telescoping formulation.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Public row-to-flat theorem -/





/-! ## 2. Clean Proposition-2.10 source rows -/













/-! ## 3. Clean final representatives -/





/-! ## 4. Clean representatives use the public row-to-flat bridge -/





/-! ## 5. Audit -/




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
