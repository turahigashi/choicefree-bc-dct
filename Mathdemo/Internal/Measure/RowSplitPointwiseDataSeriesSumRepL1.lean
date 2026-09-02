import Mathdemo.Internal.Measure.ReducingProposition210SideWitnesses

set_option linter.style.longLine false

/-!
# G303: row-to-split pointwise data for `seriesSumRep_L1`

G302 reduced Proposition 2.10 to pointwise data for the two split families
inside `seriesSumRep_L1`: `G_m F` and `tail_m F`.

This node adds the next layer of bookkeeping.  It proves that:

* `ofL` representatives are pointwise defined everywhere;
* `tailFrom` representatives are pointwise defined wherever the original row
  is pointwise defined;
* therefore, to build G302 split data, it is enough to provide rowwise
  pointwise data for the original `F i` plus summable majorants for the
  absolute row sums of the `G_m` and `tail_m` split families.

This still does not construct the majorants for Proposition 2.10.  It only
removes one layer of representative plumbing from the remaining problem.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Pointwise definedness for the split-row constructors -/

namespace RepDefinedAt









end RepDefinedAt

/-! ## 2. Majorants for the split families -/



namespace SeriesSumRepL1SplitMajorants



end SeriesSumRepL1SplitMajorants

/-! ## 3. Proposition-2.10 majorant-level witness records -/



namespace Prop210BSourceSplitMajorantWitness



end Prop210BSourceSplitMajorantWitness



namespace Prop210CSourceSplitMajorantWitness



end Prop210CSourceSplitMajorantWitness

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
