import Mathdemo.Internal.Real.SourceLevelTheorem415DownStandardRowComponents
import Mathdemo.Internal.Sec4.StepAbs
import Mathdemo.Internal.Sec4.DichotomyData

set_option linter.style.longLine false

/-!
# G260: source-level theorem 4.15 down to the one-step finite-cover assembly

G259 replayed the lower `I_B` route on the source-level theorem-4.15 surface,
but its last public route also displayed the older standard-row provider
components.  This file records the cleaner constructive route:

* the public theorem-4.15 surface remains `fn -> f` convergence in measure;
* `I_B` value identification is still discharged through the local bridge;
* the local bridge is produced from the one-step finite-cover abs assembly
  `Sec4CoverChiFStepAbs`;
* the `B`-dependent data-valued cover dichotomy is constructed internally by
  `sec4_coverDichotomyData`, so it is not an external input;
* from source-level function-side `Sec4ChiFCaseToolsData`, the one-step
  finite-cover assembly is obtained by `sec4_coverChiFStepAbs_of_dataCases`.

The remaining frontier is therefore the function-side `χ_A · f` case-tool
package for each absolute-error representative.  No Prop-to-Type witness
extraction or external selector is added here.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 1. Source-facing theorem 4.15 from one-step cover abs data -/




/-! ## 2. Function-side case tools construct the one-step cover assembly -/



/-! ## 3. Source-facing route through final tools -/





/-! ## 4. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
