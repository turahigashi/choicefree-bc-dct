import Mathdemo.Internal.Measure.MoveCharacteristicDomainWitnessDefinition2
import Mathdemo.Internal.Real.RemoveBundledSourceStandardRowProvider

set_option linter.style.longLine false

/-!
# G282: use Definition-2.3 data on the source-shaped standard-row route

G281 moved the characteristic-function absolute-convergence witness back to a
Definition-2.3 compatibility surface, but it did so on the older row-seed
residual route.  That route still bundled the remaining Proposition-4.2
obligations as two coarse fields.

This node combines G281 with the already existing G271 standard-row route.
The public theorem-4.15 statement now uses:

* Definition-2.3 characteristic-function domain data;
* the standard positive-side outer convergence for the Proposition-4.2 rows;
* the standard negative-side rows;
* the standard negative-side outer convergence for those rows.

Thus the direct `charDomain` input is no longer public on the source-shaped
standard-row path either.  The remaining frontier is no longer a vague
row-seed package; it is the three standard row/outer facts that belong to the
Proposition-4.2 proof.
-/

namespace BishopC

variable {X R : Type*} [COFOC R]
variable {S : IntSpaceRC X R}

set_option linter.unusedVariables false

/-! ## 1. Source-shaped standard-row provider over Definition 2.3 -/





end BishopC

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter4
namespace Theorem415Route

/-! ## 2. Theorem 4.15 from Definition-2.3 standard-row data -/




/-! ## 3. Audit and package -/





end Theorem415Route
end BishopRegularSeqChapter4

open BishopRegularSeqChapter4.Theorem415Route



end BishopCReal
