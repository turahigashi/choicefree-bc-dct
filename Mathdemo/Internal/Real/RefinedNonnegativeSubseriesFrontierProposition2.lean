import Mathdemo.Internal.Real.AssemblingProposition24ClosureNumeric

set_option linter.style.longLine false

/-!
# G144: refined nonnegative-subseries frontier for Proposition 2.4

G142/G143 used broad numeric projection bridges.  This file narrows the
remaining analytic frontier to the source-faithful data actually needed by the
proof of Proposition 2.4:

* subseries projection is required only for nonnegative absolute-value series;
* scalar recovery is required only through carried scalar-specific data
  (not through a global selector from arbitrary scalar multiplication);
* the resulting data still assembles into the G140/G139 Proposition 2.4
  closure route without choosing representatives from quotients.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24RefinedSeriesFrontier

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition
open Prop24LocalAbsProjection
open Prop24RepresentationAbsProjection

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}


























end Prop24RefinedSeriesFrontier
end BishopRegularSeqChapter2





end BishopCReal
