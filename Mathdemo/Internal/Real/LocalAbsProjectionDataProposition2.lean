import Mathdemo.Internal.Real.Proposition24ConstructionExplicitAbs

set_option linter.style.longLine false

/-!
# G140: local abs-projection data for Proposition 2.4

G139 assembled Proposition 2.4 closure from explicit abs-decomposition data.
This file factors that large data interface into local, operation-shaped
projection data:

* addition/subtraction representatives can project absolute summability to
  their component representatives;
* scalar multiplication can project absolute summability to its source
  representative when the needed scalar data is supplied;
* absolute value can project absolute summability to its source representative.

These are data-carrying interfaces, not theorem-mining from a bare proposition.
They are then composed to produce the G138/G139 formula inputs for `min2` and
union.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24LocalAbsProjection

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}

















end Prop24LocalAbsProjection
end BishopRegularSeqChapter2





end BishopCReal
