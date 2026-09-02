import Mathdemo.Internal.Real.ReducingRepresentationProjectionsNumericSeriesProjections

set_option linter.style.longLine false

/-!
# G143: assembling Proposition 2.4 closure from numeric series bridges

G142 isolated the remaining analytic frontier as numeric RegularSeq series
projection bridges.  This file composes those bridges back up through the
representation and local operation layers, producing the Chapter 2
Proposition 2.4 closure inputs for intersection and union.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24SeriesBridgeAssembly

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition
open Prop24LocalAbsProjection
open Prop24RepresentationAbsProjection
open Prop24SeriesProjection

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}











end Prop24SeriesBridgeAssembly
end BishopRegularSeqChapter2





end BishopCReal
