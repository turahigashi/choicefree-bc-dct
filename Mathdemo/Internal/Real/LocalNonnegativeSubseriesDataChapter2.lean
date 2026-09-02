import Mathdemo.Internal.Real.ClosingHalfAbsoluteValueTermLaw

set_option linter.style.longLine false

/-!
# G148: local nonnegative-subseries data for Chapter 2 Proposition 2.4

G147 closed the scalar-recovery side of Proposition 2.4.  The remaining analytic
content is now only the nonnegative subseries projection used by the concrete
source representations:

* the left/right channels of `pairInterleave`;
* the middle channel of `absRepSeq`.

This file avoids a global arbitrary subseries selector.  It takes those local
nonnegative-channel projections as carried data and assembles the existing
Proposition 2.4 closure route from that local data plus the closed scalar
recoveries.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace Prop24LocalNonnegativeSubseries

open CharacteristicFormula
open CharacteristicValueTransport
open CharacteristicFormulaValueTransport
open Prop24FromAbsDecomposition
open Prop24LocalAbsProjection
open Prop24RepresentationAbsProjection
open Prop24RefinedSeriesFrontier
open Prop24HalfTermLaw

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}











end Prop24LocalNonnegativeSubseries
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.Prop24FromAbsDecomposition





end BishopCReal
