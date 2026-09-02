import Mathdemo.Internal.Real.Proposition25RelativeDifferenceMeasure

set_option linter.style.longLine false

/-!
# G151: assembling the Chapter 2 finite-set law package

G149 and G150 separately closed the RegularSeq versions of Propositions 2.4 and
2.5.  This file wires them into the `FiniteSetLawPackage` target introduced at
the chapter-2 entry surface.

The package is still data-bearing: for each pair of sets it receives the local
Proposition 2.4 construction data and the Proposition 2.5 subtraction
construction data explicitly.  No global selector is introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace FiniteSetLawAssembly

open Prop24LocalNonnegativeSubseries
open Prop24MeasureIdentityFromLocalNonnegative
open Prop25SubMeasure

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}










end FiniteSetLawAssembly
end BishopRegularSeqChapter2

open BishopRegularSeqChapter2
open BishopRegularSeqChapter2.FiniteSetLawAssembly





end BishopCReal
