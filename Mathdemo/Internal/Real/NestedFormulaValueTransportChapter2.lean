import Mathdemo.Internal.Real.BasicL1ValueAtTransportChapter2

set_option linter.style.longLine false

/-!
# G138: nested formula value transport for Chapter 2 Proposition 2.4

G137 closed the reusable operation-level `valueAt` transport lemmas.  This file
uses them to build the nested value transport for the actual characteristic
formulas:

* `min2(r,s) = 1/2 * ((r+s) - |r-s|)`;
* `or2(r,s) = (r+s) - min2(r,s)`.

Absolute-summability decomposition remains explicit data.  No quotient
representative is selected after the fact, and no choice-selection principle is
introduced.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqChapter2
namespace CharacteristicFormulaValueTransport

open CharacteristicFormula
open CharacteristicTruthTable
open CharacteristicValueTransport
open BishopRegularSeqL1ValueTransport

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}















end CharacteristicFormulaValueTransport
end BishopRegularSeqChapter2





end BishopCReal
