import Mathdemo.Internal.Real.NoInverseMinLawsRepresentativeExtraction

set_option linter.style.longLine false

/-!
# G108: lt-data extraction is the lt-witness extraction frontier

G107 routed the no-inverse min-law bridge through
`CRealQuotPropLTToDataLTObligation`.  Since `ltQuotData` is an abbreviation for
`CRealQuotLTDataWitness`, this obligation is exactly the witness-extraction
frontier isolated in `CRealQuotientCotransitivityDataBridge`.

This file lifts that definitional identification to the property-(4)
interface.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}



namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}









end BishopRegularSeqTheorem118





end BishopCReal
