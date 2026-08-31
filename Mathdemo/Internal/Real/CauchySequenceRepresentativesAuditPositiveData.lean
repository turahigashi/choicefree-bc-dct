import Mathdemo.Internal.Real.COFOCAssemblyAfterPositiveOrderData

/-!
# Cauchy-sequence representatives audit for the positive-data branch

`COFOCAssemblyAfterPositiveOrderData` assembled the localized positive-data decidable branch into a
`COFOC` once Cauchy-sequence representatives are supplied.  `CauchySequenceRepresentativesImplyGlobalRepresentatives`
already proved the general audit: because constant quotient-valued sequences
are Cauchy in any `COFO`, representatives for all Cauchy sequences recover a
global representative selector.

This file specializes that audit to the positive-data branch, so the remaining
representative frontier is stated without ambiguity for the latest branch.
-/

namespace BishopCReal

open BishopC
open BishopCRat





end BishopCReal

set_option linter.style.longLine false

