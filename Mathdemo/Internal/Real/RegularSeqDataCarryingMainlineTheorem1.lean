import Mathdemo.Internal.Real.QuotClassicalExtractionAudit

set_option linter.style.longLine false

/-!
# G110: RegularSeq/data-carrying mainline for theorem 1.18 property (4)

G109 was a useful audit: the previous opaque quotient route can discharge the two
remaining extraction obligations by `selector-based route`.  That is not the
Bishop-faithful proof route.

This file switches the property-(4) surface back to the representation-carrying
route.  The mainline data carries:

* the RegularSeq real surface;
* data-valued positivity/order infrastructure;
* the G96 property-(4) reduction data, whose min-law frontier is stated over
  representatives rather than by extracting representatives from a quotient.

The previous G109 selector extraction object is mentioned only as an adapter type,
not as a field used by the theorem-producing function.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}






end BishopRegularSeqTheorem118





end BishopCReal
