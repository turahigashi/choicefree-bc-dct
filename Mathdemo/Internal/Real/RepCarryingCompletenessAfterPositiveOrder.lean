import Mathdemo.Internal.Real.LocalizingOrderDataExtractionPositiveInverse

/-!
# Rep-carrying completeness after positive order-data localization

`LocalizingOrderDataExtractionPositiveInverse` localized the remaining `ltQuotData` extraction used by the
positive inverse to the shape `ltQuot zeroQuot x -> ltQuotData zeroQuot x`.
This file propagates that cleanup through the representation-carrying
completeness layer from `RepresentativeCarryingCompletenessRepFreeDecidable`.

The result is still not the opaque `COFOC.complete` theorem.  As before, the
complete branch is honest only for quotient Cauchy sequences whose terms come
with representatives.  The improvement here is that this whole
representation-carrying bridge now uses only positive-branch order-data
extraction, not a general extractor for arbitrary strict inequalities.
-/

namespace BishopCReal

open BishopC
open BishopCRat












end BishopCReal

set_option linter.style.longLine false

