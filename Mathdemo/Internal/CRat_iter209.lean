import Mathdemo.Internal.CRat_iter208

/-!
Public artifact compatibility node.

The original development node recorded a selector-based quotient-extraction audit.
That audit is not part of the public choice-free DCT closure and is intentionally
omitted from this artifact copy.  Downstream public theorem declarations do not
use any declaration from that audit node.
-/

namespace BishopCReal

/-- Compatibility type for later historical bookkeeping nodes.

The development version of this node contained a non-public extraction audit.
The public artifact keeps only this inert type name because a later progress
meter records that such an adapter was documented, without using its contents.
-/
structure CRealQuotClassicalExtractionAudit : Type 1 where
  omitted_from_public_artifact : Prop

end BishopCReal
