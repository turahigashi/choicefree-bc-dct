import Mathdemo.Internal.CRat_iter334
import Mathdemo.Internal.CRat_iter425

/-!
Public artifact compatibility node.

The original development node contained an optional series-valued PFun shadow
that selected a witness from a `Nonempty` domain field.  It is not used by the
public DCT theorem aliases, so the public artifact keeps only the transitive
imports needed by later stable nodes.
-/

namespace BishopC
end BishopC

namespace BishopCReal
end BishopCReal
