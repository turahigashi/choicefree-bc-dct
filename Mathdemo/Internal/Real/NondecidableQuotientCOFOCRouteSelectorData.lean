import Mathdemo.Internal.Real.DataValuedQuotientCOFOrderLayer

/-!
# Nondecidable quotient COFOC route from selector data and inverse totalization

`DataValuedQuotientCOFOrderLayer` separated the data-valued order layer from the live Prop-valued
`COF` interface.  Together with the `PosEventuallyWitnessSelectorFrontier` `PosEventually` selector,
this gives the missing `ltQuot -> ltQuotData` bridge without asking for a
global strict-order decision procedure.

This file threads that bridge through the already-closed positive-inverse and
completeness machinery.  The remaining constructive inputs are now explicit:

* a global representative selector for quotient elements;
* a selector for the witnesses hidden in `PosEventually`;
* a totalization of the data-indexed positive inverse.

No `CRealQuotLTDecidable` hypothesis appears in the assembled `COFO`/`COFOC`
route below.  Decidability remains only as one optional way to build the
inverse totalization datum from `SplittingPositiveInverseDataTotalInverse`.
-/

namespace BishopCReal

open BishopC
open BishopCRat



















end BishopCReal

set_option linter.style.longLine false

