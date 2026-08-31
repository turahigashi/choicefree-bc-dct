import Mathdemo.Internal.Real.COFOCAssemblyRepresentedPositiveShifts

/-!
# Represented positive shifts are not a genuine weakening

`PositiveShiftsRecoverGlobalRepresentatives` reduced global representatives to positive `ltQuotData` plus
represented positive shifts.  This file audits the other direction: a global
representative selector immediately supplies represented positive shifts by
using the algebraic shift `-x + 1`.

Thus, once positive `ltQuotData` is assumed, represented positive shifts and
global representatives are interderivable.  The shift route is still a useful
localization of where the representative problem re-enters, but it is not an
independent weakening of the quotient-representative frontier.
-/

namespace BishopCReal

open BishopC
open BishopCRat








end BishopCReal

set_option linter.style.longLine false

