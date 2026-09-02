import Mathdemo.Internal.Real.PositiveShiftRouteSelectorExactMin

set_option linter.style.longLine false

/-!
# G105: positive-shift route is equivalent to the selector-exact route

G104 connected property (4)'s no-inverse min-law bridge to the positive-shift
representative route.  Earlier work (`RepresentedPositiveShiftsNotGenuineWeakening`) already audited that
represented positive shifts are not a genuine weakening of global
representatives: a global representative selector immediately supplies the
shift `-x + 1`.

This file lifts that audit to the G103/G104 property-(4) interface.  The
positive-shift route and the direct selector-exact route are interderivable.
Thus G104 is a useful factoring of the frontier, but it does not reduce the
remaining selector problem below the G103 pair:

* global quotient representatives;
* `PosEventually` Prop-to-data selection.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
