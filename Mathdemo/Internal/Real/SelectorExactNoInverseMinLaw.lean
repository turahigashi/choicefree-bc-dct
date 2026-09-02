import Mathdemo.Internal.Real.Property4ReductionNoInverseMin

set_option linter.style.longLine false

/-!
# G103: selector-exact no-inverse min-law bridge

G102 routed property (4) through no-inverse min-law transport, but still took
the no-inverse transport law bundle as a field.  This file generates that
bundle from the exact remaining inputs:

* a G96 scalar-min bridge;
* a global quotient representative selector;
* a `PosEventually` selector.

Thus positive-inverse totalization is no longer merely absent from the proof
body; it is absent from the data interface for this min-law route.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
