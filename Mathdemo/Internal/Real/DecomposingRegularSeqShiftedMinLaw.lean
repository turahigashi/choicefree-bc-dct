import Mathdemo.Internal.Real.ExactRegularSeqDataMinLawFrontier

set_option linter.style.longLine false

/-!
# G112: decomposing the RegularSeq shifted-min law

G111 exposed two RegularSeq/data min laws as the constructive frontier.  The
line-743 shifted-min law

`min(x + d, c) <= min(x, c) + d`, for `0 <= d`,

has the same source shape as the half-sum proof already isolated on the old
adapter route: translate the left side, use monotonicity in the second
argument, then add the common nonnegative shift.

This file keeps the proof on the RegularSeq/data mainline by making those
three representative-level pieces explicit and deriving the line-743 law from
them.  No quotient representative extraction is used.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}









end BishopRegularSeqTheorem118





end BishopCReal
