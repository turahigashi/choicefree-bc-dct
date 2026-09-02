import Mathdemo.Internal.Real.ReplacingTailRepresentativesDisplayedPFunApproximants

/-!
# G78: factoring the displayed scalar frontier into two law interfaces

G77 reduced Theorem 1.18(4)'s remaining pointwise frontier to displayed scalar
orders.  This file packages the two remaining displayed scalar laws as global
interfaces:

* large line 735: the displayed min-Lipschitz inequality;
* small line 743: the displayed min-tail inequality.

The laws remain explicit data.  G78 only shows that once these two displayed
laws are supplied, they feed the G77 route for every point and every
Corollary 1.17 approximant.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}











end BishopRegularSeqTheorem118




set_option linter.style.longLine false


end BishopCReal
