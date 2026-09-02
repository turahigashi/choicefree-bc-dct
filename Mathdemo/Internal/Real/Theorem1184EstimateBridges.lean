import Mathdemo.Internal.Real.Theorem118Property4Estimate

/-!
# G56: Theorem 1.18(4) estimate bridges from order bounds

G55 separated the two displayed estimates in Theorem 1.18(4).  This file
refines the remaining target once more.  The source inequalities have the
shape

* a truncation error is bounded above by the norm error;
* the norm error is below the selected epsilon;
* therefore the truncation error is below the selected epsilon.

For the small truncation branch, the old-space small truncation is first added
to both sides.  The new package records exactly these two order-bound inputs
and the strict-upper-bound transfer needed to assemble the G55 bridges.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Generic order step used in the source estimates: a non-strict upper bound
followed by a strict upper bound yields the required strict upper bound. -/
structure RegularSeqStrictUpperTransfer : Type 1 where
  from_le_lt :
    forall {x y z : RegularSeq},
      RegularSeqLe x y -> regularSeqLtData y z -> regularSeqLtData x z
  source_order_step_for_epsilon_estimates : Prop

namespace BishopRegularSeqTheorem118

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}








end BishopRegularSeqTheorem118





end BishopCReal
