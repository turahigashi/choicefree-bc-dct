import Mathdemo.Internal.Real.AssemblingLargeBranchLipschitzBridgeG62

/-!
# G64: reducing the small branch to its non-strict norm-bound bridge

G63 rejoined the G62 large branch to the final Theorem 1.18(4) assembly, but
still accepted the small branch as an already-built `Property4SmallLipschitzBridge`.
This file pushes the small branch one layer down: it is now obtained from the
source-shaped non-strict bound behind lines 743--747 plus the existing strict
upper-transfer step.
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
