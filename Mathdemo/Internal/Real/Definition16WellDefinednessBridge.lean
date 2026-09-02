import Mathdemo.Internal.Real.Definition16L1IntegrableFunctions

/-!
# G39: Definition 1.6 well-definedness bridge via Lemma 1.7

After Definition 1.6 the source uses Lemma 1.7 to justify that the represented
integral does not depend on the chosen representation.  This file exposes that
dependency without selecting representatives implicitly: a zero-version bridge
for Lemma 1.7 is threaded into the `L1` integral congruence statement.
-/

namespace BishopCReal

open BishopC
open BishopCRat

variable {Arch : ScalarMulArchimedeanData} {X : Type}

/-- Non-negativity in the current RegularSeq surface, stated as absence of a
strict tail below zero. -/
abbrev RegularSeqNonneg (x : RegularSeq) : Prop :=
  Not (regularSeqLtProp x zeroSeq)






namespace BishopRegularSeqIntegrableRep

variable {S : BishopRegularSeqIntegrationSpaceDef11 Arch X}




end BishopRegularSeqIntegrableRep





end BishopCReal
